from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from append_derived import append_theorem
from common import read_jsonl, resolve_max_attempts, write_jsonl_atomic
from lean_verify import verify_scratch
from llm_client import call_chat_completion_json, load_llm_settings
from state_update import apply_state_update


SCRATCH_TEMPLATE = (
    "import AutomatedTheoryConstruction.Theory\n"
    "import AutomatedTheoryConstruction.Derived\n\n"
    "namespace AutomatedTheoryConstruction\n\n"
    "-- Temporary Lean code generated for verification is written here.\n\n"
    "end AutomatedTheoryConstruction\n"
)


def pick_next_problem(open_rows: list[dict[str, Any]], max_attempts: int) -> dict[str, Any] | None:
    eligible = [row for row in open_rows if int(row.get("n", 0)) < max_attempts]
    if not eligible:
        return None
    eligible.sort(key=lambda row: (int(row.get("n", 0)), str(row.get("id", ""))))
    return eligible[0]


def validate_picker_output(payload: dict[str, Any], open_rows: list[dict[str, Any]], max_attempts: int) -> str:
    if "error" in payload:
        if payload.get("error") == "no_selectable_problem":
            return ""
        raise ValueError("picker output contains unsupported error value")

    allowed_keys = {"selected_problem_id"}
    if set(payload.keys()) != allowed_keys:
        raise ValueError("picker output must contain exactly one key: selected_problem_id")

    selected_id = payload.get("selected_problem_id")
    if not isinstance(selected_id, str) or not selected_id:
        raise ValueError("selected_problem_id must be a non-empty string")

    eligible_ids = {
        str(row.get("id", ""))
        for row in open_rows
        if int(row.get("n", 0)) < max_attempts
    }
    if selected_id not in eligible_ids:
        raise ValueError("selected_problem_id is not eligible under current open problems and max_attempts")
    return selected_id


def validate_prover_output(payload: dict[str, Any], expected_problem_id: str) -> tuple[str, str, str, list[str]]:
    required_keys = {"problem_id", "result", "proof_text", "counterexample_text", "new_problems"}
    if set(payload.keys()) != required_keys:
        raise ValueError("prover output keys mismatch required contract")

    problem_id = payload.get("problem_id")
    if problem_id != expected_problem_id:
        raise ValueError("prover output problem_id does not match picked problem")

    result = payload.get("result")
    if result not in {"proof", "counterexample", "stuck"}:
        raise ValueError("prover result must be one of: proof, counterexample, stuck")

    proof_text = payload.get("proof_text")
    counterexample_text = payload.get("counterexample_text")
    if not isinstance(proof_text, str) or not isinstance(counterexample_text, str):
        raise ValueError("proof_text and counterexample_text must be strings")

    new_problems_value = payload.get("new_problems")
    if not isinstance(new_problems_value, list):
        raise ValueError("new_problems must be an array of strings")
    if len(new_problems_value) > 2:
        raise ValueError("new_problems must have length <= 2")
    if any((not isinstance(item, str)) for item in new_problems_value):
        raise ValueError("new_problems must contain only strings")

    new_problems = [item.strip() for item in new_problems_value if item.strip()][:2]
    return result, proof_text, counterexample_text, new_problems


def load_json_payload_from_args(inline_json: str | None, json_file: str | None) -> dict[str, Any] | None:
    if inline_json is None and json_file is None:
        return None
    if inline_json is not None and json_file is not None:
        raise ValueError("Use only one of inline JSON or JSON file input")

    raw = inline_json
    if raw is None and json_file is not None:
        raw = Path(json_file).read_text(encoding="utf-8")

    payload = json.loads(raw)
    if not isinstance(payload, dict):
        raise ValueError("JSON payload must be an object")
    return payload


def load_prompt_text(prompt_file: str) -> str:
    path = Path(prompt_file)
    if not path.exists():
        raise ValueError(f"Prompt file not found: {prompt_file}")
    return path.read_text(encoding="utf-8")


def looks_formalizable(stmt: str) -> bool:
    simple_stmt = " ".join(stmt.split())
    return (
        ("forall" in simple_stmt or "∀" in simple_stmt)
        and "=" in simple_stmt
        and "op" in simple_stmt
        and len(simple_stmt) < 2000
    )


def formalize_to_scratch(problem_id: str, stmt: str, mode: str, proof_text: str, counterexample_text: str) -> tuple[str | None, str | None]:
    if not looks_formalizable(stmt):
        return None, None

    theorem_name = f"thm_{problem_id}"
    if mode == "proof":
        body = proof_text.strip() if proof_text.strip() else "sorry"
        theorem = f"theorem {theorem_name} : {stmt} := by\n  {body}\n"
    else:
        witness = counterexample_text.strip() if counterexample_text.strip() else "by\n  sorry"
        theorem = f"theorem {theorem_name}_counterexample_placeholder : True := {witness}\n"

    scratch = (
        "import AutomatedTheoryConstruction.Theory\n"
        "import AutomatedTheoryConstruction.Derived\n\n"
        "namespace AutomatedTheoryConstruction\n\n"
        f"{theorem}\n"
        "end AutomatedTheoryConstruction\n"
    )
    return theorem_name, scratch


def parse_new_problems(raw_values: list[str]) -> list[str]:
    values: list[str] = []
    for raw in raw_values:
        text = raw.strip()
        if text:
            values.append(text)
    return values[:2]


def initialize_runtime_state(data_dir: Path, seeds_file: Path, scratch_file: Path, reset_scratch: bool) -> None:
    seed_rows = read_jsonl(seeds_file)
    if not seed_rows:
        raise ValueError(f"Seeds file is empty: {seeds_file}")

    data_dir.mkdir(parents=True, exist_ok=True)
    write_jsonl_atomic(data_dir / "open_problems.jsonl", seed_rows)
    write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
    write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])

    if reset_scratch:
        scratch_file.parent.mkdir(parents=True, exist_ok=True)
        scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Run one iteration of the minimal prototype loop.")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--config", default="config/defaults.json")
    parser.add_argument("--seeds-file", default="theories/semigroup_like_01/seeds.jsonl")
    parser.add_argument("--scratch-file", default="AutomatedTheoryConstruction/Scratch.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--reset-scratch-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--max-attempts", type=int)
    parser.add_argument("--picker-output-json")
    parser.add_argument("--picker-output-file")
    parser.add_argument("--prover-output-json")
    parser.add_argument("--prover-output-file")
    parser.add_argument("--enable-llm", action="store_true")
    parser.add_argument("--llm-base-url")
    parser.add_argument("--llm-api-key")
    parser.add_argument("--llm-model")
    parser.add_argument("--llm-timeout", type=int, default=60)
    parser.add_argument("--picker-prompt-file", default="prompts/picker.md")
    parser.add_argument("--prover-prompt-file", default="prompts/prover.md")
    parser.add_argument("--mock-result", choices=["proof", "counterexample", "stuck"], default="stuck")
    parser.add_argument("--mock-proof-text", default="")
    parser.add_argument("--mock-counterexample-text", default="")
    parser.add_argument("--mock-new-problem", action="append", default=[])
    parser.add_argument("--skip-verify", action="store_true")
    args = parser.parse_args()

    data_dir = Path(args.data_dir)
    config_path = Path(args.config)
    scratch_file = Path(args.scratch_file)

    if args.initialize_on_start:
        initialize_runtime_state(
            data_dir=data_dir,
            seeds_file=Path(args.seeds_file),
            scratch_file=scratch_file,
            reset_scratch=args.reset_scratch_on_start,
        )

    max_attempts = resolve_max_attempts(args.max_attempts, config_path)

    open_rows = read_jsonl(data_dir / "open_problems.jsonl")
    picker_payload = load_json_payload_from_args(args.picker_output_json, args.picker_output_file)

    llm_settings = None
    if args.enable_llm:
        llm_settings = load_llm_settings(
            base_url_override=args.llm_base_url,
            api_key_override=args.llm_api_key,
            model_override=args.llm_model,
            timeout_override=args.llm_timeout,
        )
        if picker_payload is None:
            picker_prompt = load_prompt_text(args.picker_prompt_file)
            picker_payload = call_chat_completion_json(
                llm_settings,
                picker_prompt,
                {
                    "open_problems": open_rows,
                    "max_attempts": max_attempts,
                },
            )

    picked: dict[str, Any] | None = None
    if picker_payload is not None:
        selected_problem_id = validate_picker_output(picker_payload, open_rows, max_attempts)
        if not selected_problem_id:
            print({"status": "no_eligible_open_problem", "max_attempts": max_attempts})
            return
        for row in open_rows:
            if str(row.get("id", "")) == selected_problem_id:
                picked = row
                break
    else:
        picked = pick_next_problem(open_rows, max_attempts)

    if picked is None:
        print({"status": "no_eligible_open_problem", "max_attempts": max_attempts})
        return

    problem_id = str(picked["id"])
    stmt = str(picked.get("stmt", ""))

    prover_payload = load_json_payload_from_args(args.prover_output_json, args.prover_output_file)
    if prover_payload is None and llm_settings is not None:
        prover_prompt = load_prompt_text(args.prover_prompt_file)
        prover_payload = call_chat_completion_json(
            llm_settings,
            prover_prompt,
            {
                "problem_id": problem_id,
                "stmt": stmt,
                "open_problems": open_rows,
                "max_attempts": max_attempts,
            },
        )

    if prover_payload is not None:
        result, proof_text, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)
    else:
        result = args.mock_result
        proof_text = args.mock_proof_text
        counterexample_text = args.mock_counterexample_text
        new_problems = parse_new_problems(args.mock_new_problem)

    formalization_rejected = False
    verify_success = False
    theorem_name = None

    if result in {"proof", "counterexample"}:
        theorem_name, scratch_code = formalize_to_scratch(
            problem_id=problem_id,
            stmt=stmt,
            mode=result,
            proof_text=proof_text,
            counterexample_text=counterexample_text,
        )
        if scratch_code is None:
            formalization_rejected = True
        else:
            scratch_file.write_text(scratch_code, encoding="utf-8")
            if args.skip_verify:
                verify_success = True
            else:
                verify_result = verify_scratch(problem_id, result, scratch_file, timeout_sec=60)
                verify_success = bool(verify_result.get("success", False))

            if verify_success and result == "proof":
                theorem_body_match = re.search(
                    r"namespace AutomatedTheoryConstruction\n\n(.*)\nend AutomatedTheoryConstruction",
                    scratch_code,
                    re.DOTALL,
                )
                if theorem_body_match:
                    append_theorem(Path(args.derived_file), theorem_body_match.group(1), theorem_name)

    report = apply_state_update(
        data_dir=data_dir,
        config_path=config_path,
        problem_id=problem_id,
        result=result,
        verify_success=verify_success,
        theorem_name=theorem_name,
        new_problems=new_problems,
        formalization_rejected=formalization_rejected,
        max_attempts_override=args.max_attempts,
    )
    report["picked_problem_id"] = problem_id
    report["result"] = result
    print(report)


if __name__ == "__main__":
    main()
