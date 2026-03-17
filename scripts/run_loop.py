from __future__ import annotations

import argparse
import json
import re
import time
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


def load_optional_text(file_path: str) -> str:
    path = Path(file_path)
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def looks_formalizable(stmt: str) -> bool:
    simple_stmt = " ".join(stmt.split())
    return (
        ("∀" in simple_stmt or "∀" in simple_stmt)
        and "=" in simple_stmt
        and "op" in simple_stmt
        and len(simple_stmt) < 2000
    )


def formalize_to_scratch(
    problem_id: str,
    stmt: str,
    mode: str,
    proof_text: str,
    counterexample_text: str,
    include_mathlib_import: bool,
) -> tuple[str | None, str | None]:
    if not looks_formalizable(stmt):
        return None, None

    theorem_name = f"thm_{problem_id}"
    if mode == "proof":
        raw_body = proof_text.strip() if proof_text.strip() else "sorry"
        body = "\n  ".join(line.rstrip() for line in raw_body.splitlines())
        theorem = f"theorem {theorem_name} : {stmt} := by\n  {body}\n"
    else:
        witness = counterexample_text.strip() if counterexample_text.strip() else "by\n  sorry"
        theorem = f"theorem {theorem_name}_counterexample_placeholder : True := {witness}\n"

    import_block = ""
    if include_mathlib_import:
        import_block = "import Mathlib\n"

    scratch = (
        import_block
        + "import AutomatedTheoryConstruction.Theory\n"
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


def analyze_lean_failure(stderr: str, stdout: str) -> dict[str, Any]:
    text = (stderr or "") + "\n" + (stdout or "")
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    top_lines = lines[:12]
    categories: list[str] = []

    if "Type mismatch" in text:
        categories.append("type_mismatch")
    if "rewrite` failed" in text or "Tactic `rewrite` failed" in text:
        categories.append("rewrite_failed")
    if "unsolved goals" in text:
        categories.append("unsolved_goals")
    if "unknown constant" in text or "unknown identifier" in text:
        categories.append("unknown_symbol")
    if "unknown tactic" in text:
        categories.append("unknown_tactic")
    if "Application type mismatch" in text:
        categories.append("application_type_mismatch")
    if not categories:
        categories.append("other")

    fingerprint = " | ".join(top_lines[:3]) if top_lines else "no_diagnostics"
    return {
        "fingerprint": fingerprint,
        "categories": categories,
        "top_lines": top_lines,
    }


def load_formalization_memory(memory_path: Path, problem_id: str) -> list[dict[str, str]]:
    if not memory_path.exists():
        return []
    try:
        payload = json.loads(memory_path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if not isinstance(payload, dict):
        return []
    rows = payload.get(problem_id, [])
    if not isinstance(rows, list):
        return []
    safe_rows: list[dict[str, str]] = []
    for item in rows:
        if not isinstance(item, dict):
            continue
        safe_rows.append(
            {
                "result": str(item.get("result", "")),
                "proof_text": str(item.get("proof_text", "")),
                "counterexample_text": str(item.get("counterexample_text", "")),
                "lean_error_excerpt": str(item.get("lean_error_excerpt", "")),
            }
        )
    return safe_rows


def save_formalization_memory(memory_path: Path, problem_id: str, history: list[dict[str, str]]) -> None:
    memory_path.parent.mkdir(parents=True, exist_ok=True)
    payload: dict[str, Any] = {}
    if memory_path.exists():
        try:
            existing = json.loads(memory_path.read_text(encoding="utf-8"))
            if isinstance(existing, dict):
                payload = existing
        except Exception:
            payload = {}
    payload[problem_id] = history[-20:]
    memory_path.write_text(json.dumps(payload, ensure_ascii=True, indent=2), encoding="utf-8")


def query_prover_with_retries(
    llm_settings: Any,
    prover_prompt: str,
    problem_id: str,
    stmt: str,
    open_rows: list[dict[str, Any]],
    max_attempts: int,
    prover_retries: int,
    theory_context: str,
) -> tuple[str, str, str, list[str], int]:
    retries = max(1, prover_retries)
    last_result = "stuck"
    last_proof_text = ""
    last_counterexample_text = ""
    last_new_problems: list[str] = []

    for attempt in range(1, retries + 1):
        payload: dict[str, Any] = {
            "problem_id": problem_id,
            "stmt": stmt,
            "theory_context": theory_context,
            "open_problems": open_rows,
            "max_attempts": max_attempts,
            "prover_attempt_index": attempt,
            "prover_attempt_budget": retries,
            "mathlib_allowed": True,
            "new_problem_generation_policy": {
                "prefer_generalization": True,
                "avoid_direct_axiom_instantiation": True,
                "avoid_variable_renaming_only": True,
                "target_novelty": "medium_or_high",
                "examples_of_boring_patterns": [
                    "x x duplicates only",
                    "single-axiom restatement",
                    "commutativity/idempotence restatement",
                ],
            },
        }
        if attempt > 1:
            payload["retry_instruction"] = (
                "Previous attempt returned stuck. Try a different angle. "
                "If you still cannot prove or refute, return at least one concrete "
                "counterexample candidate in counterexample_text and up to two useful new_problems."
            )
            payload["previous_result"] = last_result
            payload["previous_counterexample_text"] = last_counterexample_text
            payload["previous_new_problems"] = last_new_problems

        prover_payload = call_chat_completion_json(llm_settings, prover_prompt, payload)
        result, proof_text, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)

        last_result = result
        last_proof_text = proof_text
        last_counterexample_text = counterexample_text
        last_new_problems = new_problems

        if result != "stuck":
            return result, proof_text, counterexample_text, new_problems, attempt

    return last_result, last_proof_text, last_counterexample_text, last_new_problems, retries


def attempt_formalization_until_timeout(
    *,
    problem_id: str,
    stmt: str,
    result: str,
    proof_text: str,
    counterexample_text: str,
    new_problems: list[str],
    scratch_file: Path,
    skip_verify: bool,
    llm_settings: Any,
    prover_prompt: str,
    open_rows: list[dict[str, Any]],
    max_attempts: int,
    theory_context: str,
    verify_timeout_sec: int,
    formalization_retry_budget_sec: int,
    memory_path: Path,
) -> tuple[bool, bool, str | None, str, str, str, list[str], str]:
    verify_success = False
    formalization_rejected = False
    theorem_name: str | None = None
    verify_error_excerpt = ""
    include_mathlib_import = False

    if result not in {"proof", "counterexample"}:
        return verify_success, formalization_rejected, theorem_name, result, proof_text, counterexample_text, new_problems, verify_error_excerpt

    deadline = time.monotonic() + max(1, formalization_retry_budget_sec)
    persisted_history = load_formalization_memory(memory_path, problem_id)
    repair_round = 0
    repair_history: list[dict[str, str]] = list(persisted_history)

    while True:
        theorem_name, scratch_code = formalize_to_scratch(
            problem_id=problem_id,
            stmt=stmt,
            mode=result,
            proof_text=proof_text,
            counterexample_text=counterexample_text,
            include_mathlib_import=include_mathlib_import,
        )

        lean_diagnostics = ""
        if scratch_code is None:
            verify_error_excerpt = "formalization failed before Lean check"
            verify_error_analysis = {
                "fingerprint": "formalization_failed_before_lean",
                "categories": ["formalization_failed"],
                "top_lines": [verify_error_excerpt],
            }
        else:
            scratch_file.write_text(scratch_code, encoding="utf-8")
            if skip_verify:
                verify_success = True
                verify_error_analysis = {
                    "fingerprint": "verify_skipped",
                    "categories": ["verify_skipped"],
                    "top_lines": [],
                }
            else:
                verify_result = verify_scratch(problem_id, result, scratch_file, timeout_sec=verify_timeout_sec)
                verify_success = bool(verify_result.get("success", False))
                lean_diagnostics = (
                    str(verify_result.get("stderr", "")) + "\n" + str(verify_result.get("stdout", ""))
                ).strip()
                if not verify_success:
                    verify_stderr = str(verify_result.get("stderr", "")).strip()
                    verify_stdout = str(verify_result.get("stdout", "")).strip()
                    verify_error_excerpt = (verify_stderr or verify_stdout).splitlines()[0] if (verify_stderr or verify_stdout) else "Lean verification failed"
                verify_error_analysis = analyze_lean_failure(
                    str(verify_result.get("stderr", "")),
                    str(verify_result.get("stdout", "")),
                )

            if verify_success:
                return (
                    verify_success,
                    False,
                    theorem_name,
                    result,
                    proof_text,
                    counterexample_text,
                    new_problems,
                    verify_error_excerpt,
                )

        if llm_settings is None or time.monotonic() >= deadline:
            formalization_rejected = True
            save_formalization_memory(memory_path, problem_id, repair_history)
            return (
                verify_success,
                formalization_rejected,
                theorem_name,
                result,
                proof_text,
                counterexample_text,
                new_problems,
                verify_error_excerpt,
            )

        error_fingerprint = str(verify_error_analysis.get("fingerprint", "no_diagnostics"))

        repair_history.append(
            {
                "result": result,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "lean_error_excerpt": verify_error_excerpt,
                "lean_error_fingerprint": error_fingerprint,
            }
        )
        if len(repair_history) > 4:
            repair_history = repair_history[-20:]
        save_formalization_memory(memory_path, problem_id, repair_history)

        repair_round += 1
        repair_payload: dict[str, Any] = {
            "problem_id": problem_id,
            "stmt": stmt,
            "theory_context": theory_context,
            "open_problems": open_rows,
            "max_attempts": max_attempts,
            "prover_attempt_index": repair_round,
            "prover_attempt_budget": "until_formalization_timeout",
            "mathlib_allowed": True,
            "new_problem_generation_policy": {
                "prefer_generalization": True,
                "avoid_direct_axiom_instantiation": True,
                "avoid_variable_renaming_only": True,
                "target_novelty": "medium_or_high",
            },
            "retry_instruction": (
                "Previous proof/counterexample failed Lean formalization or verification. "
                "Read the Lean diagnostics carefully and return a corrected Lean-valid response. "
                "If result is proof, proof_text must be Lean tactic code only."
            ),
            "error_fingerprint": error_fingerprint,
            "error_categories": verify_error_analysis.get("categories", []),
            "previous_result": result,
            "previous_proof_text": proof_text,
            "previous_counterexample_text": counterexample_text,
            "previous_new_problems": new_problems,
            "repair_history_tail": repair_history[-8:],
            "lean_error_excerpt": verify_error_excerpt,
            "lean_error_top_lines": verify_error_analysis.get("top_lines", []),
            "lean_diagnostics": "\n".join(lean_diagnostics.splitlines()[:60]),
            "current_scratch_code": scratch_code or "",
            "mathlib_import_in_scratch": include_mathlib_import,
            "deadline_note": "Keep trying corrections until a Lean-checkable output is found.",
        }

        repaired = call_chat_completion_json(llm_settings, prover_prompt, repair_payload)
        try:
            result, proof_text, counterexample_text, new_problems = validate_prover_output(repaired, problem_id)
        except ValueError as exc:
            verify_error_excerpt = f"repair output invalid: {exc}"
            continue

        # Keep default path lightweight. Enable Mathlib import only when diagnostics suggest missing tactics/symbols.
        categories = verify_error_analysis.get("categories", [])
        if "unknown_tactic" in categories or "unknown_symbol" in categories:
            include_mathlib_import = True


def run_single_shot_mode(args: argparse.Namespace) -> None:
    if not args.single_shot_stmt:
        raise ValueError("--single-shot-stmt is required when --mode single-shot")

    problem_id = args.single_shot_problem_id
    stmt = args.single_shot_stmt
    scratch_file = Path(args.scratch_file)
    memory_path = Path(args.formalization_memory_file)
    theorem_name = None
    verify_success = False
    verify_error_excerpt = ""
    formalization_rejected = False
    prover_attempts_used = 1

    prover_payload = load_json_payload_from_args(args.prover_output_json, args.prover_output_file)
    llm_settings = None
    theory_context = load_optional_text(args.theory_file)

    if args.enable_llm:
        llm_settings = load_llm_settings(
            base_url_override=args.llm_base_url,
            api_key_override=args.llm_api_key,
            model_override=args.llm_model,
            timeout_override=args.llm_timeout,
        )

    if prover_payload is not None:
        result, proof_text, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)
    elif llm_settings is not None:
        prover_prompt = load_prompt_text(args.prover_prompt_file)
        result, proof_text, counterexample_text, new_problems, prover_attempts_used = query_prover_with_retries(
            llm_settings=llm_settings,
            prover_prompt=prover_prompt,
            problem_id=problem_id,
            stmt=stmt,
            open_rows=[],
            max_attempts=1,
            prover_retries=args.prover_retries,
            theory_context=theory_context,
        )
    else:
        result = args.mock_result
        proof_text = args.mock_proof_text
        counterexample_text = args.mock_counterexample_text
        new_problems = parse_new_problems(args.mock_new_problem)

    prover_prompt = load_prompt_text(args.prover_prompt_file) if llm_settings is not None else ""
    (
        verify_success,
        formalization_rejected,
        theorem_name,
        result,
        proof_text,
        counterexample_text,
        new_problems,
        verify_error_excerpt,
    ) = attempt_formalization_until_timeout(
        problem_id=problem_id,
        stmt=stmt,
        result=result,
        proof_text=proof_text,
        counterexample_text=counterexample_text,
        new_problems=new_problems,
        scratch_file=scratch_file,
        skip_verify=args.skip_verify,
        llm_settings=llm_settings,
        prover_prompt=prover_prompt,
        open_rows=[],
        max_attempts=1,
        theory_context=theory_context,
        verify_timeout_sec=60,
        formalization_retry_budget_sec=args.formalization_retry_budget_sec,
        memory_path=memory_path,
    )

    if verify_success and result == "proof" and args.single_shot_append_derived:
        scratch_code = scratch_file.read_text(encoding="utf-8")
        theorem_body_match = re.search(
            r"namespace AutomatedTheoryConstruction\n\n(.*)\nend AutomatedTheoryConstruction",
            scratch_code,
            re.DOTALL,
        )
        if theorem_body_match:
            append_theorem(Path(args.derived_file), theorem_body_match.group(1), theorem_name)

    report = {
        "mode": "single-shot",
        "problem_id": problem_id,
        "stmt": stmt,
        "result": result,
        "verify_success": verify_success,
        "verify_error_excerpt": verify_error_excerpt,
        "formalization_rejected": formalization_rejected,
        "theorem_name": theorem_name,
        "prover_attempts_used": prover_attempts_used,
        "prover_counterexample_text": counterexample_text,
        "prover_new_problem_suggestions": new_problems,
        "derived_appended": bool(verify_success and result == "proof" and args.single_shot_append_derived),
    }
    if llm_settings is not None:
        report["llm_base_url"] = llm_settings.base_url
        report["llm_model"] = llm_settings.model
    print(report)


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
    parser.add_argument("--mode", choices=["loop", "single-shot"], default="loop")
    parser.add_argument("--initialize-on-start", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--enable-llm", action="store_true")
    parser.add_argument("--llm-base-url")
    parser.add_argument("--llm-api-key")
    parser.add_argument("--llm-model")
    parser.add_argument("--llm-timeout", type=int, default=60)
    parser.add_argument("--single-shot-stmt")
    parser.add_argument("--skip-verify", action="store_true")
    args = parser.parse_args()

    # Fixed runtime paths and hidden compatibility defaults.
    args.data_dir = "data"
    args.config = "config/defaults.json"
    args.seeds_file = "theories/semigroup_like_01/seeds.jsonl"
    args.scratch_file = "AutomatedTheoryConstruction/Scratch.lean"
    args.derived_file = "AutomatedTheoryConstruction/Derived.lean"
    args.reset_scratch_on_start = True
    args.max_attempts = None
    args.picker_output_json = None
    args.picker_output_file = None
    args.prover_output_json = None
    args.prover_output_file = None
    args.theory_file = "AutomatedTheoryConstruction/Theory.lean"
    args.picker_prompt_file = "prompts/picker.md"
    args.prover_prompt_file = "prompts/prover.md"
    args.prover_retries = 1
    args.formalization_retry_budget_sec = 180
    args.formalization_memory_file = "data/formalization_memory.json"
    args.single_shot_problem_id = "single_000001"
    args.single_shot_append_derived = False
    args.mock_result = "stuck"
    args.mock_proof_text = ""
    args.mock_counterexample_text = ""
    args.mock_new_problem = []

    data_dir = Path(args.data_dir)
    config_path = Path(args.config)
    scratch_file = Path(args.scratch_file)
    memory_path = Path(args.formalization_memory_file)

    if args.mode == "single-shot":
        run_single_shot_mode(args)
        return

    if args.initialize_on_start:
        initialize_runtime_state(
            data_dir=data_dir,
            seeds_file=Path(args.seeds_file),
            scratch_file=scratch_file,
            reset_scratch=args.reset_scratch_on_start,
        )

    max_attempts = resolve_max_attempts(args.max_attempts, config_path)
    theory_context = load_optional_text(args.theory_file)
    open_path = data_dir / "open_problems.jsonl"

    llm_settings = None
    if args.enable_llm:
        llm_settings = load_llm_settings(
            base_url_override=args.llm_base_url,
            api_key_override=args.llm_api_key,
            model_override=args.llm_model,
            timeout_override=args.llm_timeout,
        )
    completed_iterations = 0
    while True:
        if not open_path.exists():
            print({"status": "open_problems_missing", "iterations_completed": completed_iterations})
            return

        open_rows = read_jsonl(open_path)
        if not open_rows:
            print({"status": "no_open_problems", "iterations_completed": completed_iterations})
            return

        eligible_rows = [row for row in open_rows if int(row.get("n", 0)) < max_attempts]
        if not eligible_rows:
            print({
                "status": "no_eligible_open_problem",
                "max_attempts": max_attempts,
                "iterations_completed": completed_iterations,
            })
            return

        picker_payload = load_json_payload_from_args(args.picker_output_json, args.picker_output_file)
        if llm_settings is not None and picker_payload is None:
            picker_prompt = load_prompt_text(args.picker_prompt_file)
            picker_payload = call_chat_completion_json(
                llm_settings,
                picker_prompt,
                {
                    "theory_context": theory_context,
                    "open_problems": eligible_rows,
                    "max_attempts": max_attempts,
                },
            )

        picked: dict[str, Any] | None = None
        picker_fallback_used = False
        if picker_payload is not None:
            try:
                selected_problem_id = validate_picker_output(picker_payload, open_rows, max_attempts)
            except ValueError:
                selected_problem_id = ""
                picker_fallback_used = True

            if selected_problem_id:
                for row in open_rows:
                    if str(row.get("id", "")) == selected_problem_id:
                        picked = row
                        break
            else:
                picker_fallback_used = True
                picked = pick_next_problem(open_rows, max_attempts)
        else:
            picked = pick_next_problem(open_rows, max_attempts)

        if picked is None:
            print({
                "status": "no_eligible_open_problem",
                "max_attempts": max_attempts,
                "iterations_completed": completed_iterations,
            })
            return

        problem_id = str(picked["id"])
        stmt = str(picked.get("stmt", ""))

        prover_payload = load_json_payload_from_args(args.prover_output_json, args.prover_output_file)
        prover_attempts_used = 1
        if prover_payload is not None:
            result, proof_text, counterexample_text, new_problems = validate_prover_output(prover_payload, problem_id)
        elif llm_settings is not None:
            prover_prompt = load_prompt_text(args.prover_prompt_file)
            result, proof_text, counterexample_text, new_problems, prover_attempts_used = query_prover_with_retries(
                llm_settings=llm_settings,
                prover_prompt=prover_prompt,
                problem_id=problem_id,
                stmt=stmt,
                open_rows=open_rows,
                max_attempts=max_attempts,
                prover_retries=args.prover_retries,
                theory_context=theory_context,
            )
        else:
            result = args.mock_result
            proof_text = args.mock_proof_text
            counterexample_text = args.mock_counterexample_text
            new_problems = parse_new_problems(args.mock_new_problem)

        prover_prompt_for_repair = load_prompt_text(args.prover_prompt_file) if llm_settings is not None else ""
        (
            verify_success,
            formalization_rejected,
            theorem_name,
            result,
            proof_text,
            counterexample_text,
            new_problems,
            verify_error_excerpt,
        ) = attempt_formalization_until_timeout(
            problem_id=problem_id,
            stmt=stmt,
            result=result,
            proof_text=proof_text,
            counterexample_text=counterexample_text,
            new_problems=new_problems,
            scratch_file=scratch_file,
            skip_verify=args.skip_verify,
            llm_settings=llm_settings,
            prover_prompt=prover_prompt_for_repair,
            open_rows=open_rows,
            max_attempts=max_attempts,
            theory_context=theory_context,
            verify_timeout_sec=60,
            formalization_retry_budget_sec=args.formalization_retry_budget_sec,
            memory_path=memory_path,
        )

        if verify_success and result == "proof":
            scratch_code = scratch_file.read_text(encoding="utf-8")
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
        completed_iterations += 1
        report["picked_problem_id"] = problem_id
        report["result"] = result
        report["verify_success"] = verify_success
        report["verify_error_excerpt"] = verify_error_excerpt
        report["prover_attempts_used"] = prover_attempts_used
        report["prover_counterexample_text"] = counterexample_text
        report["prover_new_problem_suggestions"] = new_problems
        report["iteration"] = completed_iterations
        report["picker_fallback_used"] = picker_fallback_used
        if llm_settings is not None:
            report["llm_base_url"] = llm_settings.base_url
            report["llm_model"] = llm_settings.model
        print(report)


if __name__ == "__main__":
    main()
