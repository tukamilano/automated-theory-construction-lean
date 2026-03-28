from __future__ import annotations

import argparse
import json
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

from append_derived import build_derived_entries_from_file
from common import load_theory_context
from theorem_reuse_memory import (
    load_theorem_reuse_memory,
    summarize_supporting_theorem_frequency,
)
from worker_client import WorkerSettings, invoke_worker_json, load_task_worker_settings, load_worker_settings

DEFAULT_PREVIEW_OUTPUT = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")


def debug_log(message: str) -> None:
    timestamp = time.strftime("%H:%M:%S")
    print(f"[{timestamp}] {message}", file=sys.stderr, flush=True)


def load_text(path: Path) -> str:
    if not path.exists():
        raise ValueError(f"File not found: {path}")
    return path.read_text(encoding="utf-8")


def single_line_excerpt(text: str, limit: int = 240) -> str:
    normalized = " ".join(text.strip().split())
    if not normalized:
        return ""
    if len(normalized) <= limit:
        return normalized
    return normalized[: limit - 3] + "..."


def normalize_statement_text(statement: str) -> str:
    return " ".join(statement.split())


def build_exact_duplicate_statement_groups(entries: list[dict[str, str]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[str]] = {}
    for entry in entries:
        theorem_name = str(entry.get("theorem_name", "")).strip()
        statement = normalize_statement_text(str(entry.get("statement", "")))
        if not theorem_name or not statement:
            continue
        grouped.setdefault(statement, []).append(theorem_name)

    duplicates: list[dict[str, Any]] = []
    for statement, theorem_names in grouped.items():
        if len(theorem_names) < 2:
            continue
        duplicates.append(
            {
                "statement": statement,
                "theorem_names": theorem_names,
            }
        )
    duplicates.sort(key=lambda item: (len(item["theorem_names"]), item["statement"]), reverse=True)
    return duplicates


def validate_refactor_output(payload: dict[str, Any]) -> tuple[str, str, str, list[str]]:
    required_keys = {"result", "refactored_code", "summary", "change_notes"}
    if set(payload.keys()) != required_keys:
        raise ValueError("refactor output must contain exactly: result, refactored_code, summary, change_notes")

    result = payload.get("result")
    if result not in {"ok", "stuck"}:
        raise ValueError("refactor result must be one of: ok, stuck")

    refactored_code = payload.get("refactored_code")
    summary = payload.get("summary")
    change_notes = payload.get("change_notes")
    if not isinstance(refactored_code, str) or not isinstance(summary, str) or not isinstance(change_notes, list):
        raise ValueError("refactored_code, summary, and change_notes must have types str, str, list[str]")
    if any(not isinstance(item, str) for item in change_notes):
        raise ValueError("change_notes must contain only strings")

    cleaned_code = refactored_code.strip()
    if result == "ok":
        if not cleaned_code:
            raise ValueError("refactored_code must be non-empty when result=ok")
        if "namespace AutomatedTheoryConstruction" not in cleaned_code:
            raise ValueError("refactored_code must contain namespace AutomatedTheoryConstruction")
        if "end AutomatedTheoryConstruction" not in cleaned_code:
            raise ValueError("refactored_code must end the AutomatedTheoryConstruction namespace")
    else:
        if cleaned_code:
            raise ValueError("refactored_code must be empty when result=stuck")

    return result, cleaned_code, summary.strip(), [item.strip() for item in change_notes if item.strip()]


def verify_lean_file(file_path: Path, timeout_sec: int | None) -> dict[str, Any]:
    import subprocess

    cmd = ["lake", "env", "lean", str(file_path)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec, check=False)
    except subprocess.TimeoutExpired as exc:
        stderr_text = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
        stdout_text = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        timeout_label = f"{timeout_sec}s" if timeout_sec is not None else "without a limit"
        return {
            "success": False,
            "stderr": f"Lean verification timed out after {timeout_label}\n{stderr_text}".strip(),
            "stdout": stdout_text,
        }

    return {
        "success": proc.returncode == 0,
        "stderr": proc.stderr,
        "stdout": proc.stdout,
    }


def verify_refactored_code(derived_file: Path, code: str, timeout_sec: int | None) -> dict[str, Any]:
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".lean",
        prefix="Derived.refactor.",
        dir=str(derived_file.parent),
        delete=False,
    ) as handle:
        temp_path = Path(handle.name)
        handle.write(code + "\n")

    try:
        result = verify_lean_file(temp_path, timeout_sec=timeout_sec)
        result["checked_file"] = str(temp_path)
        return result
    finally:
        temp_path.unlink(missing_ok=True)


def build_payload(
    *,
    derived_file: Path,
    theory_file: Path,
    derived_code: str,
    theory_context: str,
    theorem_inventory: list[dict[str, str]],
    duplicate_groups: list[dict[str, Any]],
    repair_round: int,
    previous_refactored_code: str,
    lean_diagnostics: str,
    last_error_excerpt: str,
    refactor_history_tail: list[dict[str, Any]],
    theorem_reuse_memory: list[dict[str, Any]],
    supporting_theorem_frequency: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "derived_file": str(derived_file),
        "theory_file": str(theory_file),
        "derived_code": derived_code,
        "theory_context": theory_context,
        "theorem_inventory": theorem_inventory,
        "exact_duplicate_statement_groups": duplicate_groups,
        "refactor_goals": {
            "deduplicate_equivalent_theorems": True,
            "reduce_closure_lemmas": True,
            "prefer_stronger_reusable_statements": True,
            "allow_short_aliases_for_compatibility": True,
            "preserve_semantic_theorem_names_when_reasonable": True,
            "prefer_dependency_layering": True,
            "allow_reordering_declarations": True,
            "style_target": "curated_mathlib_basic_like",
            "organize_by_conceptual_families": True,
        },
        "repair_strategy": {
            "incremental_repair": True,
            "preserve_working_regions": True,
            "prefer_small_targeted_edits_per_round": True,
            "rerun_lean_after_each_candidate": True,
        },
        "repair_round": repair_round,
        "previous_refactored_code": previous_refactored_code,
        "current_candidate_code": previous_refactored_code,
        "lean_diagnostics": "\n".join(lean_diagnostics.splitlines()[:120]),
        "last_error_excerpt": last_error_excerpt,
        "refactor_history_tail": refactor_history_tail[-4:],
        "theorem_reuse_memory": theorem_reuse_memory[-12:],
        "supporting_theorem_frequency": supporting_theorem_frequency[:20],
    }


def persist_outputs(
    *,
    candidate_code: str,
    derived_file: Path,
    output_file: Path | None,
    apply_in_place: bool,
    backup_file: Path | None,
) -> tuple[str | None, str | None]:
    written_output: str | None = None
    backup_output: str | None = None

    if backup_file is not None and apply_in_place:
        backup_file.write_text(derived_file.read_text(encoding="utf-8"), encoding="utf-8")
        backup_output = str(backup_file)

    if output_file is not None:
        output_file.parent.mkdir(parents=True, exist_ok=True)
        output_file.write_text(candidate_code + "\n", encoding="utf-8")
        written_output = str(output_file)

    if apply_in_place:
        derived_file.write_text(candidate_code + "\n", encoding="utf-8")
        written_output = str(derived_file)

    return written_output, backup_output


def main() -> None:
    parser = argparse.ArgumentParser(description="LLM-guided refactoring for AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--prompt-file", default="prompts/derived_refactorer.md")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int)
    parser.add_argument("--verify-timeout", type=int)
    parser.add_argument("--output-file")
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--backup-file")
    parser.add_argument("--theorem-reuse-memory-file", default="data/theorem_reuse_memory.json")
    args = parser.parse_args()

    derived_file = Path(args.derived_file)
    theory_file = Path(args.theory_file)
    prompt_file = Path(args.prompt_file)
    theorem_reuse_memory_file = Path(args.theorem_reuse_memory_file)
    if args.output_file:
        output_file = Path(args.output_file)
    elif args.apply:
        output_file = None
    else:
        output_file = DEFAULT_PREVIEW_OUTPUT
    backup_file = Path(args.backup_file) if args.backup_file else None

    prompt_text = load_text(prompt_file)
    derived_code = load_text(derived_file)
    _, theory_context = load_theory_context(theory_file)
    theorem_inventory = build_derived_entries_from_file(derived_file)
    duplicate_groups = build_exact_duplicate_statement_groups(theorem_inventory)
    theorem_reuse_memory = load_theorem_reuse_memory(theorem_reuse_memory_file)
    supporting_theorem_frequency = summarize_supporting_theorem_frequency(theorem_reuse_memory)

    base_worker_settings = load_worker_settings(
        command_override=args.worker_command,
        timeout_override=args.worker_timeout,
        default_timeout_sec=None,
    )
    refactor_base_settings = WorkerSettings(
        command=base_worker_settings.command,
        timeout_sec=None,
        propagate_timeout=False,
    )
    worker_settings = load_task_worker_settings(
        task_name="refactor_derived",
        base_settings=refactor_base_settings,
        timeout_override=args.worker_timeout,
    )

    verify_timeout_sec = args.verify_timeout

    debug_log(
        "Starting derived refactor: "
        f"derived={derived_file} prompt={prompt_file} output={output_file or derived_file} "
        f"worker_timeout={'none' if worker_settings.timeout_sec is None else worker_settings.timeout_sec} "
        f"verify_timeout={'none' if verify_timeout_sec is None else verify_timeout_sec}"
    )
    debug_log(
        f"Loaded theorem inventory: entries={len(theorem_inventory)} duplicate_statement_groups={len(duplicate_groups)}"
    )
    debug_log(
        "Loaded theorem reuse memory: "
        f"entries={len(theorem_reuse_memory)} supporting_theorem_hints={len(supporting_theorem_frequency)}"
    )

    previous_refactored_code = ""
    lean_diagnostics = ""
    last_error_excerpt = ""
    refactor_history: list[dict[str, Any]] = []
    last_worker_meta: dict[str, Any] = {}
    summary = ""
    change_notes: list[str] = []

    repair_round = 0
    while True:
        debug_log(f"Round {repair_round}: invoking worker `{worker_settings.command}`")
        payload = build_payload(
            derived_file=derived_file,
            theory_file=theory_file,
            derived_code=derived_code,
            theory_context=theory_context,
            theorem_inventory=theorem_inventory,
            duplicate_groups=duplicate_groups,
            repair_round=repair_round,
            previous_refactored_code=previous_refactored_code,
            lean_diagnostics=lean_diagnostics,
            last_error_excerpt=last_error_excerpt,
            refactor_history_tail=refactor_history,
            theorem_reuse_memory=theorem_reuse_memory,
            supporting_theorem_frequency=supporting_theorem_frequency,
        )
        try:
            raw_result, worker_meta = invoke_worker_json(
                settings=worker_settings,
                task_type="refactor_derived",
                system_prompt=prompt_text,
                payload=payload,
                metadata={"repair_round": repair_round, "derived_file": str(derived_file)},
            )
        except Exception as exc:
            debug_log(f"Round {repair_round}: worker failed: {exc}")
            report = {
                "status": "worker_error",
                "repair_rounds_used": repair_round,
                "error": str(exc),
                "duplicate_statement_group_count": len(duplicate_groups),
                "output_file": str(output_file) if output_file is not None else None,
            }
            print(json.dumps(report, ensure_ascii=False))
            raise SystemExit(1) from exc
        last_worker_meta = worker_meta
        debug_log(
            f"Round {repair_round}: worker returned "
            f"(model={worker_meta.get('model', '') or 'unknown'}, "
            f"raw_output_chars={int(worker_meta.get('raw_output_chars', 0) or 0)})"
        )
        result, candidate_code, summary, change_notes = validate_refactor_output(raw_result)
        if result == "stuck":
            debug_log(f"Round {repair_round}: worker returned stuck")
            report = {
                "status": "stuck",
                "repair_rounds_used": repair_round,
                "summary": summary,
                "change_notes": change_notes,
                "duplicate_statement_group_count": len(duplicate_groups),
                "verify_success": False,
                "worker_json_parse_attempts": int(worker_meta.get("json_parse_attempts", 0) or 0),
                "worker_raw_parse_fallback_used": bool(worker_meta.get("raw_parse_fallback_used", False)),
                "client_json_parse_attempts": int(worker_meta.get("client_json_parse_attempts", 0) or 0),
                "client_raw_parse_fallback_used": bool(worker_meta.get("client_raw_parse_fallback_used", False)),
            }
            print(json.dumps(report, ensure_ascii=False))
            return

        debug_log(f"Round {repair_round}: verifying Lean candidate")
        verify_result = verify_refactored_code(
            derived_file=derived_file,
            code=candidate_code,
            timeout_sec=verify_timeout_sec,
        )
        verify_success = bool(verify_result.get("success", False))
        lean_diagnostics = (
            str(verify_result.get("stderr", "")) + "\n" + str(verify_result.get("stdout", ""))
        ).strip()
        last_error_excerpt = single_line_excerpt(lean_diagnostics.splitlines()[0] if lean_diagnostics else "")
        debug_log(
            f"Round {repair_round}: verify_success={verify_success}"
            + (f" last_error={last_error_excerpt}" if last_error_excerpt else "")
        )
        refactor_history.append(
            {
                "repair_round": repair_round,
                "summary": summary,
                "change_notes": change_notes,
                "verify_success": verify_success,
                "last_error_excerpt": last_error_excerpt,
            }
        )

        if verify_success:
            debug_log(f"Round {repair_round}: writing output")
            written_output, backup_output = persist_outputs(
                candidate_code=candidate_code,
                derived_file=derived_file,
                output_file=output_file,
                apply_in_place=args.apply,
                backup_file=backup_file,
            )
            report = {
                "status": "ok",
                "repair_rounds_used": repair_round,
                "summary": summary,
                "change_notes": change_notes,
                "duplicate_statement_group_count": len(duplicate_groups),
                "verify_success": True,
                "output_file": written_output,
                "backup_file": backup_output,
                "worker_json_parse_attempts": int(last_worker_meta.get("json_parse_attempts", 0) or 0),
                "worker_raw_parse_fallback_used": bool(last_worker_meta.get("raw_parse_fallback_used", False)),
                "client_json_parse_attempts": int(last_worker_meta.get("client_json_parse_attempts", 0) or 0),
                "client_raw_parse_fallback_used": bool(last_worker_meta.get("client_raw_parse_fallback_used", False)),
            }
            print(json.dumps(report, ensure_ascii=False))
            return

        previous_refactored_code = candidate_code
        repair_round += 1


if __name__ == "__main__":
    main()
