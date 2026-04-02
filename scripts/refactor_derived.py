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
DEFAULT_CONSECUTIVE_NOOP_LIMIT = 2
DEFAULT_MAX_WALL_CLOCK_SEC = 900


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


def extract_theorem_entries_from_code(derived_file: Path, code: str) -> list[dict[str, str]]:
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".lean",
        prefix="Derived.refactor.entries.",
        dir=str(derived_file.parent),
        delete=False,
    ) as handle:
        temp_path = Path(handle.name)
        handle.write(code + "\n")

    try:
        return build_derived_entries_from_file(temp_path)
    finally:
        temp_path.unlink(missing_ok=True)


def validate_refactor_output(payload: dict[str, Any]) -> tuple[str, str, str, list[str], list[str]]:
    required_keys = {"result", "refactored_code", "summary", "change_notes", "touched_theorems"}
    if set(payload.keys()) != required_keys:
        raise ValueError(
            "refactor output must contain exactly: result, refactored_code, summary, change_notes, touched_theorems"
        )

    result = payload.get("result")
    if result not in {"ok", "noop", "stuck"}:
        raise ValueError("refactor result must be one of: ok, noop, stuck")

    refactored_code = payload.get("refactored_code")
    summary = payload.get("summary")
    change_notes = payload.get("change_notes")
    touched_theorems = payload.get("touched_theorems")
    if (
        not isinstance(refactored_code, str)
        or not isinstance(summary, str)
        or not isinstance(change_notes, list)
        or not isinstance(touched_theorems, list)
    ):
        raise ValueError("refactor output fields have invalid types")
    if any(not isinstance(item, str) for item in change_notes):
        raise ValueError("change_notes must contain only strings")
    if any(not isinstance(item, str) for item in touched_theorems):
        raise ValueError("touched_theorems must contain only strings")

    cleaned_code = refactored_code.strip()
    if result == "stuck":
        if cleaned_code:
            raise ValueError("refactored_code must be empty when result=stuck")
    else:
        if not cleaned_code:
            raise ValueError("refactored_code must be non-empty when result is ok or noop")
        if "namespace AutomatedTheoryConstruction" not in cleaned_code:
            raise ValueError("refactored_code must contain namespace AutomatedTheoryConstruction")
        if "end AutomatedTheoryConstruction" not in cleaned_code:
            raise ValueError("refactored_code must end the AutomatedTheoryConstruction namespace")

    cleaned_touched = [item.strip() for item in touched_theorems if item.strip()]
    return (
        result,
        cleaned_code,
        summary.strip(),
        [item.strip() for item in change_notes if item.strip()],
        cleaned_touched,
    )


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


def select_focus_theorem_names(
    *,
    theorem_inventory: list[dict[str, str]],
    duplicate_groups: list[dict[str, Any]],
    supporting_theorem_frequency: list[dict[str, Any]],
    target_theorem_name: str | None,
    max_items: int = 6,
) -> list[str]:
    theorem_names = [str(entry.get("theorem_name", "")).strip() for entry in theorem_inventory]
    theorem_names = [name for name in theorem_names if name]
    name_set = set(theorem_names)
    selected: list[str] = []

    def add(name: str) -> None:
        cleaned = name.strip()
        if not cleaned or cleaned not in name_set or cleaned in selected or len(selected) >= max_items:
            return
        selected.append(cleaned)

    target = (target_theorem_name or "").strip()
    if target:
        add(target)
        try:
            target_idx = theorem_names.index(target)
        except ValueError:
            target_idx = -1
        if target_idx >= 0:
            if target_idx > 0:
                add(theorem_names[target_idx - 1])
            if target_idx + 1 < len(theorem_names):
                add(theorem_names[target_idx + 1])
    elif theorem_names:
        add(theorem_names[-1])
        if len(theorem_names) >= 2:
            add(theorem_names[-2])

    for group in duplicate_groups:
        names = [str(item).strip() for item in group.get("theorem_names", []) if str(item).strip()]
        if target and target not in names:
            continue
        for name in names:
            add(name)
        if selected:
            break

    for item in supporting_theorem_frequency:
        add(str(item.get("theorem_name", "")))
        if len(selected) >= max_items:
            break

    return selected


def build_payload(
    *,
    derived_file: Path,
    theory_file: Path,
    derived_code: str,
    theory_context: str,
    theorem_inventory: list[dict[str, str]],
    duplicate_groups: list[dict[str, Any]],
    focus_theorem_names: list[str],
    sweep_round: int,
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
        "focus_theorem_names": focus_theorem_names,
        "refactor_goals": {
            "prefer_existing_theorem_reuse": True,
            "allow_local_reordering_only": True,
            "allow_short_aliases_for_exact_duplicates": True,
            "preserve_theorem_names": True,
            "preserve_theorem_statements": True,
            "forbid_deleting_theorems": True,
            "forbid_global_reorganization": True,
        },
        "repair_strategy": {
            "incremental_repair": True,
            "preserve_working_regions": True,
            "prefer_small_targeted_edits_per_round": True,
            "rerun_lean_after_each_candidate": True,
            "noop_is_allowed": True,
        },
        "sweep_round": sweep_round,
        "repair_round": repair_round,
        "previous_refactored_code": previous_refactored_code,
        "current_candidate_code": previous_refactored_code,
        "lean_diagnostics": "\n".join(lean_diagnostics.splitlines()[:120]),
        "last_error_excerpt": last_error_excerpt,
        "refactor_history_tail": refactor_history_tail[-6:],
        "theorem_reuse_memory": theorem_reuse_memory[-12:],
        "supporting_theorem_frequency": supporting_theorem_frequency[:20],
    }


def persist_outputs(
    *,
    candidate_code: str,
    original_code: str,
    derived_file: Path,
    output_file: Path | None,
    apply_in_place: bool,
    backup_file: Path | None,
) -> tuple[str | None, str | None]:
    written_output: str | None = None
    backup_output: str | None = None

    if backup_file is not None and apply_in_place and candidate_code.strip() != original_code.strip():
        backup_file.write_text(original_code, encoding="utf-8")
        backup_output = str(backup_file)

    if output_file is not None:
        output_file.parent.mkdir(parents=True, exist_ok=True)
        output_file.write_text(candidate_code + "\n", encoding="utf-8")
        written_output = str(output_file)

    if apply_in_place and candidate_code.strip() != original_code.strip():
        derived_file.write_text(candidate_code + "\n", encoding="utf-8")
        written_output = str(derived_file)

    return written_output, backup_output


def run_refactor_derived(
    *,
    derived_file: Path,
    theory_file: Path,
    prompt_file: Path,
    theorem_reuse_memory_file: Path,
    output_file: Path | None,
    apply_in_place: bool,
    backup_file: Path | None,
    verify_timeout_sec: int | None,
    worker_settings: WorkerSettings | None = None,
    worker_command: str | None = None,
    worker_timeout: int | None = None,
    target_theorem_name: str | None = None,
    consecutive_noop_limit: int = 2,
    max_wall_clock_sec: int | None = 300,
) -> dict[str, Any]:
    prompt_text = load_text(prompt_file)
    original_code = load_text(derived_file)
    _, theory_context = load_theory_context(theory_file)
    theorem_reuse_memory = load_theorem_reuse_memory(theorem_reuse_memory_file)
    supporting_theorem_frequency = summarize_supporting_theorem_frequency(theorem_reuse_memory)

    if worker_settings is None:
        base_worker_settings = load_worker_settings(
            command_override=worker_command,
            timeout_override=worker_timeout,
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
            timeout_override=worker_timeout,
        )

    current_code = original_code
    current_inventory = build_derived_entries_from_file(derived_file)
    previous_refactored_code = ""
    lean_diagnostics = ""
    last_error_excerpt = ""
    last_worker_meta: dict[str, Any] = {}
    last_summary = ""
    last_change_notes: list[str] = []
    last_touched_theorems: list[str] = []
    refactor_history: list[dict[str, Any]] = []
    accepted_rounds = 0
    total_rounds = 0
    consecutive_noops = 0
    changed = False
    stop_reason = "no_candidates"
    deadline = None if max_wall_clock_sec in (None, 0) else time.monotonic() + max_wall_clock_sec

    debug_log(
        "Starting derived refactor: "
        f"derived={derived_file} prompt={prompt_file} output={output_file or derived_file} "
        f"target={target_theorem_name or 'auto'} "
        f"worker_timeout={'none' if worker_settings.timeout_sec is None else worker_settings.timeout_sec} "
        f"verify_timeout={'none' if verify_timeout_sec is None else verify_timeout_sec}"
    )

    while True:
        if deadline is not None and time.monotonic() >= deadline:
            stop_reason = "max_wall_clock_reached"
            break
        if consecutive_noops >= max(1, consecutive_noop_limit):
            stop_reason = "consecutive_noop_limit_reached"
            break

        duplicate_groups = build_exact_duplicate_statement_groups(current_inventory)
        focus_theorem_names = select_focus_theorem_names(
            theorem_inventory=current_inventory,
            duplicate_groups=duplicate_groups,
            supporting_theorem_frequency=supporting_theorem_frequency,
            target_theorem_name=target_theorem_name,
        )
        if not current_inventory or not focus_theorem_names:
            stop_reason = "no_candidates"
            break

        total_rounds += 1
        repair_round = 0 if not lean_diagnostics else total_rounds - accepted_rounds - 1
        debug_log(
            f"Refactor round {total_rounds}: focus={focus_theorem_names} "
            f"accepted={accepted_rounds} consecutive_noops={consecutive_noops}"
        )
        payload = build_payload(
            derived_file=derived_file,
            theory_file=theory_file,
            derived_code=current_code,
            theory_context=theory_context,
            theorem_inventory=current_inventory,
            duplicate_groups=duplicate_groups,
            focus_theorem_names=focus_theorem_names,
            sweep_round=accepted_rounds,
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
                metadata={
                    "focus_theorem_names": focus_theorem_names,
                    "target_theorem_name": target_theorem_name or "",
                    "round": total_rounds,
                },
            )
        except Exception as exc:
            debug_log(f"Refactor round {total_rounds}: worker failed: {exc}")
            return {
                "status": "worker_error",
                "error": str(exc),
                "accepted_rounds": accepted_rounds,
                "total_rounds": total_rounds,
                "stop_reason": "worker_error",
                "verify_success": False,
                "output_file": str(output_file) if output_file is not None else None,
            }

        last_worker_meta = worker_meta
        result, candidate_code, summary, change_notes, touched_theorems = validate_refactor_output(raw_result)
        last_summary = summary
        last_change_notes = change_notes
        last_touched_theorems = touched_theorems or focus_theorem_names

        if result == "stuck":
            debug_log(f"Refactor round {total_rounds}: worker returned stuck")
            stop_reason = "worker_stuck"
            break

        if result == "noop" or candidate_code.strip() == current_code.strip():
            debug_log(f"Refactor round {total_rounds}: noop")
            consecutive_noops += 1
            previous_refactored_code = candidate_code
            lean_diagnostics = ""
            last_error_excerpt = ""
            refactor_history.append(
                {
                    "round": total_rounds,
                    "result": "noop",
                    "summary": summary,
                    "touched_theorems": last_touched_theorems,
                }
            )
            continue

        debug_log(f"Refactor round {total_rounds}: verifying Lean candidate")
        verify_result = verify_refactored_code(
            derived_file=derived_file,
            code=candidate_code,
            timeout_sec=verify_timeout_sec,
        )
        verify_success = bool(verify_result.get("success", False))
        lean_diagnostics = (str(verify_result.get("stderr", "")) + "\n" + str(verify_result.get("stdout", ""))).strip()
        last_error_excerpt = single_line_excerpt(lean_diagnostics.splitlines()[0] if lean_diagnostics else "")
        if not verify_success:
            debug_log(
                f"Refactor round {total_rounds}: candidate rejected"
                + (f" last_error={last_error_excerpt}" if last_error_excerpt else "")
            )
            previous_refactored_code = candidate_code
            refactor_history.append(
                {
                    "round": total_rounds,
                    "result": "verify_failed",
                    "summary": summary,
                    "last_error_excerpt": last_error_excerpt,
                    "touched_theorems": last_touched_theorems,
                }
            )
            continue

        current_code = candidate_code
        current_inventory = extract_theorem_entries_from_code(derived_file, current_code)
        previous_refactored_code = candidate_code
        lean_diagnostics = ""
        last_error_excerpt = ""
        accepted_rounds += 1
        changed = True
        consecutive_noops = 0
        refactor_history.append(
            {
                "round": total_rounds,
                "result": "accepted",
                "summary": summary,
                "change_notes": change_notes,
                "touched_theorems": last_touched_theorems,
            }
        )
        debug_log(
            f"Refactor round {total_rounds}: accepted touched={last_touched_theorems} "
            f"change_notes={change_notes}"
        )

    output_to_write = current_code.strip()
    if output_to_write:
        written_output, backup_output = persist_outputs(
            candidate_code=output_to_write,
            original_code=original_code,
            derived_file=derived_file,
            output_file=output_file,
            apply_in_place=apply_in_place,
            backup_file=backup_file,
        )
    else:
        written_output = None
        backup_output = None

    status = "ok" if changed else "noop"
    return {
        "status": status,
        "accepted_rounds": accepted_rounds,
        "total_rounds": total_rounds,
        "stop_reason": stop_reason,
        "summary": last_summary,
        "change_notes": last_change_notes,
        "touched_theorems": last_touched_theorems,
        "verify_success": True,
        "output_file": written_output,
        "backup_file": backup_output,
        "duplicate_statement_group_count": len(build_exact_duplicate_statement_groups(current_inventory)),
        "refactor_output_theorem_count": len(current_inventory),
        "worker_json_parse_attempts": int(last_worker_meta.get("json_parse_attempts", 0) or 0),
        "worker_raw_parse_fallback_used": bool(last_worker_meta.get("raw_parse_fallback_used", False)),
        "client_json_parse_attempts": int(last_worker_meta.get("client_json_parse_attempts", 0) or 0),
        "client_raw_parse_fallback_used": bool(last_worker_meta.get("client_raw_parse_fallback_used", False)),
    }


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
    parser.add_argument("--target-theorem-name")
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

    report = run_refactor_derived(
        derived_file=derived_file,
        theory_file=theory_file,
        prompt_file=prompt_file,
        theorem_reuse_memory_file=theorem_reuse_memory_file,
        output_file=output_file,
        apply_in_place=args.apply,
        backup_file=backup_file,
        verify_timeout_sec=args.verify_timeout,
        worker_command=args.worker_command,
        worker_timeout=args.worker_timeout,
        target_theorem_name=args.target_theorem_name,
        consecutive_noop_limit=DEFAULT_CONSECUTIVE_NOOP_LIMIT,
        max_wall_clock_sec=DEFAULT_MAX_WALL_CLOCK_SEC,
    )
    print(json.dumps(report, ensure_ascii=False))
    if report.get("status") == "worker_error":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
