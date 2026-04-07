from __future__ import annotations

import argparse
import time
from pathlib import Path
from typing import Any

from append_derived import build_derived_entries_from_file
from common import load_theory_context
from derived_refactor_utils import build_exact_duplicate_statement_groups
from derived_refactor_utils import build_report
from derived_refactor_utils import candidate_fingerprint
from derived_refactor_utils import debug_log
from derived_refactor_utils import detect_no_progress
from derived_refactor_utils import emit_progress_event
from derived_refactor_utils import emit_progress_error
from derived_refactor_utils import emit_progress_finish
from derived_refactor_utils import emit_progress_start
from derived_refactor_utils import error_fingerprint
from derived_refactor_utils import extract_theorem_entries_from_code
from derived_refactor_utils import load_text
from derived_refactor_utils import normalize_stop_reason
from derived_refactor_utils import print_report
from derived_refactor_utils import resolve_refactor_worker_settings
from derived_refactor_utils import single_line_excerpt
from derived_refactor_utils import validate_full_file_refactor_output
from derived_refactor_utils import verify_refactored_code
from theorem_reuse_memory import (
    load_theorem_reuse_memory,
    summarize_supporting_theorem_frequency,
)
from worker_client import invoke_worker_json

DEFAULT_PREVIEW_OUTPUT = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_PROGRESS_LOG = Path("AutomatedTheoryConstruction/Derived.refactor.pass1.log.jsonl")


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
    progress_log_file: Path | None,
    worker_settings: WorkerSettings | None = None,
    worker_command: str | None = None,
    worker_timeout: int | None = None,
    target_theorem_name: str | None = None,
    max_wall_clock_sec: int | None = None,
) -> dict[str, Any]:
    prompt_text = load_text(prompt_file)
    original_code = load_text(derived_file)
    _, theory_context = load_theory_context(theory_file)
    theorem_reuse_memory = load_theorem_reuse_memory(theorem_reuse_memory_file)
    supporting_theorem_frequency = summarize_supporting_theorem_frequency(theorem_reuse_memory)

    worker_settings = resolve_refactor_worker_settings(
        worker_settings=worker_settings,
        worker_command=worker_command,
        worker_timeout=worker_timeout,
    )

    current_code = original_code
    current_inventory = build_derived_entries_from_file(derived_file)
    previous_refactored_code = ""
    lean_diagnostics = ""
    last_error_excerpt = ""
    last_summary = ""
    last_change_notes: list[str] = []
    last_touched_theorems: list[str] = []
    refactor_history: list[dict[str, Any]] = []
    accepted_rounds = 0
    total_rounds = 0
    changed = False
    raw_stop_reason = "no_candidates"
    deadline = None if max_wall_clock_sec in (None, 0) else time.monotonic() + max_wall_clock_sec

    debug_log(
        "Starting derived refactor: "
        f"derived={derived_file} prompt={prompt_file} output={output_file or derived_file} "
        f"target={target_theorem_name or 'auto'} "
        f"worker_timeout={'none' if worker_settings.timeout_sec is None else worker_settings.timeout_sec} "
        f"verify_timeout={'none' if verify_timeout_sec is None else verify_timeout_sec}"
    )
    emit_progress_start(progress_log_file, pass_name="pass_1")

    while True:
        if deadline is not None and time.monotonic() >= deadline:
            raw_stop_reason = "budget_exhausted:max_wall_clock_reached"
            break

        duplicate_groups = build_exact_duplicate_statement_groups(current_inventory)
        focus_theorem_names = select_focus_theorem_names(
            theorem_inventory=current_inventory,
            duplicate_groups=duplicate_groups,
            supporting_theorem_frequency=supporting_theorem_frequency,
            target_theorem_name=target_theorem_name,
        )
        if not focus_theorem_names:
            raw_stop_reason = "no_candidates"
            break

        total_rounds += 1
        repair_round = 0 if not lean_diagnostics else total_rounds - accepted_rounds - 1
        debug_log(
            f"Refactor round {total_rounds}: focus={focus_theorem_names} accepted={accepted_rounds}"
        )
        emit_progress_event(
            progress_log_file,
            pass_name="pass_1",
            phase="round_start",
            round=total_rounds,
            result="running",
            focus_theorem_names=focus_theorem_names,
            repair_round=repair_round,
            error_excerpt=last_error_excerpt,
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
            raw_result, _worker_meta = invoke_worker_json(
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
            emit_progress_error(
                progress_log_file,
                pass_name="pass_1",
                phase="worker_error",
                round=total_rounds,
                stop_reason="worker_error",
                focus_theorem_names=focus_theorem_names,
                error_excerpt=single_line_excerpt(str(exc)),
            )
            return build_report(
                "error",
                "worker_error",
                stop_detail=str(exc),
                input_file=derived_file,
                output_file=output_file,
                extra={
                    "accepted_rounds": accepted_rounds,
                    "total_rounds": total_rounds,
                    "verify_success": False,
                },
            )

        result, candidate_code, summary, change_notes, touched_theorems = validate_full_file_refactor_output(
            raw_result,
            label="refactor output",
        )
        last_summary = summary
        last_change_notes = change_notes
        last_touched_theorems = touched_theorems or focus_theorem_names

        if result == "stuck":
            debug_log(f"Refactor round {total_rounds}: worker returned stuck")
            emit_progress_event(
                progress_log_file,
                pass_name="pass_1",
                phase="worker_result",
                round=total_rounds,
                result="stuck",
                focus_theorem_names=last_touched_theorems,
                error_excerpt="worker returned stuck",
            )
            raw_stop_reason = "worker_stuck"
            break

        if result == "noop" or candidate_code.strip() == current_code.strip():
            debug_log(f"Refactor round {total_rounds}: noop")
            previous_refactored_code = candidate_code
            lean_diagnostics = ""
            last_error_excerpt = ""
            refactor_history.append(
                {
                    "round": total_rounds,
                    "result": "noop",
                    "summary": summary,
                    "touched_theorems": last_touched_theorems,
                    "candidate_hash": candidate_fingerprint(candidate_code),
                    "error_fingerprint": "",
                }
            )
            emit_progress_event(
                progress_log_file,
                pass_name="pass_1",
                phase="worker_result",
                round=total_rounds,
                result="noop",
                focus_theorem_names=last_touched_theorems,
                repair_round=repair_round,
                error_excerpt="",
            )
            no_progress, no_progress_reason = detect_no_progress(refactor_history)
            if no_progress:
                raw_stop_reason = f"no_progress:{no_progress_reason}"
                debug_log(f"Refactor round {total_rounds}: stopping ({raw_stop_reason})")
                break
            continue

        debug_log(f"Refactor round {total_rounds}: verifying Lean candidate")
        emit_progress_event(
            progress_log_file,
            pass_name="pass_1",
            phase="verify_start",
            round=total_rounds,
            result="running",
            focus_theorem_names=last_touched_theorems,
            repair_round=repair_round,
            error_excerpt="",
        )
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
                    "candidate_hash": candidate_fingerprint(candidate_code),
                    "error_fingerprint": error_fingerprint(last_error_excerpt),
                }
            )
            emit_progress_event(
                progress_log_file,
                pass_name="pass_1",
                phase="verify_result",
                round=total_rounds,
                result="verify_failed",
                focus_theorem_names=last_touched_theorems,
                repair_round=repair_round,
                error_excerpt=last_error_excerpt,
            )
            no_progress, no_progress_reason = detect_no_progress(refactor_history)
            if no_progress:
                raw_stop_reason = f"no_progress:{no_progress_reason}"
                debug_log(f"Refactor round {total_rounds}: stopping ({raw_stop_reason})")
                break
            continue

        current_code = candidate_code
        current_inventory = extract_theorem_entries_from_code(derived_file, current_code)
        previous_refactored_code = candidate_code
        lean_diagnostics = ""
        last_error_excerpt = ""
        accepted_rounds += 1
        changed = True
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
        emit_progress_event(
            progress_log_file,
            pass_name="pass_1",
            phase="verify_result",
            round=total_rounds,
            result="accepted",
            focus_theorem_names=last_touched_theorems,
            repair_round=repair_round,
            error_excerpt="",
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
    stop_reason, stop_detail = normalize_stop_reason(raw_stop_reason)
    emit_progress_finish(
        progress_log_file,
        pass_name="pass_1",
        round=total_rounds,
        result=status,
        stop_reason=stop_reason,
        focus_theorem_names=last_touched_theorems,
    )
    return build_report(
        status,
        stop_reason,
        stop_detail=stop_detail,
        input_file=derived_file,
        output_file=written_output,
        extra={
            "accepted_rounds": accepted_rounds,
            "total_rounds": total_rounds,
            "summary": last_summary,
            "change_notes": last_change_notes,
            "touched_theorems": last_touched_theorems,
            "verify_success": True,
            "backup_file": backup_output,
            "duplicate_statement_group_count": len(build_exact_duplicate_statement_groups(current_inventory)),
            "refactor_output_theorem_count": len(current_inventory),
            "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
        },
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="LLM-guided refactoring for AutomatedTheoryConstruction/Derived.lean")
    worker_timeout_help = "Per worker subprocess timeout in seconds."
    verify_timeout_help = "Per Lean verification timeout in seconds."
    retry_budget_help = "Whole pass 1 wall-clock budget in seconds."
    parser.add_argument("--derived-file", default="AutomatedTheoryConstruction/Derived.lean")
    parser.add_argument("--theory-file", default="AutomatedTheoryConstruction/Theory.lean")
    parser.add_argument("--prompt-file", default="prompts/derived/refactorer.md")
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--verify-timeout", type=int, help=verify_timeout_help)
    parser.add_argument("--output-file")
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--backup-file")
    parser.add_argument("--progress-log-file", default=str(DEFAULT_PROGRESS_LOG))
    parser.add_argument("--theorem-reuse-memory-file", default="data/theorem_reuse_memory.json")
    parser.add_argument("--target-theorem-name")
    parser.add_argument("--max-wall-clock-sec", type=int, help=retry_budget_help)
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
    progress_log_file = Path(args.progress_log_file) if args.progress_log_file else None

    report = run_refactor_derived(
        derived_file=derived_file,
        theory_file=theory_file,
        prompt_file=prompt_file,
        theorem_reuse_memory_file=theorem_reuse_memory_file,
        output_file=output_file,
        apply_in_place=args.apply,
        backup_file=backup_file,
        verify_timeout_sec=args.verify_timeout,
        progress_log_file=progress_log_file,
        worker_command=args.worker_command,
        worker_timeout=args.worker_timeout,
        target_theorem_name=args.target_theorem_name,
        max_wall_clock_sec=args.max_wall_clock_sec,
    )
    print_report(report)
    if report.get("status") == "error":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
