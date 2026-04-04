from __future__ import annotations

import argparse
import json
import re
import time
from pathlib import Path
from typing import Any

from append_derived import build_derived_entries_from_file
from derived_refactor_utils import build_report
from derived_refactor_utils import build_exact_duplicate_statement_groups
from derived_refactor_utils import candidate_fingerprint
from derived_refactor_utils import check_order_preservation_outside_region
from derived_refactor_utils import compare_theorem_inventories
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
from derived_refactor_utils import write_report
from theorem_reuse_memory import load_theorem_reuse_memory
from theorem_reuse_memory import summarize_supporting_theorem_frequency
from worker_client import invoke_worker_json


DEFAULT_INPUT = Path("AutomatedTheoryConstruction/Derived.refactored.preview.lean")
DEFAULT_PLAN = Path("AutomatedTheoryConstruction/Derived.compression.plan.json")
DEFAULT_REPORT = Path("AutomatedTheoryConstruction/Derived.compression.report.json")
DEFAULT_PROGRESS_LOG = Path("AutomatedTheoryConstruction/Derived.compression.executor.log.jsonl")
DEFAULT_PROMPT = Path("prompts/derived_compression_executor.md")
DEFAULT_THEOREM_REUSE_MEMORY = Path("data/theorem_reuse_memory.json")

SECTION_HEADING_PREFIX = "/-! ## "


def load_plan(plan_file: Path) -> dict[str, Any]:
    payload = json.loads(load_text(plan_file))
    if not isinstance(payload, dict):
        raise ValueError("compression plan must be a JSON object")
    items = payload.get("items", [])
    if not isinstance(items, list):
        raise ValueError("compression plan items must be a list")
    payload["items"] = [item for item in items if isinstance(item, dict)]
    return payload


def build_payload(
    *,
    input_file: Path,
    derived_code: str,
    theorem_inventory: list[dict[str, str]],
    plan_item: dict[str, Any],
    theorem_reuse_memory: list[dict[str, Any]],
    supporting_theorem_frequency: list[dict[str, Any]],
    repair_round: int,
    previous_refactored_code: str,
    lean_diagnostics: str,
    last_error_excerpt: str,
    item_history_tail: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "input_file": str(input_file),
        "derived_code": derived_code,
        "theorem_inventory": theorem_inventory,
        "exact_duplicate_statement_groups": build_exact_duplicate_statement_groups(theorem_inventory),
        "plan_item": plan_item,
        "theorem_reuse_memory": theorem_reuse_memory[-12:],
        "supporting_theorem_frequency": supporting_theorem_frequency[:20],
        "repair_round": repair_round,
        "previous_refactored_code": previous_refactored_code,
        "current_candidate_code": previous_refactored_code,
        "lean_diagnostics": "\n".join(lean_diagnostics.splitlines()[:120]),
        "last_error_excerpt": last_error_excerpt,
        "item_history_tail": item_history_tail[-6:],
    }


def _allowed_region_for_item(item: dict[str, Any]) -> list[str]:
    region = [str(name).strip() for name in item.get("local_reorder_region", []) if str(name).strip()]
    if region:
        return region
    names: list[str] = []
    for key in ("anchor_theorems", "rewrite_targets", "new_theorems", "section_members"):
        for name in item.get(key, []):
            cleaned = str(name).strip()
            if cleaned and cleaned not in names:
                names.append(cleaned)
    insert_before = str(item.get("insert_before", "")).strip()
    if insert_before and insert_before not in names:
        names.append(insert_before)
    return names


def _render_section_heading(title: str) -> str:
    cleaned = " ".join(str(title).split())
    if not cleaned:
        raise ValueError("section heading title must be non-empty")
    return f"{SECTION_HEADING_PREFIX}{cleaned} -/"


def _apply_cluster_sectionize_item(
    *,
    derived_code: str,
    item: dict[str, Any],
) -> tuple[str, str, str, list[str], list[str]]:
    section_title = str(item.get("section_title", "")).strip()
    insert_before = str(item.get("insert_before", "")).strip()
    section_members = _allowed_region_for_item(item)
    if not section_title:
        raise ValueError("cluster_sectionize item is missing section_title")
    if not insert_before:
        raise ValueError("cluster_sectionize item is missing insert_before")
    if len(section_members) < 2:
        raise ValueError("cluster_sectionize item must target at least two theorems")

    heading_line = _render_section_heading(section_title)
    lines = derived_code.splitlines(keepends=True)
    theorem_line_index: int | None = None
    theorem_pattern = re.compile(rf"^theorem\s+{re.escape(insert_before)}\b")
    for index, line in enumerate(lines):
        if theorem_pattern.match(line):
            theorem_line_index = index
            break
    if theorem_line_index is None:
        raise ValueError(f"cluster_sectionize insert_before target not found: {insert_before}")

    insert_index = theorem_line_index
    if insert_index > 0 and lines[insert_index - 1].lstrip().startswith("/--"):
        insert_index -= 1

    heading_check_index = insert_index - 1
    while heading_check_index >= 0 and not lines[heading_check_index].strip():
        heading_check_index -= 1
    if heading_check_index >= 0 and lines[heading_check_index].strip() == heading_line:
        return (
            "noop",
            derived_code.strip(),
            f"Section heading for {insert_before} already present.",
            [],
            section_members,
        )

    updated_lines = list(lines)
    updated_lines.insert(insert_index, heading_line + "\n\n")
    updated_code = "".join(updated_lines).strip()
    return (
        "ok",
        updated_code,
        f"Inserted section heading before {insert_before}.",
        [f"Inserted section heading `{section_title}` before `{insert_before}`."],
        section_members,
    )


def _policy_check(
    *,
    before_entries: list[dict[str, str]],
    after_entries: list[dict[str, str]],
    item: dict[str, Any],
) -> tuple[bool, str]:
    compare_result = compare_theorem_inventories(before_entries, after_entries)
    if not compare_result["ok"]:
        missing_names = ",".join(compare_result["missing_names"][:4])
        changed_names = ",".join(compare_result["changed_statements"][:4])
        return False, f"inventory preservation failed missing=[{missing_names}] changed=[{changed_names}]"

    if str(item.get("kind", "")).strip() == "cluster_reorder":
        order_result = check_order_preservation_outside_region(
            before_entries,
            after_entries,
            _allowed_region_for_item(item),
        )
        if not order_result["ok"]:
            return False, "cluster_reorder changed theorem order outside the local region"

    return True, ""


def run_apply_derived_compression_plan(
    *,
    input_file: Path,
    plan_file: Path,
    output_file: Path,
    report_file: Path,
    prompt_file: Path,
    theorem_reuse_memory_file: Path,
    progress_log_file: Path | None,
    verify_timeout_sec: int | None,
    max_wall_clock_sec: int | None,
    worker_settings: WorkerSettings | None = None,
    worker_command: str | None = None,
    worker_timeout: int | None = None,
) -> dict[str, Any]:
    prompt_text = load_text(prompt_file)
    current_code = load_text(input_file)
    current_inventory = build_derived_entries_from_file(input_file)
    original_inventory = list(current_inventory)
    plan_payload = load_plan(plan_file)
    theorem_reuse_memory = load_theorem_reuse_memory(theorem_reuse_memory_file)
    supporting_theorem_frequency = summarize_supporting_theorem_frequency(theorem_reuse_memory)

    worker_settings = resolve_refactor_worker_settings(
        worker_settings=worker_settings,
        worker_command=worker_command,
        worker_timeout=worker_timeout,
    )

    items = [item for item in plan_payload.get("items", []) if isinstance(item, dict)]
    before_duplicate_group_count = len(build_exact_duplicate_statement_groups(current_inventory))
    executor_items: list[dict[str, Any]] = []
    deadline = None if max_wall_clock_sec in (None, 0) else time.monotonic() + max_wall_clock_sec
    raw_stop_reason = "completed"
    stopped = False
    emit_progress_start(progress_log_file, pass_name="pass_1.2")

    for index, item in enumerate(items, start=1):
        if deadline is not None and time.monotonic() >= deadline:
            raw_stop_reason = "budget_exhausted:max_wall_clock_reached"
            stopped = True
            break
        item_id = str(item.get("id", f"item_{index:03d}")).strip() or f"item_{index:03d}"
        item_history: list[dict[str, Any]] = []
        previous_refactored_code = ""
        lean_diagnostics = ""
        last_error_excerpt = ""
        accepted = False
        reject_reason = ""
        last_summary = ""
        last_change_notes: list[str] = []
        last_touched_theorems: list[str] = []

        debug_log(f"Compression item {item_id}: kind={item.get('kind', '')}")
        emit_progress_event(
            progress_log_file,
            pass_name="pass_1.2",
            phase="item_start",
            round=index,
            result="running",
            item_id=item_id,
            error_excerpt="",
        )

        while True:
            if deadline is not None and time.monotonic() >= deadline:
                reject_reason = "budget_exhausted:max_wall_clock_reached"
                raw_stop_reason = reject_reason
                stopped = True
                emit_progress_event(
                    progress_log_file,
                    pass_name="pass_1.2",
                    phase="budget_stop",
                    round=index,
                    result="stopped",
                    item_id=item_id,
                    repair_round=len(item_history),
                    touched_theorems=last_touched_theorems,
                    error_excerpt="max_wall_clock_reached",
                )
                break
            repair_round = len(item_history)
            payload = build_payload(
                input_file=input_file,
                derived_code=current_code,
                theorem_inventory=current_inventory,
                plan_item=item,
                theorem_reuse_memory=theorem_reuse_memory,
                supporting_theorem_frequency=supporting_theorem_frequency,
                repair_round=repair_round,
                previous_refactored_code=previous_refactored_code,
                lean_diagnostics=lean_diagnostics,
                last_error_excerpt=last_error_excerpt,
                item_history_tail=item_history,
            )
            emit_progress_event(
                progress_log_file,
                pass_name="pass_1.2",
                phase="repair_round_start",
                round=index,
                result="running",
                item_id=item_id,
                repair_round=repair_round,
                error_excerpt=last_error_excerpt,
            )
            try:
                if str(item.get("kind", "")).strip() == "cluster_sectionize":
                    result, candidate_code, summary, change_notes, touched_theorems = _apply_cluster_sectionize_item(
                        derived_code=current_code,
                        item=item,
                    )
                else:
                    raw_result, _worker_meta = invoke_worker_json(
                        settings=worker_settings,
                        task_type="apply_derived_compression_item",
                        system_prompt=prompt_text,
                        payload=payload,
                        metadata={"item_id": item_id, "repair_round": repair_round},
                    )
                    result, candidate_code, summary, change_notes, touched_theorems = validate_full_file_refactor_output(
                        raw_result,
                        label="compression executor output",
                    )
            except Exception as exc:
                reject_reason = f"worker_error:{single_line_excerpt(str(exc), limit=120)}"
                emit_progress_error(
                    progress_log_file,
                    pass_name="pass_1.2",
                    phase="worker_error",
                    round=index,
                    stop_reason="worker_error",
                    item_id=item_id,
                    repair_round=repair_round,
                    error_excerpt=single_line_excerpt(str(exc), limit=120),
                )
                break
            last_summary = summary
            last_change_notes = change_notes
            last_touched_theorems = touched_theorems or _allowed_region_for_item(item)

            if result == "stuck":
                reject_reason = "worker_stuck"
                emit_progress_event(
                    progress_log_file,
                    pass_name="pass_1.2",
                    phase="worker_result",
                    round=index,
                    result="stuck",
                    item_id=item_id,
                    repair_round=repair_round,
                    touched_theorems=last_touched_theorems,
                    error_excerpt="worker returned stuck",
                )
                break

            if result == "noop" or candidate_code.strip() == current_code.strip():
                item_history.append(
                    {
                        "result": "noop",
                        "candidate_hash": candidate_fingerprint(candidate_code),
                        "error_fingerprint": "",
                        "touched_theorems": last_touched_theorems,
                    }
                )
                previous_refactored_code = candidate_code
                lean_diagnostics = ""
                last_error_excerpt = ""
                emit_progress_event(
                    progress_log_file,
                    pass_name="pass_1.2",
                    phase="worker_result",
                    round=index,
                    result="noop",
                    item_id=item_id,
                    repair_round=repair_round,
                    touched_theorems=last_touched_theorems,
                    error_excerpt="",
                )
                no_progress, no_progress_reason = detect_no_progress(item_history)
                if no_progress:
                    reject_reason = f"no_progress:{no_progress_reason}"
                    break
                continue

            candidate_inventory = extract_theorem_entries_from_code(input_file, candidate_code)
            policy_ok, policy_error = _policy_check(
                before_entries=current_inventory,
                after_entries=candidate_inventory,
                item=item,
            )
            if not policy_ok:
                previous_refactored_code = candidate_code
                lean_diagnostics = policy_error
                last_error_excerpt = single_line_excerpt(policy_error)
                item_history.append(
                    {
                        "result": "policy_failed",
                        "candidate_hash": candidate_fingerprint(candidate_code),
                        "error_fingerprint": error_fingerprint(policy_error),
                        "touched_theorems": last_touched_theorems,
                    }
                )
                emit_progress_event(
                    progress_log_file,
                    pass_name="pass_1.2",
                    phase="policy_result",
                    round=index,
                    result="policy_failed",
                    item_id=item_id,
                    repair_round=repair_round,
                    touched_theorems=last_touched_theorems,
                    error_excerpt=last_error_excerpt,
                )
                no_progress, no_progress_reason = detect_no_progress(item_history)
                if no_progress:
                    reject_reason = f"no_progress:{no_progress_reason}"
                    break
                continue

            emit_progress_event(
                progress_log_file,
                pass_name="pass_1.2",
                phase="verify_start",
                round=index,
                result="running",
                item_id=item_id,
                repair_round=repair_round,
                touched_theorems=last_touched_theorems,
                error_excerpt="",
            )
            verify_result = verify_refactored_code(input_file, candidate_code, verify_timeout_sec)
            lean_diagnostics = (str(verify_result.get("stderr", "")) + "\n" + str(verify_result.get("stdout", ""))).strip()
            verify_success = bool(verify_result.get("success", False))
            last_error_excerpt = single_line_excerpt(lean_diagnostics.splitlines()[0] if lean_diagnostics else "")

            if not verify_success:
                previous_refactored_code = candidate_code
                item_history.append(
                    {
                        "result": "verify_failed",
                        "candidate_hash": candidate_fingerprint(candidate_code),
                        "error_fingerprint": error_fingerprint(last_error_excerpt),
                        "touched_theorems": last_touched_theorems,
                    }
                )
                emit_progress_event(
                    progress_log_file,
                    pass_name="pass_1.2",
                    phase="verify_result",
                    round=index,
                    result="verify_failed",
                    item_id=item_id,
                    repair_round=repair_round,
                    touched_theorems=last_touched_theorems,
                    error_excerpt=last_error_excerpt,
                )
                no_progress, no_progress_reason = detect_no_progress(item_history)
                if no_progress:
                    reject_reason = f"no_progress:{no_progress_reason}"
                    break
                continue

            current_code = candidate_code
            current_inventory = candidate_inventory
            accepted = True
            item_history.append(
                {
                    "result": "accepted",
                    "candidate_hash": candidate_fingerprint(candidate_code),
                    "error_fingerprint": "",
                    "touched_theorems": last_touched_theorems,
                }
            )
            emit_progress_event(
                progress_log_file,
                pass_name="pass_1.2",
                phase="verify_result",
                round=index,
                result="accepted",
                item_id=item_id,
                repair_round=repair_round,
                touched_theorems=last_touched_theorems,
                error_excerpt="",
            )
            break

        executor_items.append(
            {
                "id": item_id,
                "kind": str(item.get("kind", "")).strip(),
                "result": "accepted" if accepted else "rejected",
                "summary": last_summary,
                "change_notes": last_change_notes,
                "touched_theorems": last_touched_theorems,
                "stop_reason": "" if accepted else normalize_stop_reason(reject_reason or "completed")[0],
                "stop_detail": "" if accepted else normalize_stop_reason(reject_reason or "completed")[1],
                "repair_rounds": len(item_history),
            }
        )
        if stopped:
            break

    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(current_code.strip() + "\n", encoding="utf-8")
    stop_reason, stop_detail = normalize_stop_reason(raw_stop_reason)
    status = "stopped" if stopped else "ok"
    report = build_report(
        status,
        stop_reason,
        stop_detail=stop_detail,
        input_file=input_file,
        output_file=output_file,
        report_file=report_file,
        extra={
            "plan_file": str(plan_file),
            "items": executor_items,
            "accepted_count": sum(1 for item in executor_items if item["result"] == "accepted"),
            "rejected_count": sum(1 for item in executor_items if item["result"] == "rejected"),
            "before_duplicate_group_count": before_duplicate_group_count,
            "after_duplicate_group_count": len(build_exact_duplicate_statement_groups(current_inventory)),
            "before_theorem_count": len(original_inventory),
            "after_theorem_count": len(current_inventory),
            "progress_log_file": str(progress_log_file) if progress_log_file is not None else None,
        },
    )
    write_report(report_file, report)
    emit_progress_finish(
        progress_log_file,
        pass_name="pass_1.2",
        round=len(executor_items),
        result=status,
        stop_reason=stop_reason,
    )
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Apply a planned soft-compression pass to Derived.refactored.preview.lean")
    worker_timeout_help = "Per worker subprocess timeout in seconds."
    verify_timeout_help = "Per Lean verification timeout in seconds."
    retry_budget_help = "Whole pass 1.2 wall-clock budget in seconds."
    parser.add_argument("--input-file", default=str(DEFAULT_INPUT))
    parser.add_argument("--plan-file", default=str(DEFAULT_PLAN))
    parser.add_argument("--output-file", default=str(DEFAULT_INPUT))
    parser.add_argument("--report-file", default=str(DEFAULT_REPORT))
    parser.add_argument("--progress-log-file", default=str(DEFAULT_PROGRESS_LOG))
    parser.add_argument("--prompt-file", default=str(DEFAULT_PROMPT))
    parser.add_argument("--theorem-reuse-memory-file", default=str(DEFAULT_THEOREM_REUSE_MEMORY))
    parser.add_argument("--worker-command")
    parser.add_argument("--worker-timeout", type=int, help=worker_timeout_help)
    parser.add_argument("--verify-timeout", type=int, help=verify_timeout_help)
    parser.add_argument("--max-wall-clock-sec", type=int, help=retry_budget_help)
    args = parser.parse_args()

    report = run_apply_derived_compression_plan(
        input_file=Path(args.input_file),
        plan_file=Path(args.plan_file),
        output_file=Path(args.output_file),
        report_file=Path(args.report_file),
        prompt_file=Path(args.prompt_file),
        theorem_reuse_memory_file=Path(args.theorem_reuse_memory_file),
        progress_log_file=Path(args.progress_log_file) if args.progress_log_file else None,
        verify_timeout_sec=args.verify_timeout,
        max_wall_clock_sec=args.max_wall_clock_sec,
        worker_command=args.worker_command,
        worker_timeout=args.worker_timeout,
    )
    print_report(report)


if __name__ == "__main__":
    main()
