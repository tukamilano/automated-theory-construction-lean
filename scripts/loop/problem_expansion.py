from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any
from typing import Callable

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
scripts_root_str = str(SCRIPTS_ROOT)
if scripts_root_str not in sys.path:
    sys.path.insert(0, scripts_root_str)

from common import ARCHIVED_PROBLEMS_FILENAME
from common import append_jsonl
from common import dedupe_problem_rows_by_stmt
from common import merge_archived_problem_rows
from common import next_problem_id
from common import normalize_open_problem_priority
from common import normalize_open_problem_row
from common import partition_open_problem_rows
from common import read_archived_problem_rows
from common import read_jsonl
from common import write_json_atomic
from common import write_jsonl_atomic
from guidance import unpack_guidance_context
from loop_helpers import load_current_guidance
from loop_helpers import load_current_research_agenda
from loop_helpers import load_theory_state
from loop_helpers import normalize_stmt_text
from loop_helpers import open_problem_priority_label
from loop_helpers import theory_state_path
from prompt_loader import load_prompt_file
from research_agenda import summarize_research_agenda_for_state
from worker_client import invoke_worker_json


OPEN_PROBLEM_PRIORITY_ORDER = {
    "high": 0,
    "medium": 1,
    "unknown": 2,
    "low": 3,
}


def append_current_iteration_log(
    current_iteration_full_logs: list[dict[str, Any]],
    *,
    stage: str,
    index: int,
    worker_meta: dict[str, Any],
) -> None:
    raw_model_output = worker_meta.get("raw_model_output")
    if not isinstance(raw_model_output, str) or not raw_model_output.strip():
        return
    current_iteration_full_logs.append(
        {
            "stage": stage,
            "index": index,
            "raw_model_output": raw_model_output,
        }
    )


def validate_problem_candidates_output(
    payload: dict[str, Any],
    *,
    expected_problem_id: str,
    max_candidates: int,
) -> list[dict[str, str]]:
    required_keys = {"problem_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("candidate output must contain exactly: problem_id, candidates")

    problem_id = str(payload.get("problem_id", "")).strip()
    if problem_id != expected_problem_id:
        raise ValueError("candidate output problem_id does not match request")

    candidates_value = payload.get("candidates")
    if not isinstance(candidates_value, list):
        raise ValueError("candidate output candidates must be an array of objects")
    if len(candidates_value) > max_candidates:
        raise ValueError(f"candidate output candidates must have length <= {max_candidates}")

    parsed: list[dict[str, str]] = []
    seen_norms: set[str] = set()
    for item in candidates_value:
        if not isinstance(item, dict) or set(item.keys()) != {"statement", "rationale"}:
            raise ValueError("each candidate must contain exactly: statement, rationale")
        statement = item.get("statement")
        rationale = item.get("rationale")
        if not isinstance(statement, str) or not isinstance(rationale, str):
            raise ValueError("candidate statement and rationale must be strings")
        normalized_statement = statement.strip()
        if not normalized_statement:
            continue
        norm = normalize_stmt_text(normalized_statement)
        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        parsed.append({"statement": normalized_statement, "rationale": rationale.strip()})

    return parsed[:max_candidates]


def validate_next_direction_payload(payload: Any) -> dict[str, str]:
    required_keys = {"label", "guidance", "rationale"}
    if not isinstance(payload, dict) or set(payload.keys()) != required_keys:
        raise ValueError("next_direction must contain exactly: label, guidance, rationale")

    label = str(payload.get("label", "")).strip()
    guidance = str(payload.get("guidance", "")).strip()
    rationale = str(payload.get("rationale", "")).strip()
    if not label or not guidance or not rationale:
        raise ValueError("next_direction label, guidance, and rationale must be non-empty")
    return {"label": label, "guidance": guidance, "rationale": rationale}


def validate_theory_snapshot_payload(payload: Any) -> str:
    theory_snapshot = str(payload or "").strip()
    if not theory_snapshot:
        raise ValueError("theory_snapshot must be non-empty")
    return theory_snapshot


def validate_string_list_payload(payload: Any, field_name: str, *, max_items: int = 6) -> list[str]:
    if not isinstance(payload, list):
        raise ValueError(f"{field_name} must be an array of strings")
    parsed: list[str] = []
    seen_norms: set[str] = set()
    for item in payload:
        if not isinstance(item, str):
            raise ValueError(f"{field_name} must contain only strings")
        value = item.strip()
        if not value:
            continue
        norm = " ".join(value.split()).lower()
        if norm in seen_norms:
            continue
        seen_norms.add(norm)
        parsed.append(value)
    return parsed[:max_items]


def validate_open_problem_priority_output(
    payload: dict[str, Any],
    expected_problem_ids: list[str],
) -> tuple[list[dict[str, str]], str, dict[str, str], dict[str, list[str]]]:
    required_keys = {
        "priorities",
        "theory_snapshot",
        "next_direction",
        "desired_summary_changes",
        "current_bottlenecks",
        "overexplored_patterns",
        "missing_bridges",
        "agenda_pressure",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("priority refresh output keys mismatch")

    priorities_value = payload.get("priorities")
    if not isinstance(priorities_value, list):
        raise ValueError("priority refresh priorities must be an array of objects")

    expected_id_set = set(expected_problem_ids)
    seen_ids: set[str] = set()
    parsed: list[dict[str, str]] = []
    for item in priorities_value:
        if not isinstance(item, dict) or set(item.keys()) != {"problem_id", "priority", "rationale"}:
            raise ValueError("each priority item must contain exactly: problem_id, priority, rationale")
        problem_id = str(item.get("problem_id", "")).strip()
        priority = normalize_open_problem_priority(item.get("priority"))
        rationale = str(item.get("rationale", "")).strip()
        if problem_id not in expected_id_set:
            raise ValueError(f"unexpected problem_id in priority refresh output: {problem_id}")
        if problem_id in seen_ids:
            raise ValueError(f"duplicate problem_id in priority refresh output: {problem_id}")
        if priority not in {"high", "medium", "low"}:
            raise ValueError(f"priority must be high|medium|low, got {priority}")
        seen_ids.add(problem_id)
        parsed.append({"problem_id": problem_id, "priority": priority, "rationale": rationale})

    if seen_ids != expected_id_set:
        missing = sorted(expected_id_set - seen_ids)
        raise ValueError(f"priority refresh output missing problem_ids: {missing}")

    theory_frontier = {
        "desired_summary_changes": validate_string_list_payload(payload.get("desired_summary_changes"), "desired_summary_changes"),
        "current_bottlenecks": validate_string_list_payload(payload.get("current_bottlenecks"), "current_bottlenecks"),
        "overexplored_patterns": validate_string_list_payload(payload.get("overexplored_patterns"), "overexplored_patterns"),
        "missing_bridges": validate_string_list_payload(payload.get("missing_bridges"), "missing_bridges"),
        "agenda_pressure": validate_string_list_payload(payload.get("agenda_pressure"), "agenda_pressure"),
    }
    return parsed, validate_theory_snapshot_payload(payload.get("theory_snapshot")), validate_next_direction_payload(payload.get("next_direction")), theory_frontier


def load_prompt_text(prompt_file: str) -> str:
    return load_prompt_file(Path(prompt_file))


def request_expand_candidates(
    *,
    worker_settings: Any,
    expand_prompt: str,
    task_type: str,
    problem_id: str,
    stmt: str,
    original_stmt: str,
    result: str,
    verify_success: bool,
    theory_context: str,
    open_rows: list[dict[str, Any]],
    existing_new_problems: list[str],
    verify_error_excerpt: str,
    current_iteration_full_logs: list[dict[str, Any]],
    same_problem_history_tail: list[dict[str, Any]],
    theory_state: dict[str, Any] | None = None,
    max_candidates: int = 3,
) -> tuple[list[dict[str, str]], dict[str, Any]]:
    expand_payload: dict[str, Any] = {
        "problem_id": problem_id,
        "stmt": stmt,
        "original_stmt": original_stmt,
        "result": result,
        "verify_success": verify_success,
        "theory_context": theory_context,
        "open_problems": open_rows,
        "existing_new_problems": list(existing_new_problems),
        "verify_error_excerpt": verify_error_excerpt,
        "current_iteration_full_logs": list(current_iteration_full_logs),
        "same_problem_history_tail": same_problem_history_tail,
        "theory_state": dict(theory_state or {}),
        "research_agenda": load_current_research_agenda(),
        "expand_generation_policy": {
            "prefer_subgoals_for_unsolved": True,
            "avoid_generalization_for_unsolved": True,
            "prefer_same_problem_decomposition": True,
            "prefer_intermediate_lemmas": True,
        },
    }
    expanded, expand_worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type=task_type,
        system_prompt=expand_prompt,
        payload=expand_payload,
        metadata={"problem_id": problem_id},
    )
    append_current_iteration_log(current_iteration_full_logs, stage="expand", index=1, worker_meta=expand_worker_meta)
    return validate_problem_candidates_output(expanded, expected_problem_id=problem_id, max_candidates=max_candidates), expand_worker_meta


def request_open_problem_priorities(
    *,
    worker_settings: Any,
    prioritizer_prompt: str,
    tracked_rows: list[dict[str, Any]],
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[list[dict[str, str]], str, dict[str, str], dict[str, list[str]], dict[str, Any]]:
    previous_theory_state, research_agenda = unpack_guidance_context(guidance)
    expected_problem_ids = [str(row.get("id", "")) for row in tracked_rows]
    priority_payload: dict[str, Any] = {
        "current_iteration": current_iteration,
        "tracked_problems": [
            {
                "problem_id": str(row.get("id", "")),
                "stmt": str(row.get("stmt", "")),
                "src": str(row.get("src", "")),
                "source_kind": str(row.get("source_kind", row.get("queue_status", "open"))),
                "queue_status": str(row.get("queue_status", row.get("source_kind", "open"))),
                "mode": str(row.get("mode", "")),
                "summary_delta": str(row.get("summary_delta", "")),
            }
            for row in tracked_rows
        ],
        "derived_theorems": [{"name": str(entry.get("name", "")), "statement": str(entry.get("statement", ""))} for entry in derived_entries],
        "priority_rubric": {
            "high": "Connects existing clusters, gives a strong equivalence/characterization/existence theorem, or is likely to unlock many future problems.",
            "medium": "Natural local extension with plausible reuse for one or two nearby problems.",
            "low": "Cosmetic variant, shallow restatement, or currently low-utility statement given the present Derived.lean.",
        },
        "previous_theory_state": previous_theory_state,
        "research_agenda": research_agenda,
    }
    prioritized, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="prioritize_open_problems",
        system_prompt=prioritizer_prompt,
        payload=priority_payload,
        metadata={"tracked_problem_count": len(tracked_rows), "derived_theorem_count": len(derived_entries)},
    )
    priority_updates, theory_snapshot, next_direction, theory_frontier = validate_open_problem_priority_output(prioritized, expected_problem_ids)
    return priority_updates, theory_snapshot, next_direction, theory_frontier, worker_meta


def append_expand_candidates(
    *,
    data_dir: Path,
    statements_with_rationale: list[dict[str, str]],
    source: str,
    source_problem_id: str,
    source_kind: str,
) -> list[dict[str, Any]]:
    if not statements_with_rationale:
        return []
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")]
    archived_rows = read_archived_problem_rows(data_dir)
    solved_rows = read_jsonl(data_dir / "solved_problems.jsonl")
    counter_rows = read_jsonl(data_dir / "counterexamples.jsonl")
    seen_norms = {
        normalize_stmt_text(str(row.get("stmt", "")))
        for row in (open_rows + archived_rows + solved_rows + counter_rows)
        if str(row.get("stmt", "")).strip()
    }
    all_ids = [str(row.get("id", "")) for row in (open_rows + archived_rows + solved_rows + counter_rows)]
    added_rows: list[dict[str, Any]] = []
    next_rows = list(open_rows)
    for item in statements_with_rationale:
        stmt = str(item.get("statement", "")).strip()
        rationale = str(item.get("rationale", "")).strip()
        norm = normalize_stmt_text(stmt)
        if not stmt or not norm or norm in seen_norms:
            continue
        new_id = next_problem_id(all_ids)
        all_ids.append(new_id)
        seen_norms.add(norm)
        new_row = normalize_open_problem_row(
            {
                "id": new_id,
                "stmt": stmt,
                "src": source,
                "mode": "expand_candidate",
                "summary_delta": rationale,
                "source_kind": "expand_candidate",
                "generated_from_source_id": source_problem_id,
                "generated_from_source_kind": source_kind,
                "priority": "unknown",
                "priority_rationale": "",
                "failure_count": 0,
            }
        )
        next_rows.append(new_row)
        added_rows.append(dict(new_row))
    if added_rows:
        write_jsonl_atomic(data_dir / "open_problems.jsonl", dedupe_problem_rows_by_stmt(next_rows))
    return added_rows


def collect_important_verified_counterexamples(data_dir: Path, *, max_items: int = 3, max_chars: int = 240) -> list[str]:
    rows = read_jsonl(data_dir / "counterexamples.jsonl")
    summaries: list[str] = []
    seen_stmt_norms: set[str] = set()
    for row in reversed(rows):
        stmt = normalize_stmt_text(str(row.get("stmt", "")))
        if not stmt or stmt in seen_stmt_norms:
            continue
        seen_stmt_norms.add(stmt)
        summary = f"Verified counterexample to: {stmt}"
        if len(summary) > max_chars:
            summary = summary[: max_chars - 3] + "..."
        summaries.append(summary)
        if len(summaries) >= max_items:
            break
    return summaries


def open_problem_sort_key(row: dict[str, Any], *, failure_archive_threshold: int) -> tuple[int, int, int]:
    priority_order = OPEN_PROBLEM_PRIORITY_ORDER.get(open_problem_priority_label(row), OPEN_PROBLEM_PRIORITY_ORDER["unknown"])
    failure_count = int(row.get("failure_count", 0) or 0)
    archived = 1 if failure_archive_threshold > 0 and failure_count >= failure_archive_threshold else 0
    return (archived, priority_order, failure_count)


def sort_open_problem_queue(open_rows: list[dict[str, Any]], *, failure_archive_threshold: int) -> list[dict[str, Any]]:
    normalized_rows = [normalize_open_problem_row(row) for row in open_rows]
    return sorted(normalized_rows, key=lambda row: open_problem_sort_key(row, failure_archive_threshold=failure_archive_threshold))


def split_active_and_archived_problem_queues(
    tracked_rows: list[dict[str, Any]],
    *,
    failure_archive_threshold: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    sorted_rows = sort_open_problem_queue(tracked_rows, failure_archive_threshold=failure_archive_threshold)
    return partition_open_problem_rows(sorted_rows, failure_threshold=failure_archive_threshold)


def apply_open_problem_priorities(open_rows: list[dict[str, Any]], priority_updates: list[dict[str, str]]) -> list[dict[str, Any]]:
    updates_by_id = {item["problem_id"]: item for item in priority_updates}
    updated_rows: list[dict[str, Any]] = []
    for row in open_rows:
        normalized = normalize_open_problem_row(row)
        update = updates_by_id.get(str(normalized.get("id", "")))
        if update is not None:
            normalized["priority"] = update["priority"]
            normalized["priority_rationale"] = update["rationale"]
        updated_rows.append(normalized)
    return updated_rows


def needs_bootstrap_priority_refresh(open_rows: list[dict[str, Any]]) -> bool:
    return any(open_problem_priority_label(row) == "unknown" for row in open_rows)


def write_theory_state(
    data_dir: Path,
    *,
    run_id: str,
    current_iteration: int,
    derived_theorem_count: int,
    open_problem_count: int,
    archived_problem_count: int,
    theory_snapshot: str,
    next_direction: dict[str, Any],
    important_verified_counterexamples: list[str],
    research_agenda_summary: dict[str, Any] | None = None,
    theory_frontier: dict[str, list[str]] | None = None,
) -> dict[str, Any]:
    existing_payload = load_theory_state(data_dir)
    frontier = dict(theory_frontier or {})
    payload = {
        "version": 1,
        "updated_at_iteration": current_iteration,
        "updated_at_run_id": run_id,
        "theory_snapshot": theory_snapshot,
        "next_direction": next_direction,
        "important_verified_counterexamples": list(important_verified_counterexamples),
        "research_agenda": dict(research_agenda_summary or {}),
        "summary_basis": {
            "derived_theorem_count": derived_theorem_count,
            "open_problem_count": open_problem_count,
            "archived_problem_count": archived_problem_count,
        },
        "desired_summary_changes": list(frontier.get("desired_summary_changes", [])),
        "current_bottlenecks": list(frontier.get("current_bottlenecks", [])),
        "overexplored_patterns": list(frontier.get("overexplored_patterns", [])),
        "missing_bridges": list(frontier.get("missing_bridges", [])),
        "agenda_pressure": list(frontier.get("agenda_pressure", [])),
    }
    if "derived_generation" in existing_payload:
        payload["derived_generation"] = int(existing_payload.get("derived_generation", 0) or 0)
    write_json_atomic(theory_state_path(data_dir), payload)
    return payload


def append_theory_state_history(history_path: Path, *, run_id: str, current_iteration: int, theory_state: dict[str, Any]) -> None:
    append_jsonl(history_path, {"run_id": run_id, "updated_at_iteration": current_iteration, "theory_state": theory_state})


def force_refresh_open_problem_priorities(
    *,
    data_dir: Path,
    worker_settings: Any,
    prioritizer_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
    run_id: str,
    theory_state_history_path: Path | None = None,
) -> tuple[bool, str, dict[str, Any]]:
    open_path = data_dir / "open_problems.jsonl"
    archived_path = data_dir / ARCHIVED_PROBLEMS_FILENAME
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    archived_rows = read_archived_problem_rows(data_dir)
    tracked_rows = [dict(row, queue_status="open", source_kind=str(row.get("source_kind", "open") or "open")) for row in open_rows]
    tracked_rows.extend(dict(row, queue_status="archived", source_kind=str(row.get("source_kind", "archived") or "archived")) for row in archived_rows)
    if not tracked_rows:
        return False, "", {}
    prioritizer_prompt = load_prompt_text(prioritizer_prompt_file)
    guidance = load_current_guidance(data_dir)
    try:
        priority_updates, theory_snapshot, next_direction, theory_frontier, worker_meta = request_open_problem_priorities(
            worker_settings=worker_settings,
            prioritizer_prompt=prioritizer_prompt,
            tracked_rows=tracked_rows,
            derived_entries=derived_entries,
            current_iteration=current_iteration,
            guidance=guidance,
        )
    except (RuntimeError, ValueError) as exc:
        return False, str(exc), {}

    refreshed_open_rows = apply_open_problem_priorities(open_rows, priority_updates)
    refreshed_archived_rows = apply_open_problem_priorities(archived_rows, priority_updates)
    refreshed_open_rows, newly_archived_rows = split_active_and_archived_problem_queues(refreshed_open_rows, failure_archive_threshold=failure_threshold)
    refreshed_archived_rows = merge_archived_problem_rows(refreshed_archived_rows, newly_archived_rows)
    refreshed_open_rows = sort_open_problem_queue(dedupe_problem_rows_by_stmt(refreshed_open_rows), failure_archive_threshold=failure_threshold)
    important_verified_counterexamples = collect_important_verified_counterexamples(data_dir)
    write_jsonl_atomic(open_path, refreshed_open_rows)
    write_jsonl_atomic(archived_path, refreshed_archived_rows)
    theory_state = write_theory_state(
        data_dir,
        run_id=run_id,
        current_iteration=current_iteration,
        derived_theorem_count=len(derived_entries),
        open_problem_count=len(refreshed_open_rows),
        archived_problem_count=len(refreshed_archived_rows),
        theory_snapshot=theory_snapshot,
        next_direction=next_direction,
        important_verified_counterexamples=important_verified_counterexamples,
        research_agenda_summary=summarize_research_agenda_for_state(guidance["research_agenda"]),
        theory_frontier=theory_frontier,
    )
    if theory_state_history_path is not None:
        append_theory_state_history(history_path=theory_state_history_path, run_id=run_id, current_iteration=current_iteration, theory_state=theory_state)
    return True, "", {**dict(worker_meta), "promoted_expand_rows": [], "remaining_expand_rows": []}


def run_batch_generator_subprocess(
    *,
    repo_root: Path,
    theory_file: Path,
    derived_file: Path,
    output_file: Path,
    seed_count: int,
) -> tuple[list[dict[str, Any]], str]:
    script_path = (SCRIPTS_ROOT / "generate_seeds_from_theory.py").resolve()
    cmd = [
        sys.executable,
        str(script_path),
        "--theory-file",
        str(theory_file),
        "--derived-file",
        str(derived_file),
        "--output-file",
        str(output_file),
        "--seed-count",
        str(seed_count),
        "--seed-src",
        "batch_generator",
        "--no-initialize-runtime-state",
        "--repo-root",
        str(repo_root),
    ]
    completed = subprocess.run(cmd, cwd=str(repo_root), capture_output=True, text=True)
    if completed.returncode != 0:
        stderr = (completed.stderr or "").strip()
        stdout = (completed.stdout or "").strip()
        return [], stderr or stdout or f"batch generator exited with code {completed.returncode}"
    return read_jsonl(output_file), ""


def maybe_backfill_open_problems_from_batch_generator(
    *,
    data_dir: Path,
    repo_root: Path,
    theory_file: Path,
    derived_file: Path,
    open_problem_target_min: int,
    seed_count: int,
    reserved_problem_ids: set[str] | None = None,
    phase_logger: Callable[..., None] | None = None,
) -> tuple[list[dict[str, Any]], str]:
    open_path = data_dir / "open_problems.jsonl"
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    reserved_ids = set(reserved_problem_ids or set())
    available_open_rows = [row for row in open_rows if str(row.get("id", "")).strip() and str(row.get("id", "")).strip() not in reserved_ids]
    if open_problem_target_min > 0 and len(available_open_rows) >= open_problem_target_min and any(open_problem_priority_label(row) == "unknown" for row in available_open_rows):
        return [], ""
    if has_available_solver_eligible_problem(open_rows, reserved_problem_ids=reserved_ids):
        return [], ""
    archived_rows = read_archived_problem_rows(data_dir)
    solved_rows = read_jsonl(data_dir / "solved_problems.jsonl")
    counter_rows = read_jsonl(data_dir / "counterexamples.jsonl")
    seen_norms = {
        normalize_stmt_text(str(row.get("stmt", "")))
        for row in (open_rows + archived_rows + solved_rows + counter_rows)
        if str(row.get("stmt", "")).strip()
    }
    all_ids = [str(row.get("id", "")) for row in open_rows + archived_rows + solved_rows + counter_rows]
    if seed_count <= 0:
        return [], ""
    if phase_logger is not None:
        phase_logger(phase="batch_seed_generation", status="begin", requested_seed_count=seed_count, active_open_problem_count=len(open_rows), reserved_problem_count=len(reserved_ids))
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", suffix=".jsonl", prefix="batch_generator_", delete=False, dir=str(data_dir)) as handle:
        output_file = Path(handle.name)
    try:
        generated_rows, error = run_batch_generator_subprocess(repo_root=repo_root, theory_file=theory_file, derived_file=derived_file, output_file=output_file, seed_count=seed_count)
        if error:
            if phase_logger is not None:
                phase_logger(phase="batch_seed_generation", status="error", requested_seed_count=seed_count, error=error)
            return [], error
        added_rows: list[dict[str, Any]] = []
        for row in generated_rows:
            stmt = str(row.get("stmt", "")).strip()
            if not stmt:
                continue
            norm = normalize_stmt_text(stmt)
            if not norm or norm in seen_norms:
                continue
            new_id = next_problem_id(all_ids)
            all_ids.append(new_id)
            seen_norms.add(norm)
            new_row = normalize_open_problem_row(
                {
                    **dict(row),
                    "id": new_id,
                    "src": str(row.get("src", "batch_generator") or "batch_generator").strip() or "batch_generator",
                    "priority": "unknown",
                    "priority_rationale": "",
                    "failure_count": 0,
                }
            )
            open_rows.append(new_row)
            added_rows.append(dict(new_row))
        if added_rows:
            write_jsonl_atomic(open_path, dedupe_problem_rows_by_stmt(open_rows))
        if phase_logger is not None:
            phase_logger(phase="batch_seed_generation", status="result", requested_seed_count=seed_count, generated_count=len(generated_rows), added_count=len(added_rows))
        return added_rows, ""
    finally:
        output_file.unlink(missing_ok=True)


def backfill_open_problems_if_needed(
    *,
    data_dir: Path,
    theory_file: Path,
    derived_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    reserved_problem_ids: set[str] | None = None,
    phase_logger: Callable[..., None] | None = None,
) -> tuple[bool, str, dict[str, Any]]:
    added_rows, batch_error = maybe_backfill_open_problems_from_batch_generator(
        data_dir=data_dir,
        repo_root=repo_root,
        theory_file=theory_file,
        derived_file=derived_file,
        open_problem_target_min=batch_generator_open_target_min,
        seed_count=batch_generator_seed_count,
        reserved_problem_ids=reserved_problem_ids,
        phase_logger=phase_logger,
    )
    return bool(added_rows), batch_error, {"batch_generator_added_problem_rows": added_rows, "batch_generator_error": batch_error}


def refresh_open_problem_state(
    *,
    data_dir: Path,
    prioritize_worker_settings: Any,
    prioritizer_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
    run_id: str,
    theory_state_history_path: Path | None,
    theory_file: Path,
    derived_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    reserved_problem_ids: set[str] | None = None,
    allow_backfill: bool = True,
    phase_logger: Callable[..., None] | None = None,
) -> dict[str, Any]:
    if allow_backfill:
        backfill_ran, backfill_error, backfill_report = backfill_open_problems_if_needed(
            data_dir=data_dir,
            theory_file=theory_file,
            derived_file=derived_file,
            repo_root=repo_root,
            batch_generator_seed_count=batch_generator_seed_count,
            batch_generator_open_target_min=batch_generator_open_target_min,
            reserved_problem_ids=reserved_problem_ids,
            phase_logger=phase_logger,
        )
    else:
        backfill_ran, backfill_error, backfill_report = False, "", {"batch_generator_added_problem_rows": [], "batch_generator_error": ""}
    priority_refresh_ran, priority_refresh_error, priority_refresh_worker_meta = force_refresh_open_problem_priorities(
        data_dir=data_dir,
        worker_settings=prioritize_worker_settings,
        prioritizer_prompt_file=prioritizer_prompt_file,
        derived_entries=derived_entries,
        current_iteration=current_iteration,
        failure_threshold=failure_threshold,
        run_id=run_id,
        theory_state_history_path=theory_state_history_path,
    )
    return {
        "priority_refresh_ran": bool(priority_refresh_ran or backfill_ran),
        "priority_refresh_error": str(backfill_error or priority_refresh_error or ""),
        "priority_refresh_failed": bool(not priority_refresh_ran and bool(priority_refresh_error)),
        "priority_refresh_report": {
            "worker_meta": priority_refresh_worker_meta,
            "batch_generator_added_problem_rows": list(backfill_report.get("batch_generator_added_problem_rows", [])),
            "batch_generator_error": str(backfill_report.get("batch_generator_error", "") or backfill_error or ""),
        },
    }


def store_expand_candidates_and_refresh(
    *,
    data_dir: Path,
    statements_with_rationale: list[dict[str, str]],
    source: str,
    source_problem_id: str,
    source_kind: str,
    prioritize_worker_settings: Any,
    prioritizer_prompt_file: str,
    derived_entries: list[dict[str, str]],
    current_iteration: int,
    failure_threshold: int,
    run_id: str,
    theory_state_history_path: Path,
    theory_file: Path,
    derived_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    allow_backfill: bool = True,
    phase_logger: Callable[..., None] | None = None,
) -> dict[str, Any]:
    stored_expand_rows = append_expand_candidates(
        data_dir=data_dir,
        statements_with_rationale=statements_with_rationale,
        source=source,
        source_problem_id=source_problem_id,
        source_kind=source_kind,
    )
    refresh_result = refresh_open_problem_state(
        data_dir=data_dir,
        prioritize_worker_settings=prioritize_worker_settings,
        prioritizer_prompt_file=prioritizer_prompt_file,
        derived_entries=derived_entries,
        current_iteration=current_iteration,
        failure_threshold=failure_threshold,
        run_id=run_id,
        theory_state_history_path=theory_state_history_path,
        theory_file=theory_file,
        derived_file=derived_file,
        repo_root=repo_root,
        batch_generator_seed_count=batch_generator_seed_count,
        batch_generator_open_target_min=batch_generator_open_target_min,
        allow_backfill=allow_backfill,
        phase_logger=phase_logger,
    )
    refresh_result["stored_expand_rows"] = stored_expand_rows
    return refresh_result
