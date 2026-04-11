from __future__ import annotations

import sys
import threading
import time
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
SCRIPTS_ROOT = SCRIPT_DIR.parent
LOOP_ROOT = SCRIPTS_ROOT / "loop"
for search_path in (SCRIPTS_ROOT, LOOP_ROOT):
    search_path_str = str(search_path)
    if search_path_str not in sys.path:
        sys.path.insert(0, search_path_str)

from common import append_jsonl
from common import normalize_open_problem_row
from common import read_archived_problem_rows
from common import read_jsonl
from formalization_runtime import attempt_formalization_until_timeout
from generated_library import render_scratch_template
from guidance import unpack_guidance_context
from loop_common import iso_timestamp_now
from loop_common import monotonic_duration_ms
from loop_helpers import append_derived_entry_cache
from loop_helpers import append_phase_attempt_record
from loop_helpers import build_problem_theory_context
from loop_helpers import emit_phase_log
from loop_helpers import extract_theorem_code_from_scratch
from loop_helpers import is_verified_resolution
from loop_helpers import load_current_guidance
from loop_helpers import load_formalization_memory
from loop_helpers import load_theory_state
from loop_helpers import open_problem_priority_label
from loop_helpers import shortlist_relevant_derived_entries
from loop_helpers import validate_theorem_name_stem
from problem_expansion import request_expand_candidates
from problem_expansion import store_expand_candidates_and_refresh
from prompt_loader import load_prompt_file
from theorem_commit import commit_verified_theorem_and_generation
from theorem_reuse_memory import append_theorem_reuse_memory_entry
from worker_client import invoke_worker_json


SCRATCH_TEMPLATE = render_scratch_template(include_generated_manifest=False)
MAX_EXPAND_CANDIDATES_PER_MAIN_THEOREM = 5
MAIN_THEOREM_CANDIDATE_COUNT = 3
MAIN_THEOREM_PATTERNS = {"new_theorem", "structure_discovery", "framework_introduction"}


def load_prompt_text(prompt_file: str) -> str:
    return load_prompt_file(Path(prompt_file))


def _build_main_theorem_followup_candidates(
    *,
    theorem_name: str,
    statement: str,
    rationale: str,
    verify_error_excerpt: str,
    missing_lemmas: list[str],
    intermediate_lemmas: list[str],
) -> list[dict[str, str]]:
    candidates: list[dict[str, str]] = []
    seen_stmt_norms: set[str] = set()

    def add_candidate(raw_statement: str, raw_rationale: str) -> None:
        stmt = str(raw_statement).strip()
        if not stmt:
            return
        norm = " ".join(stmt.split()).lower()
        if not norm or norm in seen_stmt_norms:
            return
        seen_stmt_norms.add(norm)
        candidates.append(
            {
                "statement": stmt,
                "rationale": str(raw_rationale).strip(),
            }
        )

    if statement.strip():
        add_candidate(
            statement,
            verify_error_excerpt.strip()
            or rationale.strip()
            or f"Main theorem candidate `{theorem_name}` remained unresolved.",
        )
    for item in missing_lemmas:
        add_candidate(item, f"Missing lemma needed for `{theorem_name}`.")
    for item in intermediate_lemmas:
        add_candidate(item, f"Intermediate lemma suggested while proving `{theorem_name}`.")
    return candidates


def _summarize_main_theorem_candidates(candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "candidate_rank_seed": int(candidate["candidate_rank_seed"]),
            "theorem_name_stem": str(candidate["theorem_name_stem"]),
            "statement": str(candidate["statement"]),
            "theorem_pattern": str(candidate["theorem_pattern"]),
        }
        for candidate in candidates
    ]


def _summarize_main_theorem_ranking(
    ranking: list[dict[str, Any]],
    candidate_lookup: dict[int, dict[str, Any]],
) -> list[dict[str, Any]]:
    ranking_summary: list[dict[str, Any]] = []
    for entry in ranking:
        candidate_rank_seed = int(entry["candidate_rank_seed"])
        candidate = candidate_lookup[candidate_rank_seed]
        ranking_summary.append(
            {
                "rank": int(entry["rank"]),
                "candidate_rank_seed": candidate_rank_seed,
                "decision": str(entry["decision"]),
                "theorem_name_stem": str(candidate["theorem_name_stem"]),
                "statement": str(candidate["statement"]),
                "reason": str(entry["reason"]),
            }
        )
    return ranking_summary


def _append_main_theorem_session_event(
    session_events_path: Path | None,
    *,
    event: str,
    run_id: str,
    iteration: int,
    candidate_set_id: str,
    payload: dict[str, Any],
) -> None:
    if session_events_path is None:
        return
    append_jsonl(
        session_events_path,
        {
            "event": event,
            "run_id": run_id,
            "iteration": iteration,
            "candidate_set_id": candidate_set_id,
            "recorded_at": iso_timestamp_now(),
            **payload,
        },
    )


def _store_main_theorem_followups(
    *,
    data_dir: Path,
    theorem_name: str,
    statement: str,
    rationale: str,
    verify_error_excerpt: str,
    missing_lemmas: list[str],
    intermediate_lemmas: list[str],
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
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
) -> dict[str, Any]:
    followup_candidates = _build_main_theorem_followup_candidates(
        theorem_name=theorem_name,
        statement=statement,
        rationale=rationale,
        verify_error_excerpt=verify_error_excerpt,
        missing_lemmas=missing_lemmas,
        intermediate_lemmas=intermediate_lemmas,
    )
    if not followup_candidates:
        return {
            "followup_candidates": [],
            "stored_expand_rows": [],
            "priority_refresh_ran": False,
            "priority_refresh_error": "",
            "priority_refresh_report": {},
        }
    refresh_outcome = store_expand_candidates_and_refresh(
        data_dir=data_dir,
        statements_with_rationale=followup_candidates,
        source="main_theorem_followup",
        source_problem_id=theorem_name,
        source_kind="main_theorem",
        prioritize_worker_settings=prioritize_open_problems_worker_settings,
        prioritizer_prompt_file=prioritize_open_problems_prompt_file,
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
        allow_backfill=False,
    )
    refresh_outcome["followup_candidates"] = followup_candidates
    return refresh_outcome


def _build_main_theorem_tracked_problem_payload(
    tracked_rows: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[str]]:
    visible_tracked_rows = tracked_rows[:40]
    payload_rows = [
        {
            "problem_id": str(row.get("id", "")),
            "stmt": str(row.get("stmt", "")),
            "priority": open_problem_priority_label(row),
            "queue_status": str(row.get("queue_status", "open")),
            "source_kind": str(row.get("source_kind", row.get("queue_status", "open"))),
            "failure_count": int(row.get("failure_count", 0) or 0),
            "mode": str(row.get("mode", "")),
            "summary_delta": str(row.get("summary_delta", "")),
        }
        for row in visible_tracked_rows
    ]
    known_problem_ids = [str(row.get("problem_id", "")).strip() for row in payload_rows if str(row.get("problem_id", "")).strip()]
    return payload_rows, known_problem_ids


def _validate_main_theorem_candidate(
    raw_candidate: dict[str, Any],
    *,
    known_problem_id_set: set[str],
    candidate_index: int,
) -> dict[str, Any]:
    required_keys = {
        "candidate_rank_seed",
        "statement",
        "theorem_name_stem",
        "docstring_summary",
        "rationale",
        "supporting_theorems",
        "missing_lemmas",
        "source_problem_ids",
        "theorem_pattern",
        "context_note",
        "conceptual_depth_note",
    }
    if set(raw_candidate.keys()) != required_keys:
        raise ValueError(f"main_theorem candidate {candidate_index} keys mismatch required contract")

    candidate_rank_seed = raw_candidate.get("candidate_rank_seed")
    if not isinstance(candidate_rank_seed, int):
        raise ValueError(f"main_theorem candidate {candidate_index} candidate_rank_seed must be an integer")

    statement = str(raw_candidate.get("statement", "")).strip()
    theorem_name_stem = validate_theorem_name_stem(str(raw_candidate.get("theorem_name_stem", "")).strip())
    docstring_summary = str(raw_candidate.get("docstring_summary", "")).strip()
    rationale = str(raw_candidate.get("rationale", "")).strip()
    theorem_pattern = str(raw_candidate.get("theorem_pattern", "")).strip()
    context_note = str(raw_candidate.get("context_note", "")).strip()
    conceptual_depth_note = str(raw_candidate.get("conceptual_depth_note", "")).strip()
    supporting_value = raw_candidate.get("supporting_theorems", [])
    missing_value = raw_candidate.get("missing_lemmas", [])
    source_problem_ids_value = raw_candidate.get("source_problem_ids", [])
    if not isinstance(supporting_value, list) or not isinstance(missing_value, list) or not isinstance(source_problem_ids_value, list):
        raise ValueError(
            f"main_theorem candidate {candidate_index} supporting_theorems, missing_lemmas, and source_problem_ids must be arrays"
        )

    supporting_theorems = [str(item).strip() for item in supporting_value if str(item).strip()]
    missing_lemmas = [str(item).strip() for item in missing_value if str(item).strip()]
    source_problem_ids: list[str] = []
    seen_source_ids: set[str] = set()
    for item in source_problem_ids_value:
        problem_id = str(item).strip()
        if not problem_id or problem_id in seen_source_ids:
            continue
        if known_problem_id_set and problem_id not in known_problem_id_set:
            raise ValueError(f"main_theorem candidate {candidate_index} source_problem_id is not in tracked_problems: {problem_id}")
        seen_source_ids.add(problem_id)
        source_problem_ids.append(problem_id)

    if not statement:
        raise ValueError(f"main_theorem candidate {candidate_index} statement must be non-empty")
    if not docstring_summary:
        raise ValueError(f"main_theorem candidate {candidate_index} docstring_summary must be non-empty")
    if not rationale:
        raise ValueError(f"main_theorem candidate {candidate_index} rationale must be non-empty")
    if known_problem_id_set and not source_problem_ids:
        raise ValueError(f"main_theorem candidate {candidate_index} source_problem_ids must be non-empty")
    if theorem_pattern not in MAIN_THEOREM_PATTERNS:
        raise ValueError(
            "main_theorem candidate theorem_pattern must be new_theorem|structure_discovery|framework_introduction"
        )
    if not context_note:
        raise ValueError(f"main_theorem candidate {candidate_index} context_note must be non-empty")
    if not conceptual_depth_note:
        raise ValueError(f"main_theorem candidate {candidate_index} conceptual_depth_note must be non-empty")

    return {
        "candidate_rank_seed": candidate_rank_seed,
        "statement": statement,
        "theorem_name_stem": theorem_name_stem,
        "docstring_summary": docstring_summary,
        "rationale": rationale,
        "supporting_theorems": supporting_theorems,
        "missing_lemmas": missing_lemmas,
        "source_problem_ids": source_problem_ids,
        "theorem_pattern": theorem_pattern,
        "context_note": context_note,
        "conceptual_depth_note": conceptual_depth_note,
    }


def validate_main_theorem_candidate_set_output(
    payload: dict[str, Any],
    expected_candidate_set_id: str,
    known_problem_ids: list[str],
) -> list[dict[str, Any]]:
    required_keys = {"candidate_set_id", "candidates"}
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_generate output keys mismatch required contract")

    candidate_set_id = str(payload.get("candidate_set_id", "")).strip()
    if candidate_set_id != expected_candidate_set_id:
        raise ValueError("main_theorem_generate candidate_set_id does not match request")

    raw_candidates = payload.get("candidates", [])
    if not isinstance(raw_candidates, list):
        raise ValueError("main_theorem_generate candidates must be an array")
    if len(raw_candidates) != MAIN_THEOREM_CANDIDATE_COUNT:
        raise ValueError(f"main_theorem_generate must return exactly {MAIN_THEOREM_CANDIDATE_COUNT} candidates")

    known_problem_id_set = {str(item).strip() for item in known_problem_ids if str(item).strip()}
    normalized_candidates: list[dict[str, Any]] = []
    seen_rank_seeds: set[int] = set()
    seen_statement_norms: set[str] = set()
    seen_theorem_name_stems: set[str] = set()
    theorem_patterns: set[str] = set()
    for candidate_index, item in enumerate(raw_candidates, start=1):
        if not isinstance(item, dict):
            raise ValueError("main_theorem_generate candidates must contain only objects")
        candidate = _validate_main_theorem_candidate(
            item,
            known_problem_id_set=known_problem_id_set,
            candidate_index=candidate_index,
        )
        candidate_rank_seed = int(candidate["candidate_rank_seed"])
        if candidate_rank_seed < 1 or candidate_rank_seed > MAIN_THEOREM_CANDIDATE_COUNT:
            raise ValueError("main_theorem_generate candidate_rank_seed must be within the fixed candidate set")
        if candidate_rank_seed in seen_rank_seeds:
            raise ValueError("main_theorem_generate candidate_rank_seed values must be unique")
        seen_rank_seeds.add(candidate_rank_seed)

        statement_norm = " ".join(str(candidate["statement"]).split()).lower()
        if statement_norm in seen_statement_norms:
            raise ValueError("main_theorem_generate candidate statements must be distinct")
        seen_statement_norms.add(statement_norm)

        theorem_name_stem = str(candidate["theorem_name_stem"])
        if theorem_name_stem in seen_theorem_name_stems:
            raise ValueError("main_theorem_generate theorem_name_stem values must be unique")
        seen_theorem_name_stems.add(theorem_name_stem)

        theorem_patterns.add(str(candidate["theorem_pattern"]))
        normalized_candidates.append(candidate)

    if seen_rank_seeds != set(range(1, MAIN_THEOREM_CANDIDATE_COUNT + 1)):
        raise ValueError("main_theorem_generate candidate_rank_seed values must cover the fixed candidate set")
    if len(theorem_patterns) < 2:
        raise ValueError("main_theorem_generate candidate set must contain at least two distinct theorem patterns")

    return sorted(normalized_candidates, key=lambda item: int(item["candidate_rank_seed"]))


def validate_main_theorem_selection_output(
    payload: dict[str, Any],
    *,
    expected_candidate_set_id: str,
    candidates: list[dict[str, Any]],
) -> tuple[int, str, list[dict[str, Any]]]:
    required_keys = {"candidate_set_id", "selected_candidate_rank_seed", "selection_summary", "ranking"}
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_select output keys mismatch required contract")

    candidate_set_id = str(payload.get("candidate_set_id", "")).strip()
    if candidate_set_id != expected_candidate_set_id:
        raise ValueError("main_theorem_select candidate_set_id does not match request")

    selected_candidate_rank_seed = payload.get("selected_candidate_rank_seed")
    if not isinstance(selected_candidate_rank_seed, int):
        raise ValueError("main_theorem_select selected_candidate_rank_seed must be an integer")

    selection_summary = str(payload.get("selection_summary", "")).strip()
    if not selection_summary:
        raise ValueError("main_theorem_select selection_summary must be non-empty")

    ranking_value = payload.get("ranking", [])
    if not isinstance(ranking_value, list):
        raise ValueError("main_theorem_select ranking must be an array")
    if len(ranking_value) != len(candidates):
        raise ValueError("main_theorem_select ranking length must match candidate count")

    candidate_rank_seed_set = {int(candidate["candidate_rank_seed"]) for candidate in candidates}
    normalized_ranking: list[dict[str, Any]] = []
    seen_candidate_rank_seeds: set[int] = set()
    seen_ranks: set[int] = set()
    selected_entries = 0
    for item in ranking_value:
        if not isinstance(item, dict):
            raise ValueError("main_theorem_select ranking entries must be objects")
        if set(item.keys()) != {"candidate_rank_seed", "rank", "decision", "reason"}:
            raise ValueError("main_theorem_select ranking entry keys mismatch required contract")

        candidate_rank_seed = item.get("candidate_rank_seed")
        rank = item.get("rank")
        if not isinstance(candidate_rank_seed, int) or not isinstance(rank, int):
            raise ValueError("main_theorem_select ranking candidate_rank_seed and rank must be integers")
        decision = str(item.get("decision", "")).strip()
        reason = str(item.get("reason", "")).strip()
        if candidate_rank_seed not in candidate_rank_seed_set:
            raise ValueError("main_theorem_select ranking candidate_rank_seed must refer to an input candidate")
        if candidate_rank_seed in seen_candidate_rank_seeds:
            raise ValueError("main_theorem_select ranking candidate_rank_seed values must be unique")
        if rank < 1 or rank > len(candidates):
            raise ValueError("main_theorem_select ranking rank is out of bounds")
        if rank in seen_ranks:
            raise ValueError("main_theorem_select ranking rank values must be unique")
        if decision not in {"select", "reject"}:
            raise ValueError("main_theorem_select decision must be select or reject")
        if not reason:
            raise ValueError("main_theorem_select reason must be non-empty")
        if decision == "select":
            selected_entries += 1

        seen_candidate_rank_seeds.add(candidate_rank_seed)
        seen_ranks.add(rank)
        normalized_ranking.append(
            {
                "candidate_rank_seed": candidate_rank_seed,
                "rank": rank,
                "decision": decision,
                "reason": reason,
            }
        )

    if seen_candidate_rank_seeds != candidate_rank_seed_set:
        raise ValueError("main_theorem_select ranking must cover each input candidate exactly once")
    if seen_ranks != set(range(1, len(candidates) + 1)):
        raise ValueError("main_theorem_select ranking must cover every rank exactly once")
    if selected_entries != 1:
        raise ValueError("main_theorem_select must mark exactly one candidate as select")
    if selected_candidate_rank_seed not in candidate_rank_seed_set:
        raise ValueError("main_theorem_select selected_candidate_rank_seed must refer to an input candidate")

    ranking_by_rank = {int(item["rank"]): item for item in normalized_ranking}
    top_entry = ranking_by_rank[1]
    if int(top_entry["candidate_rank_seed"]) != selected_candidate_rank_seed or str(top_entry["decision"]) != "select":
        raise ValueError("main_theorem_select rank 1 must be the selected candidate")
    for rank in range(2, len(candidates) + 1):
        if str(ranking_by_rank[rank]["decision"]) != "reject":
            raise ValueError("main_theorem_select ranks below 1 must be rejected")

    return selected_candidate_rank_seed, selection_summary, sorted(normalized_ranking, key=lambda item: int(item["rank"]))


def request_main_theorem_candidate_set(
    *,
    worker_settings: Any,
    generator_prompt: str,
    candidate_set_id: str,
    derived_entries: list[dict[str, str]],
    theory_context: str,
    tracked_rows: list[dict[str, Any]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    tracked_problem_payload, known_problem_ids = _build_main_theorem_tracked_problem_payload(tracked_rows)
    theory_state, research_agenda = unpack_guidance_context(guidance)
    payload: dict[str, Any] = {
        "candidate_set_id": candidate_set_id,
        "candidate_count": MAIN_THEOREM_CANDIDATE_COUNT,
        "current_iteration": current_iteration,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "tracked_problems": tracked_problem_payload,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_generate",
        system_prompt=generator_prompt,
        payload=payload,
        metadata={"candidate_set_id": candidate_set_id, "derived_theorem_count": len(derived_entries)},
    )
    return validate_main_theorem_candidate_set_output(response, candidate_set_id, known_problem_ids), worker_meta


def request_main_theorem_selection(
    *,
    worker_settings: Any,
    selector_prompt: str,
    candidate_set_id: str,
    candidates: list[dict[str, Any]],
    derived_entries: list[dict[str, str]],
    theory_context: str,
    tracked_rows: list[dict[str, Any]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[tuple[int, str, list[dict[str, Any]]], dict[str, Any]]:
    tracked_problem_payload, _ = _build_main_theorem_tracked_problem_payload(tracked_rows)
    theory_state, research_agenda = unpack_guidance_context(guidance)
    payload: dict[str, Any] = {
        "candidate_set_id": candidate_set_id,
        "current_iteration": current_iteration,
        "candidates": candidates,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "tracked_problems": tracked_problem_payload,
        "theory_state": theory_state,
        "research_agenda": research_agenda,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_select",
        system_prompt=selector_prompt,
        payload=payload,
        metadata={"candidate_set_id": candidate_set_id, "candidate_count": len(candidates)},
    )
    return (
        validate_main_theorem_selection_output(
            response,
            expected_candidate_set_id=candidate_set_id,
            candidates=candidates,
        ),
        worker_meta,
    )


def run_main_theorem_session(
    *,
    worker_settings: Any,
    scratch_file: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    data_dir: Path,
    base_theory_context: str,
    formalization_memory_path: Path,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    formalizer_prompt_file: str,
    repair_prompt_file: str,
    generate_prompt_file: str,
    select_prompt_file: str,
    post_expand_prompt_file: str,
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
    theory_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    current_iteration: int,
    skip_verify: bool,
    verify_timeout_sec: int | None,
    formalization_retry_budget_sec: int | None,
    max_same_error_streak: int,
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    session_events_path: Path | None,
    compile_metrics: dict[str, Any],
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
) -> dict[str, Any]:
    generate_prompt = load_prompt_text(generate_prompt_file)
    select_prompt = load_prompt_text(select_prompt_file)
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")]
    archived_rows = read_archived_problem_rows(data_dir)
    tracked_rows = [dict(row, queue_status="open") for row in open_rows]
    tracked_rows.extend(dict(row, queue_status="archived") for row in archived_rows)
    candidate_set_id = "mt_main_theorem"
    guidance = load_current_guidance(data_dir)
    emit_phase_log(
        phase_logs,
        "main_theorem_generate",
        iteration=current_iteration,
        candidate_set_id=candidate_set_id,
        derived_theorem_count=len(derived_entries),
        open_problem_count=len(open_rows),
        tracked_problem_count=len(tracked_rows),
        candidate_count=MAIN_THEOREM_CANDIDATE_COUNT,
    )
    generate_started_monotonic = time.monotonic()
    generate_started_at = iso_timestamp_now()
    try:
        candidates, _ = request_main_theorem_candidate_set(
            worker_settings=worker_settings,
            generator_prompt=generate_prompt,
            candidate_set_id=candidate_set_id,
            derived_entries=derived_entries,
            theory_context=base_theory_context,
            tracked_rows=tracked_rows,
            current_iteration=current_iteration,
            guidance=guidance,
        )
    except (RuntimeError, ValueError) as exc:
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_set_id,
            phase="main_theorem_generate",
            worker_task="main_theorem_generate",
            started_at=generate_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(generate_started_monotonic),
            success=False,
            result="error",
            error=str(exc),
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_generate_result",
            iteration=current_iteration,
            candidate_set_id=candidate_set_id,
            status="error",
            error=str(exc),
        )
        _append_main_theorem_session_event(
            session_events_path,
            event="main_theorem_generate_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=candidate_set_id,
            payload={"status": "error", "error": str(exc)},
        )
        return {
            "status": "main_theorem_generate_error",
            "processed": False,
            "verify_success": False,
            "error": str(exc),
        }
    append_phase_attempt_record(
        phase_attempts_path,
        run_id=run_id,
        session_type="main_theorem_session",
        iteration=current_iteration,
        entity_id=candidate_set_id,
        phase="main_theorem_generate",
        worker_task="main_theorem_generate",
        started_at=generate_started_at,
        finished_at=iso_timestamp_now(),
        duration_ms=monotonic_duration_ms(generate_started_monotonic),
        success=True,
        result="ok",
    )
    emit_phase_log(
        phase_logs,
        "main_theorem_generate_result",
        iteration=current_iteration,
        candidate_set_id=candidate_set_id,
        status="ok",
        candidate_count=len(candidates),
        candidates=_summarize_main_theorem_candidates(candidates),
    )
    _append_main_theorem_session_event(
        session_events_path,
        event="main_theorem_generate_result",
        run_id=run_id,
        iteration=current_iteration,
        candidate_set_id=candidate_set_id,
        payload={
            "status": "ok",
            "candidate_count": len(candidates),
            "candidates": _summarize_main_theorem_candidates(candidates),
        },
    )

    emit_phase_log(
        phase_logs,
        "main_theorem_select",
        iteration=current_iteration,
        candidate_set_id=candidate_set_id,
        candidate_count=len(candidates),
    )
    select_started_monotonic = time.monotonic()
    select_started_at = iso_timestamp_now()
    try:
        (selected_candidate_rank_seed, selection_summary, ranking), _ = request_main_theorem_selection(
            worker_settings=worker_settings,
            selector_prompt=select_prompt,
            candidate_set_id=candidate_set_id,
            candidates=candidates,
            derived_entries=derived_entries,
            theory_context=base_theory_context,
            tracked_rows=tracked_rows,
            current_iteration=current_iteration,
            guidance=guidance,
        )
    except (RuntimeError, ValueError) as exc:
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_set_id,
            phase="main_theorem_select",
            worker_task="main_theorem_select",
            started_at=select_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(select_started_monotonic),
            success=False,
            result="error",
            error=str(exc),
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_select_result",
            iteration=current_iteration,
            candidate_set_id=candidate_set_id,
            status="error",
            error=str(exc),
        )
        _append_main_theorem_session_event(
            session_events_path,
            event="main_theorem_select_result",
            run_id=run_id,
            iteration=current_iteration,
            candidate_set_id=candidate_set_id,
            payload={"status": "error", "error": str(exc)},
        )
        return {
            "status": "main_theorem_select_error",
            "processed": False,
            "verify_success": False,
            "error": str(exc),
            "generated_candidates": candidates,
        }
    append_phase_attempt_record(
        phase_attempts_path,
        run_id=run_id,
        session_type="main_theorem_session",
        iteration=current_iteration,
        entity_id=candidate_set_id,
        phase="main_theorem_select",
        worker_task="main_theorem_select",
        started_at=select_started_at,
        finished_at=iso_timestamp_now(),
        duration_ms=monotonic_duration_ms(select_started_monotonic),
        success=True,
        result="ok",
    )
    candidate_lookup = {int(candidate["candidate_rank_seed"]): candidate for candidate in candidates}
    selected_candidate = candidate_lookup[selected_candidate_rank_seed]
    emit_phase_log(
        phase_logs,
        "main_theorem_select_result",
        iteration=current_iteration,
        candidate_set_id=candidate_set_id,
        status="ok",
        selected_candidate_rank_seed=selected_candidate_rank_seed,
        selection_summary=selection_summary,
        selected_candidate={
            "candidate_rank_seed": int(selected_candidate["candidate_rank_seed"]),
            "theorem_name_stem": str(selected_candidate["theorem_name_stem"]),
            "statement": str(selected_candidate["statement"]),
            "theorem_pattern": str(selected_candidate["theorem_pattern"]),
        },
        ranking=_summarize_main_theorem_ranking(ranking, candidate_lookup),
    )
    _append_main_theorem_session_event(
        session_events_path,
        event="main_theorem_select_result",
        run_id=run_id,
        iteration=current_iteration,
        candidate_set_id=candidate_set_id,
        payload={
            "status": "ok",
            "selected_candidate_rank_seed": selected_candidate_rank_seed,
            "selection_summary": selection_summary,
            "selected_candidate": {
                "candidate_rank_seed": int(selected_candidate["candidate_rank_seed"]),
                "theorem_name_stem": str(selected_candidate["theorem_name_stem"]),
                "statement": str(selected_candidate["statement"]),
                "theorem_pattern": str(selected_candidate["theorem_pattern"]),
            },
            "ranking": _summarize_main_theorem_ranking(ranking, candidate_lookup),
        },
    )

    report = process_main_theorem(
        candidate_id=candidate_set_id,
        statement=str(selected_candidate["statement"]),
        theorem_name=f"main_thm_{selected_candidate['theorem_name_stem']}",
        docstring_summary=str(selected_candidate["docstring_summary"]),
        rationale=str(selected_candidate["rationale"]),
        supporting_theorems=list(selected_candidate["supporting_theorems"]),
        missing_lemmas=list(selected_candidate["missing_lemmas"]),
        scratch_file=scratch_file,
        derived_file=derived_file,
        derived_entries=derived_entries,
        data_dir=data_dir,
        base_theory_context=base_theory_context,
        formalization_memory_path=formalization_memory_path,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        worker_settings=worker_settings,
        formalizer_prompt_file=formalizer_prompt_file,
        repair_prompt_file=repair_prompt_file,
        post_expand_prompt_file=post_expand_prompt_file,
        prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
        prioritize_open_problems_prompt_file=prioritize_open_problems_prompt_file,
        theory_file=theory_file,
        repo_root=repo_root,
        batch_generator_seed_count=batch_generator_seed_count,
        batch_generator_open_target_min=batch_generator_open_target_min,
        current_iteration=current_iteration,
        skip_verify=skip_verify,
        verify_timeout_sec=verify_timeout_sec,
        formalization_retry_budget_sec=formalization_retry_budget_sec,
        max_same_error_streak=max_same_error_streak,
        failure_threshold=failure_threshold,
        phase_logs=phase_logs,
        run_id=run_id,
        phase_attempts_path=phase_attempts_path,
        theory_state_history_path=(
            (phase_attempts_path.parent if phase_attempts_path is not None else data_dir)
            / "theory_state_history.jsonl"
        ),
        compile_metrics=compile_metrics,
        state_lock=state_lock,
        derived_runtime_state=derived_runtime_state,
    )
    report["generated_candidates"] = candidates
    report["selected_candidate_rank_seed"] = selected_candidate_rank_seed
    report["selection_summary"] = selection_summary
    report["ranking"] = ranking
    report["suggested_statement"] = str(selected_candidate["statement"])
    report["suggested_rationale"] = str(selected_candidate["rationale"])
    report["source_problem_ids"] = list(selected_candidate["source_problem_ids"])
    if session_events_path is not None:
        report["session_events_file"] = str(session_events_path)
    return report


def process_main_theorem(
    *,
    candidate_id: str,
    statement: str,
    theorem_name: str,
    docstring_summary: str,
    rationale: str,
    supporting_theorems: list[str],
    missing_lemmas: list[str],
    scratch_file: Path,
    derived_file: Path,
    derived_entries: list[dict[str, str]],
    data_dir: Path,
    base_theory_context: str,
    formalization_memory_path: Path,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    worker_settings: Any,
    formalizer_prompt_file: str,
    repair_prompt_file: str,
    post_expand_prompt_file: str,
    prioritize_open_problems_worker_settings: Any,
    prioritize_open_problems_prompt_file: str,
    theory_file: Path,
    repo_root: Path,
    batch_generator_seed_count: int,
    batch_generator_open_target_min: int,
    current_iteration: int,
    skip_verify: bool,
    verify_timeout_sec: int | None,
    formalization_retry_budget_sec: int | None,
    max_same_error_streak: int,
    failure_threshold: int,
    phase_logs: bool,
    run_id: str,
    phase_attempts_path: Path | None,
    theory_state_history_path: Path,
    compile_metrics: dict[str, Any],
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
) -> dict[str, Any]:
    statement = statement.strip()
    theorem_name = theorem_name.strip()
    if not statement or not theorem_name:
        return {
            "processed": False,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": False,
        }

    scratch_file.parent.mkdir(parents=True, exist_ok=True)
    scratch_file.write_text(SCRATCH_TEMPLATE, encoding="utf-8")

    theorem_context = build_problem_theory_context(base_theory_context, derived_entries, statement)
    current_iteration_full_logs: list[dict[str, Any]] = []
    intermediate_lemmas: list[str] = []
    proof_sketch = rationale.strip() or f"Prove {theorem_name} from the current Derived.lean cluster."

    proof_formalizer_prompt = load_prompt_text(formalizer_prompt_file)
    proof_repair_prompt = load_prompt_text(repair_prompt_file)
    verify_success, _, result, _, _, _, verify_error_excerpt, final_stmt = attempt_formalization_until_timeout(
        problem_id=candidate_id,
        theorem_name=theorem_name,
        stmt=statement,
        result="proof",
        proof_sketch=proof_sketch,
        counterexample_text="",
        scratch_file=scratch_file,
        skip_verify=skip_verify,
        formalize_worker_settings=formalize_worker_settings,
        repair_worker_settings=repair_worker_settings,
        formalizer_prompts={"proof": proof_formalizer_prompt, "counterexample": proof_formalizer_prompt},
        repair_prompts={"proof": proof_repair_prompt, "counterexample": proof_repair_prompt},
        open_rows=[normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")],
        theory_context=theorem_context,
        verify_timeout_sec=verify_timeout_sec,
        formalization_retry_budget_sec=formalization_retry_budget_sec,
        memory_path=formalization_memory_path,
        current_iteration_full_logs=current_iteration_full_logs,
        initial_proof_text="",
        phase_logger=(lambda **fields: emit_phase_log(phase_logs, iteration=current_iteration, **fields)),
        forbid_sorry=True,
        max_same_error_streak=max_same_error_streak,
        retry_initial_formalization_until_budget=True,
        run_id=run_id,
        session_type="main_theorem_session",
        iteration=current_iteration,
        phase_attempts_path=phase_attempts_path,
        compile_metrics=compile_metrics,
    )
    emit_phase_log(
        phase_logs,
        "main_theorem_formalization_result",
        iteration=current_iteration,
        candidate_id=candidate_id,
        theorem_name=theorem_name,
        result=result,
        verify_success=verify_success,
        error_excerpt=verify_error_excerpt,
    )

    if not is_verified_resolution(verify_success=verify_success, result=result):
        followup_refresh = _store_main_theorem_followups(
            data_dir=data_dir,
            theorem_name=theorem_name,
            statement=final_stmt.strip() or statement,
            rationale=rationale,
            verify_error_excerpt=verify_error_excerpt,
            missing_lemmas=missing_lemmas,
            intermediate_lemmas=intermediate_lemmas,
            prioritize_open_problems_worker_settings=prioritize_open_problems_worker_settings,
            prioritize_open_problems_prompt_file=prioritize_open_problems_prompt_file,
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
        )
        return {
            "processed": True,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": False,
            "verify_error_excerpt": verify_error_excerpt,
            "followup_candidates": list(followup_refresh.get("followup_candidates", [])),
            "stored_expand_rows": list(followup_refresh.get("stored_expand_rows", [])),
            "priority_refresh_ran": bool(followup_refresh.get("priority_refresh_ran", False)),
            "priority_refresh_error": str(followup_refresh.get("priority_refresh_error", "")),
        }

    theorem_code = extract_theorem_code_from_scratch(scratch_file)
    derived_entries_for_context = [dict(entry) for entry in derived_entries]
    if theorem_code:
        append_derived_entry_cache(derived_entries_for_context, theorem_code)
    emit_phase_log(
        phase_logs,
        "main_theorem_append_derived",
        iteration=current_iteration,
        candidate_id=candidate_id,
        theorem_name=theorem_name,
        appended=bool(theorem_code),
    )
    known_theorem_names = {
        str(entry.get("name", "")).strip()
        for entry in derived_entries_for_context
        if str(entry.get("name", "")).strip()
    }

    post_expand_candidates: list[dict[str, str]] = []
    post_expand_error = ""
    theorem_context = build_problem_theory_context(base_theory_context, derived_entries_for_context, final_stmt)
    if theorem_code:
        emit_phase_log(
            phase_logs,
            "post_theorem_expand",
            iteration=current_iteration,
            candidate_id=candidate_id,
            theorem_name=theorem_name,
        )
        post_expand_started_monotonic = time.monotonic()
        post_expand_started_at = iso_timestamp_now()
        try:
            post_expand_candidates, _ = request_expand_candidates(
                worker_settings=worker_settings,
                expand_prompt=load_prompt_text(post_expand_prompt_file),
                task_type="post_theorem_expand",
                problem_id=candidate_id,
                stmt=final_stmt,
                original_stmt=statement,
                result=result,
                verify_success=verify_success,
                theory_context=theorem_context,
                open_rows=[normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")],
                existing_new_problems=[],
                verify_error_excerpt="",
                current_iteration_full_logs=current_iteration_full_logs,
                same_problem_history_tail=load_formalization_memory(formalization_memory_path, candidate_id)[-8:],
                theory_state=load_theory_state(data_dir),
                max_candidates=MAX_EXPAND_CANDIDATES_PER_MAIN_THEOREM,
            )
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="post_theorem_expand",
                worker_task="post_theorem_expand",
                started_at=post_expand_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(post_expand_started_monotonic),
                success=True,
                result="ok",
            )
            emit_phase_log(
                phase_logs,
                "post_theorem_expand_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                generated_problem_count=len(post_expand_candidates),
            )
        except (RuntimeError, ValueError) as exc:
            post_expand_error = str(exc)
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type="main_theorem_session",
                iteration=current_iteration,
                entity_id=candidate_id,
                phase="post_theorem_expand",
                worker_task="post_theorem_expand",
                started_at=post_expand_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(post_expand_started_monotonic),
                success=False,
                result="error",
                error=post_expand_error,
            )
            emit_phase_log(
                phase_logs,
                "post_theorem_expand_result",
                iteration=current_iteration,
                candidate_id=candidate_id,
                status="error",
                error=post_expand_error,
            )

    theorem_reuse_payload = {
        "candidate_id": candidate_id,
        "theorem_name": theorem_name,
        "statement": final_stmt.strip() or statement,
        "docstring_summary": docstring_summary,
        "rationale": rationale,
        "supporting_theorems": [theorem for theorem in supporting_theorems if theorem in known_theorem_names],
        "intermediate_lemmas": intermediate_lemmas,
        "iteration": current_iteration,
        "appended_to_derived": bool(theorem_code),
    }
    with state_lock:
        committed_theorem_code = commit_verified_theorem_and_generation(
            scratch_path=scratch_file,
            derived_file=derived_file,
            derived_entries=derived_entries,
            docstring=docstring_summary,
            data_dir=data_dir,
            derived_runtime_state=derived_runtime_state,
            run_id=run_id,
            current_iteration=current_iteration,
            rebuild_derived=not skip_verify,
        )
        theorem_reuse_payload["appended_to_derived"] = bool(committed_theorem_code)
        append_theorem_reuse_memory_entry(data_dir / "theorem_reuse_memory.json", theorem_reuse_payload)
        refresh_outcome = store_expand_candidates_and_refresh(
            data_dir=data_dir,
            statements_with_rationale=post_expand_candidates,
            source="post_theorem_expand",
            source_problem_id=theorem_name,
            source_kind="main_theorem",
            prioritize_worker_settings=prioritize_open_problems_worker_settings,
            prioritizer_prompt_file=prioritize_open_problems_prompt_file,
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
            allow_backfill=False,
        )
        stored_expand_rows = list(refresh_outcome.get("stored_expand_rows", []))
        priority_refresh_ran = bool(refresh_outcome.get("priority_refresh_ran", False))
        priority_refresh_error = str(refresh_outcome.get("priority_refresh_error", ""))
        priority_refresh_report = dict(refresh_outcome.get("priority_refresh_report", {}))
        if bool(refresh_outcome.get("priority_refresh_failed", False)):
            return {
                "processed": True,
                "candidate_id": candidate_id,
                "status": "proved",
                "verify_success": True,
                "theorem_name": theorem_name,
                "statement": final_stmt.strip() or statement,
                "theorem_code": committed_theorem_code,
                "supporting_theorems": list(supporting_theorems),
                "post_theorem_expand_candidates": post_expand_candidates,
                "stored_expand_rows": stored_expand_rows,
                "post_theorem_expand_error": post_expand_error,
                "batch_generator_added_problem_rows": list(priority_refresh_report.get("batch_generator_added_problem_rows", [])),
                "batch_generator_error": str(priority_refresh_report.get("batch_generator_error", "")),
                "promoted_expand_rows": [],
                "priority_refresh_ran": False,
                "priority_refresh_error": priority_refresh_error,
            }
    return {
        "processed": True,
        "candidate_id": candidate_id,
        "status": "proved",
        "verify_success": True,
        "theorem_name": theorem_name,
        "statement": final_stmt.strip() or statement,
        "theorem_code": committed_theorem_code,
        "supporting_theorems": list(supporting_theorems),
        "post_theorem_expand_candidates": post_expand_candidates,
        "stored_expand_rows": stored_expand_rows,
        "post_theorem_expand_error": post_expand_error,
        "batch_generator_added_problem_rows": list(priority_refresh_report.get("batch_generator_added_problem_rows", [])) if priority_refresh_ran else [],
        "batch_generator_error": str(priority_refresh_report.get("batch_generator_error", "")) if priority_refresh_ran else "",
        "promoted_expand_rows": list(priority_refresh_report.get("worker_meta", {}).get("promoted_expand_rows", [])) if priority_refresh_ran else [],
        "priority_refresh_ran": priority_refresh_ran,
        "priority_refresh_error": priority_refresh_error,
    }
