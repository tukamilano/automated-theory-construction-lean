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


SCRATCH_TEMPLATE = render_scratch_template()
MAX_EXPAND_CANDIDATES_PER_MAIN_THEOREM = 5


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


def validate_main_theorem_suggestion_output(
    payload: dict[str, Any],
    expected_candidate_id: str,
    known_problem_ids: list[str],
) -> tuple[str, str, str, str, str, list[str], list[str], list[str]]:
    required_keys = {
        "candidate_id",
        "result",
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
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_suggest output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_suggest candidate_id does not match request")

    result = str(payload.get("result", "")).strip()
    if result != "ok":
        raise ValueError("main_theorem_suggest result must be ok")

    statement = str(payload.get("statement", "")).strip()
    theorem_name_stem = str(payload.get("theorem_name_stem", "")).strip()
    docstring_summary = str(payload.get("docstring_summary", "")).strip()
    rationale = str(payload.get("rationale", "")).strip()
    theorem_pattern = str(payload.get("theorem_pattern", "")).strip()
    context_note = str(payload.get("context_note", "")).strip()
    conceptual_depth_note = str(payload.get("conceptual_depth_note", "")).strip()
    supporting = payload.get("supporting_theorems", [])
    missing = payload.get("missing_lemmas", [])
    source_problem_ids_value = payload.get("source_problem_ids", [])
    if not isinstance(supporting, list) or not isinstance(missing, list) or not isinstance(source_problem_ids_value, list):
        raise ValueError("main_theorem_suggest supporting_theorems, missing_lemmas, and source_problem_ids must be arrays")

    supporting_theorems = [str(item).strip() for item in supporting if str(item).strip()]
    missing_lemmas = [str(item).strip() for item in missing if str(item).strip()]
    known_problem_id_set = {str(item).strip() for item in known_problem_ids if str(item).strip()}
    source_problem_ids: list[str] = []
    seen_source_ids: set[str] = set()
    for item in source_problem_ids_value:
        problem_id = str(item).strip()
        if not problem_id or problem_id in seen_source_ids:
            continue
        if known_problem_id_set and problem_id not in known_problem_id_set:
            raise ValueError(f"main_theorem_suggest source_problem_id is not in tracked_problems: {problem_id}")
        seen_source_ids.add(problem_id)
        source_problem_ids.append(problem_id)

    if not statement:
        raise ValueError("main_theorem_suggest statement must be non-empty when result=ok")
    theorem_name_stem = validate_theorem_name_stem(theorem_name_stem)
    if not docstring_summary:
        raise ValueError("main_theorem_suggest docstring_summary must be non-empty when result=ok")
    if known_problem_id_set and not source_problem_ids:
        raise ValueError("main_theorem_suggest source_problem_ids must be non-empty when tracked_problems are available")
    if theorem_pattern not in {"new_theorem", "structure_discovery", "framework_introduction"}:
        raise ValueError("main_theorem_suggest theorem_pattern must be new_theorem|structure_discovery|framework_introduction")
    if not context_note:
        raise ValueError("main_theorem_suggest context_note must be non-empty when result=ok")
    if not conceptual_depth_note:
        raise ValueError("main_theorem_suggest conceptual_depth_note must be non-empty when result=ok")

    return (
        result,
        statement,
        theorem_name_stem,
        docstring_summary,
        rationale,
        supporting_theorems,
        missing_lemmas,
        source_problem_ids,
    )


def request_main_theorem_suggestion(
    *,
    worker_settings: Any,
    suggester_prompt: str,
    candidate_id: str,
    derived_entries: list[dict[str, str]],
    theory_context: str,
    tracked_rows: list[dict[str, Any]],
    current_iteration: int,
    guidance: dict[str, Any],
) -> tuple[tuple[str, str, str, str, str, list[str], list[str], list[str]], dict[str, Any]]:
    visible_tracked_rows = tracked_rows[:40]
    known_problem_ids = [str(row.get("id", "")).strip() for row in visible_tracked_rows if str(row.get("id", "")).strip()]
    theory_state, research_agenda = unpack_guidance_context(guidance)
    payload: dict[str, Any] = {
        "candidate_id": candidate_id,
        "current_iteration": current_iteration,
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in derived_entries
        ],
        "theory_context": theory_context,
        "tracked_problems": [
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
        ],
        "theory_state": theory_state,
        "research_agenda": research_agenda,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_suggest",
        system_prompt=suggester_prompt,
        payload=payload,
        metadata={"candidate_id": candidate_id, "derived_theorem_count": len(derived_entries)},
    )
    return validate_main_theorem_suggestion_output(response, candidate_id, known_problem_ids), worker_meta


def run_manual_main_theorem_check(
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
    suggest_prompt_file: str,
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
    phase_attempts_path: Path,
    compile_metrics: dict[str, Any],
    state_lock: threading.Lock,
    derived_runtime_state: dict[str, Any],
) -> dict[str, Any]:
    suggest_prompt = load_prompt_text(suggest_prompt_file)
    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(data_dir / "open_problems.jsonl")]
    archived_rows = read_archived_problem_rows(data_dir)
    tracked_rows = [dict(row, queue_status="open") for row in open_rows]
    tracked_rows.extend(dict(row, queue_status="archived") for row in archived_rows)
    candidate_id = "mt_manual"
    emit_phase_log(
        phase_logs,
        "main_theorem_suggest",
        iteration=current_iteration,
        candidate_id=candidate_id,
        derived_theorem_count=len(derived_entries),
        open_problem_count=len(open_rows),
        tracked_problem_count=len(tracked_rows),
    )
    suggest_started_monotonic = time.monotonic()
    suggest_started_at = iso_timestamp_now()
    try:
        (
            result,
            statement,
            theorem_name_stem,
            docstring_summary,
            rationale,
            supporting_theorems,
            missing_lemmas,
            source_problem_ids,
        ), _ = request_main_theorem_suggestion(
            worker_settings=worker_settings,
            suggester_prompt=suggest_prompt,
            candidate_id=candidate_id,
            derived_entries=derived_entries,
            theory_context=base_theory_context,
            tracked_rows=tracked_rows,
            current_iteration=current_iteration,
            guidance=load_current_guidance(data_dir),
        )
    except (RuntimeError, ValueError) as exc:
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_id,
            phase="main_theorem_suggest",
            worker_task="main_theorem_suggest",
            started_at=suggest_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(suggest_started_monotonic),
            success=False,
            result="error",
            error=str(exc),
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_suggest_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status="error",
            error=str(exc),
        )
        return {
            "status": "main_theorem_suggest_error",
            "processed": False,
            "verify_success": False,
            "error": str(exc),
        }
    append_phase_attempt_record(
        phase_attempts_path,
        run_id=run_id,
        session_type="main_theorem_session",
        iteration=current_iteration,
        entity_id=candidate_id,
        phase="main_theorem_suggest",
        worker_task="main_theorem_suggest",
        started_at=suggest_started_at,
        finished_at=iso_timestamp_now(),
        duration_ms=monotonic_duration_ms(suggest_started_monotonic),
        success=result == "ok",
        result=result,
    )
    emit_phase_log(
        phase_logs,
        "main_theorem_suggest_result",
        iteration=current_iteration,
        candidate_id=candidate_id,
        status=result,
    )

    report = process_manual_main_theorem(
        candidate_id=candidate_id,
        statement=statement,
        theorem_name=f"main_thm_{theorem_name_stem}",
        docstring_summary=docstring_summary,
        rationale=rationale,
        supporting_theorems=supporting_theorems,
        missing_lemmas=missing_lemmas,
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
        theory_state_history_path=Path(phase_attempts_path).parent / "theory_state_history.jsonl",
        compile_metrics=compile_metrics,
        state_lock=state_lock,
        derived_runtime_state=derived_runtime_state,
    )
    report["suggested_statement"] = statement
    report["suggested_rationale"] = rationale
    report["source_problem_ids"] = list(source_problem_ids)
    return report


def process_manual_main_theorem(
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
    phase_attempts_path: Path,
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
