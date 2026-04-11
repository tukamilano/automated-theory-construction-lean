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


def validate_main_theorem_suggestion_output(
    payload: dict[str, Any],
    expected_candidate_id: str,
) -> tuple[str, str, str, str, str, list[str], list[str]]:
    required_keys = {
        "candidate_id",
        "result",
        "statement",
        "theorem_name_stem",
        "docstring_summary",
        "rationale",
        "supporting_theorems",
        "missing_lemmas",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_suggest output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_suggest candidate_id does not match request")

    result = str(payload.get("result", "")).strip()
    if result not in {"ok", "stuck"}:
        raise ValueError("main_theorem_suggest result must be ok|stuck")

    statement = str(payload.get("statement", "")).strip()
    theorem_name_stem = str(payload.get("theorem_name_stem", "")).strip()
    docstring_summary = str(payload.get("docstring_summary", "")).strip()
    rationale = str(payload.get("rationale", "")).strip()
    supporting = payload.get("supporting_theorems", [])
    missing = payload.get("missing_lemmas", [])
    if not isinstance(supporting, list) or not isinstance(missing, list):
        raise ValueError("main_theorem_suggest supporting_theorems and missing_lemmas must be arrays")

    supporting_theorems = [str(item).strip() for item in supporting if str(item).strip()]
    missing_lemmas = [str(item).strip() for item in missing if str(item).strip()]

    if result == "ok":
        if not statement:
            raise ValueError("main_theorem_suggest statement must be non-empty when result=ok")
        theorem_name_stem = validate_theorem_name_stem(theorem_name_stem)
        if not docstring_summary:
            raise ValueError("main_theorem_suggest docstring_summary must be non-empty when result=ok")
    else:
        if statement or theorem_name_stem or docstring_summary:
            raise ValueError("main_theorem_suggest stuck result must not return statement/name/docstring")

    return (
        result,
        statement,
        theorem_name_stem,
        docstring_summary,
        rationale,
        supporting_theorems,
        missing_lemmas,
    )


def validate_main_theorem_plan_output(
    payload: dict[str, Any],
    expected_candidate_id: str,
) -> tuple[str, str, str, list[str], list[str], str]:
    required_keys = {
        "candidate_id",
        "result",
        "plan_summary",
        "proof_sketch",
        "supporting_theorems",
        "intermediate_lemmas",
        "notes",
    }
    if set(payload.keys()) != required_keys:
        raise ValueError("main_theorem_plan output keys mismatch required contract")

    candidate_id = str(payload.get("candidate_id", "")).strip()
    if candidate_id != expected_candidate_id:
        raise ValueError("main_theorem_plan candidate_id does not match request")

    result = str(payload.get("result", "")).strip()
    if result not in {"ok", "stuck"}:
        raise ValueError("main_theorem_plan result must be ok|stuck")

    plan_summary = str(payload.get("plan_summary", "")).strip()
    proof_sketch = str(payload.get("proof_sketch", "")).strip()
    notes = str(payload.get("notes", "")).strip()
    supporting = payload.get("supporting_theorems", [])
    intermediate = payload.get("intermediate_lemmas", [])
    if not isinstance(supporting, list) or not isinstance(intermediate, list):
        raise ValueError("main_theorem_plan supporting_theorems and intermediate_lemmas must be arrays")

    supporting_theorems = [str(item).strip() for item in supporting if str(item).strip()]
    intermediate_lemmas = [str(item).strip() for item in intermediate if str(item).strip()]
    if result == "ok" and not proof_sketch:
        raise ValueError("main_theorem_plan proof_sketch must be non-empty when result=ok")
    return result, plan_summary, proof_sketch, supporting_theorems, intermediate_lemmas, notes


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
) -> tuple[tuple[str, str, str, str, str, list[str], list[str]], dict[str, Any]]:
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
            for row in tracked_rows[:40]
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
    return validate_main_theorem_suggestion_output(response, candidate_id), worker_meta


def request_main_theorem_plan(
    *,
    worker_settings: Any,
    planner_prompt: str,
    candidate_row: dict[str, Any],
    derived_entries: list[dict[str, str]],
    theory_context: str,
) -> tuple[tuple[str, str, str, list[str], list[str], str], dict[str, Any]]:
    payload: dict[str, Any] = {
        "candidate_id": str(candidate_row.get("candidate_id", "")),
        "statement": str(candidate_row.get("statement", "")),
        "theorem_name": str(candidate_row.get("theorem_name", "")),
        "docstring_summary": str(candidate_row.get("docstring_summary", "")),
        "rationale": str(candidate_row.get("rationale", "")),
        "supporting_theorems": list(candidate_row.get("supporting_theorems", [])),
        "missing_lemmas": list(candidate_row.get("missing_lemmas", [])),
        "derived_theorems": [
            {
                "name": str(entry.get("name", "")),
                "statement": str(entry.get("statement", "")),
            }
            for entry in shortlist_relevant_derived_entries(
                derived_entries,
                str(candidate_row.get("statement", "")),
                max_entries=8,
            )
        ],
        "theory_context": theory_context,
    }
    response, worker_meta = invoke_worker_json(
        settings=worker_settings,
        task_type="main_theorem_plan",
        system_prompt=planner_prompt,
        payload=payload,
        metadata={"candidate_id": str(candidate_row.get("candidate_id", ""))},
    )
    return validate_main_theorem_plan_output(response, str(candidate_row.get("candidate_id", ""))), worker_meta


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
    plan_prompt_file: str,
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
    if result != "ok":
        return {
            "status": "main_theorem_suggest_stuck",
            "processed": False,
            "verify_success": False,
        }

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
        plan_prompt_file=plan_prompt_file,
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
    plan_prompt_file: str,
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
    plan_summary = ""
    proof_sketch = ""
    plan_notes = ""
    intermediate_lemmas: list[str] = []
    emit_phase_log(
        phase_logs,
        "main_theorem_plan",
        iteration=current_iteration,
        candidate_id=candidate_id,
        theorem_name=theorem_name,
    )
    planner_prompt = load_prompt_text(plan_prompt_file)
    plan_started_monotonic = time.monotonic()
    plan_started_at = iso_timestamp_now()
    try:
        (
            plan_result,
            generated_plan_summary,
            generated_proof_sketch,
            plan_supporting_theorems,
            intermediate_lemmas,
            plan_notes,
        ), _ = request_main_theorem_plan(
            worker_settings=worker_settings,
            planner_prompt=planner_prompt,
            candidate_row={
                "candidate_id": candidate_id,
                "statement": statement,
                "theorem_name": theorem_name,
                "docstring_summary": docstring_summary,
                "rationale": rationale,
                "supporting_theorems": supporting_theorems,
                "missing_lemmas": missing_lemmas,
            },
            derived_entries=derived_entries,
            theory_context=theorem_context,
        )
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_id,
            phase="main_theorem_plan",
            worker_task="main_theorem_plan",
            started_at=plan_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(plan_started_monotonic),
            success=plan_result == "ok",
            result=plan_result,
        )
        if plan_result == "ok":
            plan_summary = generated_plan_summary
            proof_sketch = generated_proof_sketch
            supporting_theorems = plan_supporting_theorems or list(supporting_theorems)
        emit_phase_log(
            phase_logs,
            "main_theorem_plan_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status=plan_result,
        )
    except (RuntimeError, ValueError) as exc:
        plan_notes = f"main theorem plan failed: {exc}"
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type="main_theorem_session",
            iteration=current_iteration,
            entity_id=candidate_id,
            phase="main_theorem_plan",
            worker_task="main_theorem_plan",
            started_at=plan_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(plan_started_monotonic),
            success=False,
            result="error",
            error=str(exc),
        )
        emit_phase_log(
            phase_logs,
            "main_theorem_plan_result",
            iteration=current_iteration,
            candidate_id=candidate_id,
            status="error",
            error=str(exc),
        )

    if not proof_sketch:
        proof_sketch = rationale.strip() or f"Prove {theorem_name} from the current Derived.lean cluster."
    if plan_summary:
        theorem_context += f"\n\n-- Main theorem proof plan:\n-- {plan_summary}"
    if intermediate_lemmas:
        theorem_context += "\n-- Intermediate lemmas:\n"
        theorem_context += "\n".join(f"-- {item}" for item in intermediate_lemmas)
    if plan_notes:
        theorem_context += f"\n-- Planner notes: {plan_notes}"

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
        return {
            "processed": True,
            "candidate_id": candidate_id,
            "status": "blocked",
            "verify_success": False,
            "verify_error_excerpt": verify_error_excerpt,
            "plan_summary": plan_summary,
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
        "plan_summary": plan_summary,
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
