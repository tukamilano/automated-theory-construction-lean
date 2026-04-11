from __future__ import annotations

import time
from pathlib import Path
from typing import Any
from typing import Callable


def attempt_formalization_until_timeout(
    *,
    problem_id: str,
    theorem_name: str,
    stmt: str,
    result: str,
    proof_sketch: str,
    counterexample_text: str,
    scratch_file: Path,
    skip_verify: bool,
    formalize_worker_settings: Any,
    repair_worker_settings: Any,
    formalizer_prompts: dict[str, str],
    repair_prompts: dict[str, str],
    open_rows: list[dict[str, Any]],
    theory_context: str,
    verify_timeout_sec: int | None = 180,
    formalization_retry_budget_sec: int | None = None,
    memory_path: Path,
    current_iteration_full_logs: list[dict[str, Any]],
    initial_prelude_code: str = "",
    initial_proof_text: str = "",
    phase_logger: Callable[..., None] | None = None,
    forbid_sorry: bool = False,
    max_same_error_streak: int | None = None,
    retry_initial_formalization_until_budget: bool = False,
    run_id: str,
    session_type: str,
    iteration: int,
    phase_attempts_path: Path,
    compile_metrics: dict[str, Any],
) -> tuple[bool, str | None, str, str, str, str, str, str]:
    from run_loop import LEAN_VERIFY_LOCK
    from run_loop import RepairRequestPacket
    from run_loop import analyze_lean_failure
    from run_loop import append_current_iteration_log
    from run_loop import append_phase_attempt_record
    from run_loop import build_retry_deadline
    from run_loop import extract_unused_variable_names
    from run_loop import file_contains_sorry
    from run_loop import formalize_to_scratch
    from run_loop import invoke_worker_json
    from run_loop import is_worker_timeout_error
    from run_loop import iso_timestamp_now
    from run_loop import load_formalization_memory
    from run_loop import monotonic_duration_ms
    from run_loop import normalize_stmt_text
    from run_loop import prune_unused_binders_from_statement
    from run_loop import request_initial_formalization
    from run_loop import save_formalization_memory
    from run_loop import select_formalizer_prompt
    from run_loop import update_compile_metrics
    from run_loop import update_same_fingerprint_streak
    from run_loop import validate_formalizer_output
    from run_loop import validate_theorem_name
    from run_loop import verify_scratch
    from run_loop import write_formalization_candidate_to_scratch

    verify_success = False
    current_theorem_name = validate_theorem_name(theorem_name)
    current_stmt = stmt
    verify_error_excerpt = ""
    prelude_code = initial_prelude_code
    proof_text = initial_proof_text
    attempted_strengthened_statements = {normalize_stmt_text(current_stmt)}
    best_verified_candidate: dict[str, Any] | None = None
    deadline = build_retry_deadline(formalization_retry_budget_sec)

    if result not in {"proof", "counterexample"}:
        persisted_history = load_formalization_memory(memory_path, problem_id)
        persisted_history.append(
            {
                "result": result,
                "verify_success": verify_success,
                "proof_sketch": proof_sketch,
                "prelude_code": prelude_code,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "lean_error_excerpt": verify_error_excerpt,
                "lean_error_fingerprint": "non_formalized_result",
            }
        )
        save_formalization_memory(memory_path, problem_id, persisted_history)
        return (
            verify_success,
            current_theorem_name,
            result,
            prelude_code,
            proof_text,
            counterexample_text,
            verify_error_excerpt,
            current_stmt,
        )

    initial_formalize_round = 0
    initial_retry_instruction = ""
    previous_initial_result = ""
    previous_initial_prelude_code = ""
    previous_initial_proof_text = ""
    previous_initial_counterexample_text = ""
    if not prelude_code.strip() and not proof_text.strip():
        while True:
            if (
                retry_initial_formalization_until_budget
                and deadline is not None
                and initial_formalize_round > 0
                and time.monotonic() >= deadline
            ):
                if not verify_error_excerpt:
                    verify_error_excerpt = (
                        "formalization retry budget exhausted before initial formalization produced Lean code"
                    )
                return (
                    verify_success,
                    current_theorem_name,
                    "stuck",
                    prelude_code,
                    proof_text,
                    counterexample_text,
                    verify_error_excerpt,
                    current_stmt,
                )
            try:
                same_problem_history_tail = load_formalization_memory(memory_path, problem_id)[-8:]
                proof_lean_started_monotonic = time.monotonic()
                proof_lean_started_at = iso_timestamp_now()
                result, proof_sketch, prelude_code, proof_text, counterexample_text = request_initial_formalization(
                    formalize_worker_settings=formalize_worker_settings,
                    formalizer_prompt=select_formalizer_prompt(formalizer_prompts, result=result),
                    problem_id=problem_id,
                    stmt=current_stmt,
                    result=result,
                    proof_sketch=proof_sketch,
                    counterexample_text=counterexample_text,
                    open_rows=open_rows,
                    theory_context=theory_context,
                    current_iteration_full_logs=current_iteration_full_logs,
                    same_problem_history_tail=same_problem_history_tail,
                    retry_round=initial_formalize_round,
                    retry_instruction=initial_retry_instruction,
                    previous_result=previous_initial_result,
                    previous_prelude_code=previous_initial_prelude_code,
                    previous_proof_text=previous_initial_proof_text,
                    previous_counterexample_text=previous_initial_counterexample_text,
                )
            except RuntimeError as exc:
                append_phase_attempt_record(
                    phase_attempts_path,
                    run_id=run_id,
                    session_type=session_type,
                    iteration=iteration,
                    entity_id=problem_id,
                    phase="proof_lean",
                    worker_task="formalize",
                    started_at=proof_lean_started_at,
                    finished_at=iso_timestamp_now(),
                    duration_ms=monotonic_duration_ms(proof_lean_started_monotonic),
                    success=False,
                    result="timeout" if is_worker_timeout_error(exc) else "error",
                    timeout=is_worker_timeout_error(exc),
                    error=str(exc),
                )
                if is_worker_timeout_error(exc):
                    persisted_history = load_formalization_memory(memory_path, problem_id)
                    verify_error_excerpt = f"formalize worker timeout: {exc}"
                    persisted_history.append(
                        {
                            "result": "stuck",
                            "verify_success": verify_success,
                            "proof_sketch": proof_sketch,
                            "prelude_code": prelude_code,
                            "proof_text": proof_text,
                            "counterexample_text": counterexample_text,
                            "lean_error_excerpt": verify_error_excerpt,
                            "lean_error_fingerprint": "formalizer_timeout",
                        }
                    )
                    save_formalization_memory(memory_path, problem_id, persisted_history)
                    if not retry_initial_formalization_until_budget:
                        return (
                            verify_success,
                            current_theorem_name,
                            "stuck",
                            prelude_code,
                            proof_text,
                            counterexample_text,
                            verify_error_excerpt,
                            current_stmt,
                        )
                    previous_initial_result = "stuck"
                    previous_initial_prelude_code = prelude_code
                    previous_initial_proof_text = proof_text
                    previous_initial_counterexample_text = counterexample_text
                    initial_retry_instruction = (
                        "Previous formalize attempt timed out before producing Lean code. "
                        "Try a materially different proof route or a smaller reusable decomposition. "
                        "Only return `stuck` if no defensible Lean path remains."
                    )
                    initial_formalize_round += 1
                    prelude_code = ""
                    proof_text = ""
                    counterexample_text = ""
                    continue
                raise
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type=session_type,
                iteration=iteration,
                entity_id=problem_id,
                phase="proof_lean",
                worker_task="formalize",
                started_at=proof_lean_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(proof_lean_started_monotonic),
                success=result in {"proof", "counterexample"},
                result=result,
            )
            if result in {"proof", "counterexample"}:
                break

            persisted_history = load_formalization_memory(memory_path, problem_id)
            persisted_history.append(
                {
                    "result": result,
                    "verify_success": verify_success,
                    "proof_sketch": proof_sketch,
                    "prelude_code": prelude_code,
                    "proof_text": proof_text,
                    "counterexample_text": counterexample_text,
                    "lean_error_excerpt": verify_error_excerpt,
                    "lean_error_fingerprint": "formalizer_returned_stuck",
                }
            )
            save_formalization_memory(memory_path, problem_id, persisted_history)
            if not retry_initial_formalization_until_budget:
                return (
                    verify_success,
                    current_theorem_name,
                    result,
                    prelude_code,
                    proof_text,
                    counterexample_text,
                    verify_error_excerpt,
                    current_stmt,
                )
            verify_error_excerpt = "formalizer returned stuck before Lean verification"
            previous_initial_result = result
            previous_initial_prelude_code = prelude_code
            previous_initial_proof_text = proof_text
            previous_initial_counterexample_text = counterexample_text
            initial_retry_instruction = (
                "Previous formalize attempt returned `stuck` before Lean verification. "
                "Try a different proof route, intermediate lemma cut, or counterexample direction if the proof direction is unsound. "
                "Only return `stuck` if no defensible Lean path remains."
            )
            initial_formalize_round += 1
            prelude_code = ""
            proof_text = ""
            counterexample_text = ""

    persisted_history = load_formalization_memory(memory_path, problem_id)
    repair_round = 0
    repair_history: list[dict[str, Any]] = list(persisted_history)
    last_error_fingerprint = ""
    same_error_streak = 0

    def restore_best_verified_candidate() -> tuple[bool, str | None, str, str, str, str, str, str]:
        assert best_verified_candidate is not None
        best_result = str(best_verified_candidate["result"])
        best_stmt = str(best_verified_candidate["stmt"])
        best_prelude_code = str(best_verified_candidate["prelude_code"])
        best_proof_text = str(best_verified_candidate["proof_text"])
        best_counterexample_text = str(best_verified_candidate["counterexample_text"])
        best_verify_error_excerpt = str(best_verified_candidate["verify_error_excerpt"])
        write_formalization_candidate_to_scratch(
            scratch_file=scratch_file,
            theorem_name=current_theorem_name,
            stmt=best_stmt,
            result=best_result,
            prelude_code=best_prelude_code,
            proof_text=best_proof_text,
            counterexample_text=best_counterexample_text,
        )
        return (
            True,
            current_theorem_name,
            best_result,
            best_prelude_code,
            best_proof_text,
            best_counterexample_text,
            best_verify_error_excerpt,
            best_stmt,
        )

    while True:
        if phase_logger is not None:
            phase_logger(
                phase="formalize_and_verify",
                status="begin",
                problem_id=problem_id,
                result=result,
                repair_round=repair_round,
            )
        theorem_name, scratch_code = formalize_to_scratch(
            theorem_name=current_theorem_name,
            stmt=current_stmt,
            mode=result,
            prelude_code=prelude_code,
            proof_text=proof_text,
            counterexample_text=counterexample_text,
        )

        lean_diagnostics = ""
        verify_stderr_text = ""
        verify_stdout_text = ""
        scratch_file.parent.mkdir(parents=True, exist_ok=True)
        scratch_file.write_text(scratch_code, encoding="utf-8")
        if skip_verify:
            verify_success = True
            verify_error_excerpt = ""
            verify_error_analysis = {
                "fingerprint": "verify_skipped",
                "categories": ["verify_skipped"],
                "top_lines": [],
            }
        else:
            verify_started_at = iso_timestamp_now()
            verify_started_monotonic = time.monotonic()
            with LEAN_VERIFY_LOCK:
                verify_result = verify_scratch(problem_id, result, scratch_file, timeout_sec=verify_timeout_sec)
            update_compile_metrics(compile_metrics, verify_result)
            verify_success = bool(verify_result.get("success", False))
            verify_stderr_text = str(verify_result.get("stderr", ""))
            verify_stdout_text = str(verify_result.get("stdout", ""))
            lean_diagnostics = (verify_stderr_text + "\n" + verify_stdout_text).strip()
            if not verify_success:
                verify_stderr = verify_stderr_text.strip()
                verify_stdout = verify_stdout_text.strip()
                verify_error_excerpt = (verify_stderr or verify_stdout).splitlines()[0] if (verify_stderr or verify_stdout) else "Lean verification failed"
            else:
                verify_error_excerpt = ""
            verify_error_analysis = analyze_lean_failure(
                verify_stderr_text,
                verify_stdout_text,
                verify_result=verify_result,
            )
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type=session_type,
                iteration=iteration,
                entity_id=problem_id,
                phase="verify",
                worker_task="scratch_verify",
                started_at=verify_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=int(verify_result.get("duration_ms", monotonic_duration_ms(verify_started_monotonic)) or 0),
                success=verify_success,
                result="verified" if verify_success else "failed",
            )

        if phase_logger is not None:
            phase_logger(
                phase="formalize_and_verify_result",
                problem_id=problem_id,
                result=result,
                repair_round=repair_round,
                verify_success=verify_success,
                error_fingerprint=str(verify_error_analysis.get("fingerprint", "")),
            )

        if verify_success:
            if file_contains_sorry(scratch_file):
                verify_success = False
                verify_error_excerpt = "Lean verification succeeded but proof still contains sorry"
                verify_error_analysis = {
                    "fingerprint": "verified_theorem_contains_sorry",
                    "categories": ["contains_sorry"],
                    "top_lines": [verify_error_excerpt],
                }
            else:
                last_error_fingerprint = ""
                same_error_streak = 0
        if verify_success:
            best_verified_candidate = {
                "stmt": current_stmt,
                "result": result,
                "prelude_code": prelude_code,
                "proof_text": proof_text,
                "counterexample_text": counterexample_text,
                "verify_error_excerpt": verify_error_excerpt,
            }
            unused_names = extract_unused_variable_names(verify_stderr_text, verify_stdout_text)
            strengthened_stmt = (
                prune_unused_binders_from_statement(current_stmt, unused_names)
                if result == "proof" and not skip_verify
                else current_stmt
            )
            strengthened_norm = normalize_stmt_text(strengthened_stmt)
            if (
                result == "proof"
                and strengthened_stmt != current_stmt
                and strengthened_norm not in attempted_strengthened_statements
            ):
                attempted_strengthened_statements.add(strengthened_norm)
                current_stmt = strengthened_stmt
                continue
            success_fingerprint = str(verify_error_analysis.get("fingerprint", "verified"))
            repair_history.append(
                {
                    "result": result,
                    "verify_success": True,
                    "proof_sketch": proof_sketch,
                    "prelude_code": prelude_code,
                    "proof_text": proof_text,
                    "counterexample_text": counterexample_text,
                    "lean_error_excerpt": verify_error_excerpt,
                    "lean_error_fingerprint": success_fingerprint,
                }
            )
            if len(repair_history) > 20:
                repair_history = repair_history[-20:]
            save_formalization_memory(memory_path, problem_id, repair_history)
            return (
                verify_success,
                current_theorem_name,
                result,
                prelude_code,
                proof_text,
                counterexample_text,
                verify_error_excerpt,
                current_stmt,
            )

        if deadline is not None and time.monotonic() >= deadline:
            save_formalization_memory(memory_path, problem_id, repair_history)
            if best_verified_candidate is not None:
                return restore_best_verified_candidate()
            return (
                verify_success,
                current_theorem_name,
                result,
                prelude_code,
                proof_text,
                counterexample_text,
                verify_error_excerpt,
                current_stmt,
            )

        error_fingerprint = str(verify_error_analysis.get("fingerprint", "no_diagnostics"))
        error_categories = verify_error_analysis.get("categories", [])
        lean_error_top_lines = verify_error_analysis.get("top_lines", [])
        last_error_fingerprint, same_error_streak = update_same_fingerprint_streak(
            last_fingerprint=last_error_fingerprint,
            current_fingerprint=error_fingerprint,
            current_streak=same_error_streak,
        )
        if best_verified_candidate is not None and normalize_stmt_text(current_stmt) != normalize_stmt_text(str(best_verified_candidate["stmt"])):
            retry_instruction = (
                "The previous theorem already verified. A stronger candidate statement was formed by removing unused binders "
                "from `stmt`. Try to prove this stronger `stmt`; if the old proof no longer fits, revise `prelude_code` and "
                "`proof_text` minimally so the new statement verifies. proof_text must be Lean tactic code only."
            )
        else:
            retry_instruction = (
                "Previous proof/counterexample failed Lean formalization or verification. "
                "Read the Lean diagnostics carefully. Revise proof_sketch if the strategy was wrong, "
                "then fix prelude_code and proof_text to match. proof_text must be Lean tactic code only."
            )

        repair_history.append(
            {
                "result": result,
                "verify_success": verify_success,
                "proof_sketch": proof_sketch,
                "prelude_code": prelude_code,
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
        if max_same_error_streak is not None and same_error_streak >= max_same_error_streak:
            save_formalization_memory(memory_path, problem_id, repair_history)
            if best_verified_candidate is not None:
                return restore_best_verified_candidate()
            return (
                False,
                current_theorem_name,
                result,
                prelude_code,
                proof_text,
                counterexample_text,
                verify_error_excerpt,
                current_stmt,
            )
        if phase_logger is not None:
            phase_logger(
                phase="repair",
                problem_id=problem_id,
                repair_round=repair_round,
                error_fingerprint=error_fingerprint,
            )
        repair_request = RepairRequestPacket(
            problem_id=problem_id,
            stmt=current_stmt,
            theory_context=theory_context,
            retry_instruction=retry_instruction,
            error_fingerprint=error_fingerprint,
            error_categories=error_categories,
            previous_result=result,
            previous_proof_sketch=proof_sketch,
            previous_prelude_code=prelude_code,
            previous_proof_text=proof_text,
            previous_counterexample_text=counterexample_text,
            repair_history_tail=repair_history[-8:],
            lean_error_excerpt=verify_error_excerpt,
            lean_error_top_lines=lean_error_top_lines,
            lean_diagnostics="\n".join(lean_diagnostics.splitlines()[:60]),
            current_scratch_code=scratch_code or "",
            mathlib_import_in_scratch=True,
        )
        current_repair_prompt = select_formalizer_prompt(repair_prompts, result=result)

        try:
            repair_started_monotonic = time.monotonic()
            repair_started_at = iso_timestamp_now()
            repaired, repair_worker_meta = invoke_worker_json(
                settings=repair_worker_settings,
                task_type="repair",
                system_prompt=current_repair_prompt,
                payload=repair_request.to_payload(),
                metadata={"problem_id": problem_id, "repair_round": repair_round},
            )
            append_current_iteration_log(
                current_iteration_full_logs,
                stage="repair",
                index=repair_round,
                worker_meta=repair_worker_meta,
            )
        except RuntimeError as exc:
            append_phase_attempt_record(
                phase_attempts_path,
                run_id=run_id,
                session_type=session_type,
                iteration=iteration,
                entity_id=problem_id,
                phase="repair_lean",
                worker_task="repair",
                started_at=repair_started_at,
                finished_at=iso_timestamp_now(),
                duration_ms=monotonic_duration_ms(repair_started_monotonic),
                success=False,
                result="timeout" if is_worker_timeout_error(exc) else "error",
                timeout=is_worker_timeout_error(exc),
                error=str(exc),
            )
            if is_worker_timeout_error(exc):
                verify_error_excerpt = f"repair worker timeout: {exc}"
                save_formalization_memory(memory_path, problem_id, repair_history)
                if best_verified_candidate is not None:
                    return restore_best_verified_candidate()
                return (
                    verify_success,
                    theorem_name,
                    result,
                    prelude_code,
                    proof_text,
                    counterexample_text,
                    verify_error_excerpt,
                    current_stmt,
                )
            raise
        append_phase_attempt_record(
            phase_attempts_path,
            run_id=run_id,
            session_type=session_type,
            iteration=iteration,
            entity_id=problem_id,
            phase="repair_lean",
            worker_task="repair",
            started_at=repair_started_at,
            finished_at=iso_timestamp_now(),
            duration_ms=monotonic_duration_ms(repair_started_monotonic),
            success=True,
            result="ok",
        )
        try:
            result, proof_sketch, prelude_code, proof_text, counterexample_text = validate_formalizer_output(
                repaired,
                problem_id,
            ).as_tuple()
        except ValueError as exc:
            verify_error_excerpt = f"repair output invalid: {exc}"
            continue
        if result not in {"proof", "counterexample"}:
            save_formalization_memory(memory_path, problem_id, repair_history)
            if best_verified_candidate is not None:
                return restore_best_verified_candidate()
            return (
                False,
                current_theorem_name,
                result,
                prelude_code,
                proof_text,
                counterexample_text,
                verify_error_excerpt,
                current_stmt,
            )


__all__ = ["attempt_formalization_until_timeout"]
