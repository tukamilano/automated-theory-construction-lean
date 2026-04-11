from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import run_loop


def main() -> int:
    original_request_initial_formalization = run_loop.request_initial_formalization
    try:
        attempts: list[dict[str, object]] = []

        def fake_request_initial_formalization(**kwargs):
            attempts.append(
                {
                    "retry_round": kwargs.get("retry_round"),
                    "retry_instruction": kwargs.get("retry_instruction"),
                    "previous_result": kwargs.get("previous_result"),
                }
            )
            if len(attempts) == 1:
                return "stuck", "first route failed", "", "", ""
            return "proof", "second route works", "", "intro h\nexact h", ""

        run_loop.request_initial_formalization = fake_request_initial_formalization

        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            scratch_path = tmp / "Scratch.lean"
            memory_path = tmp / "formalization_memory.json"
            phase_attempts_path = tmp / "phase_attempts.jsonl"

            verify_success, theorem_name, result, prelude_code, proof_text, counterexample_text, verify_error_excerpt, stmt = (
                run_loop.attempt_formalization_until_timeout(
                    problem_id="mt_main_theorem",
                    theorem_name="main_thm_example",
                    stmt="False -> False",
                    result="proof",
                    proof_sketch="placeholder",
                    counterexample_text="",
                    scratch_file=scratch_path,
                    skip_verify=True,
                    formalize_worker_settings={},
                    repair_worker_settings={},
                    formalizer_prompts={"proof": "prompt", "counterexample": "prompt"},
                    repair_prompts={"proof": "repair", "counterexample": "repair"},
                    open_rows=[],
                    theory_context="",
                    verify_timeout_sec=10,
                    formalization_retry_budget_sec=60,
                    memory_path=memory_path,
                    current_iteration_full_logs=[],
                    initial_prelude_code="",
                    initial_proof_text="",
                    phase_logger=None,
                    max_same_error_streak=1,
                    retry_initial_formalization_until_budget=True,
                    run_id="test-run",
                    session_type="main_theorem_session",
                    iteration=1,
                    phase_attempts_path=phase_attempts_path,
                    compile_metrics={
                        "compile_attempt_count": 0,
                        "compile_success_count": 0,
                    },
                )
            )
    finally:
        run_loop.request_initial_formalization = original_request_initial_formalization

    if len(attempts) != 2:
        raise RuntimeError(f"expected two initial formalize attempts, got {attempts}")
    if attempts[0]["retry_round"] != 0:
        raise RuntimeError(f"unexpected first retry_round: {attempts[0]}")
    if attempts[1]["retry_round"] != 1:
        raise RuntimeError(f"unexpected second retry_round: {attempts[1]}")
    if attempts[1]["previous_result"] != "stuck":
        raise RuntimeError(f"expected retry payload to preserve previous_result=stuck, got {attempts[1]}")
    if not attempts[1]["retry_instruction"]:
        raise RuntimeError(f"expected retry_instruction on second attempt, got {attempts[1]}")
    if not verify_success:
        raise RuntimeError("main theorem initial formalize retry should eventually verify")
    if theorem_name != "main_thm_example":
        raise RuntimeError(f"unexpected theorem name: {theorem_name}")
    if result != "proof":
        raise RuntimeError(f"unexpected result: {result}")
    if prelude_code != "":
        raise RuntimeError(f"unexpected prelude_code: {prelude_code}")
    if proof_text != "intro h\nexact h":
        raise RuntimeError(f"unexpected proof_text: {proof_text}")
    if counterexample_text != "":
        raise RuntimeError(f"unexpected counterexample_text: {counterexample_text}")
    if verify_error_excerpt != "":
        raise RuntimeError(f"unexpected verify_error_excerpt: {verify_error_excerpt}")
    if stmt != "False -> False":
        raise RuntimeError(f"unexpected stmt: {stmt}")

    print("run loop main theorem initial formalize retry test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
