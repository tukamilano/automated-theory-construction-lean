from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import run_loop


def main() -> int:
    original_verify_scratch = run_loop.verify_scratch
    try:
        def fake_verify_scratch(_problem_id, _result, _scratch_file, timeout_sec=None):
            return {
                "success": True,
                "stdout": "",
                "stderr": "",
                "duration_ms": 0,
            }

        run_loop.verify_scratch = fake_verify_scratch

        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            scratch_path = tmp / "Scratch.lean"
            memory_path = tmp / "formalization_memory.json"
            phase_attempts_path = tmp / "phase_attempts.jsonl"

            verify_success, theorem_name, result, prelude_code, proof_text, counterexample_text, verify_error_excerpt, stmt = (
                run_loop.attempt_formalization_until_timeout(
                    problem_id="op_000005",
                    theorem_name="thm_example",
                    stmt="False",
                    result="counterexample",
                    proof_sketch="placeholder",
                    counterexample_text="",
                    scratch_file=scratch_path,
                    skip_verify=False,
                    formalize_worker_settings={},
                    repair_worker_settings={},
                    formalizer_prompts={},
                    repair_prompts={},
                    open_rows=[],
                    theory_context="",
                    verify_timeout_sec=10,
                    formalization_retry_budget_sec=1,
                    memory_path=memory_path,
                    current_iteration_full_logs=[],
                    initial_prelude_code="",
                    initial_proof_text="sorry",
                    phase_logger=None,
                    max_same_error_streak=0,
                    run_id="test-run",
                    session_type="loop",
                    iteration=1,
                    phase_attempts_path=phase_attempts_path,
                    compile_metrics={
                        "compile_attempt_count": 0,
                        "compile_success_count": 0,
                    },
                )
            )
    finally:
        run_loop.verify_scratch = original_verify_scratch

    if verify_success:
        raise RuntimeError("sorry-backed theorem should not remain verified")
    if theorem_name != "thm_example":
        raise RuntimeError(f"unexpected theorem name: {theorem_name}")
    if result != "counterexample":
        raise RuntimeError(f"unexpected result kind: {result}")
    if prelude_code != "":
        raise RuntimeError(f"unexpected prelude code: {prelude_code}")
    if proof_text != "sorry":
        raise RuntimeError(f"unexpected proof text: {proof_text}")
    if counterexample_text != "":
        raise RuntimeError(f"unexpected counterexample text: {counterexample_text}")
    if stmt != "False":
        raise RuntimeError(f"unexpected stmt: {stmt}")
    if verify_error_excerpt != "Lean verification succeeded but proof still contains sorry":
        raise RuntimeError(f"unexpected verify_error_excerpt: {verify_error_excerpt}")

    print("run loop reject sorry test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
