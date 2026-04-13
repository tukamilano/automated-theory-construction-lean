from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import run_loop


def main() -> int:
    original_invoke_worker_json = run_loop.invoke_worker_json
    try:
        def fake_invoke_worker_json(*, settings, task_type, system_prompt, payload, metadata):
            raise RuntimeError(
                "Worker returned error: Command '['codex', 'exec']' timed out after 390 seconds "
                "(task_type=prover)"
            )

        run_loop.invoke_worker_json = fake_invoke_worker_json

        with tempfile.TemporaryDirectory() as tmpdir:
            phase_attempts_path = Path(tmpdir) / "phase_attempts.jsonl"
            result, proof_sketch, counterexample_text, attempts_used, worker_meta = run_loop.query_prover_with_retries(
                worker_settings={},
                prover_prompt="test prover prompt",
                problem_id="op_000001",
                stmt="True",
                original_stmt="True",
                derived_theorems=[],
                prover_retry_budget_sec=60,
                theory_context="",
                current_iteration_full_logs=[],
                same_problem_history_tail=[],
                run_id="test-run",
                session_type="loop",
                iteration=1,
                phase_attempts_path=phase_attempts_path,
                max_same_error_streak=None,
            )
    finally:
        run_loop.invoke_worker_json = original_invoke_worker_json

    if result != "stuck":
        raise RuntimeError(f"timeout should be converted to stuck, got {result}")
    if "timed out" not in proof_sketch:
        raise RuntimeError(f"timeout explanation missing from proof sketch: {proof_sketch}")
    if counterexample_text != "":
        raise RuntimeError(f"timeout path should not invent a counterexample: {counterexample_text}")
    if attempts_used != 1:
        raise RuntimeError(f"timeout path should stop after the first failed attempt, got {attempts_used}")
    if worker_meta != {}:
        raise RuntimeError(f"timeout path should return empty worker metadata, got {worker_meta}")

    print("run loop prover timeout test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
