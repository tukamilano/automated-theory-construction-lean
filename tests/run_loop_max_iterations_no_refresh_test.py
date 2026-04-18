from __future__ import annotations

import json
import sys
import tempfile
import time
from pathlib import Path
from types import SimpleNamespace


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import run_loop
from common import write_jsonl_atomic


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        data_dir = tmp / "data"
        loop_dir = data_dir / "loop"
        data_dir.mkdir(parents=True, exist_ok=True)
        loop_dir.mkdir(parents=True, exist_ok=True)
        write_jsonl_atomic(
            loop_dir / "open_problems.jsonl",
            [
                {
                    "id": "op_000001",
                    "stmt": "True",
                    "src": "smoke",
                    "priority": "high",
                    "priority_rationale": "fixture",
                    "failure_count": 0,
                },
            ],
        )
        write_jsonl_atomic(loop_dir / "archived_problems.jsonl", [])
        write_jsonl_atomic(loop_dir / "solved_problems.jsonl", [])
        write_jsonl_atomic(loop_dir / "counterexamples.jsonl", [])

        summary_path = tmp / "runs" / "run-test" / "summary.json"
        artifact_paths = {
            "summary": summary_path,
            "theory_state_history": tmp / "runs" / "run-test" / "theory_state_history.jsonl",
            "phase_attempts": tmp / "runs" / "run-test" / "phase_attempts.jsonl",
        }
        compile_metrics = {
            "solved_per_run": 0,
            "time_to_first_green_ms": None,
            "wall_clock_to_last_solve_ms": None,
            "compile_attempt_count": 0,
            "compile_success_count": 0,
        }
        args = SimpleNamespace(
            phase_logs=False,
            max_iterations=1,
            parallel_sessions=1,
            open_problem_failure_threshold=2,
            seed_count=7,
            skip_verify=True,
            max_same_error_streak=5,
            prover_retry_budget_sec=120,
            formalization_retry_budget_sec=300,
        )

        refresh_calls: list[int] = []
        original_refresh = run_loop.refresh_open_problem_state
        original_session = run_loop.run_problem_session
        try:
            def fake_refresh_open_problem_state(**kwargs):
                refresh_calls.append(int(kwargs.get("current_iteration", -1)))
                return {
                    "priority_refresh_ran": False,
                    "priority_refresh_error": "",
                    "priority_refresh_report": {
                        "batch_generator_added_problem_rows": [],
                        "batch_generator_error": "",
                        "worker_meta": {},
                    },
                }

            def fake_run_problem_session(**kwargs):
                picked = dict(kwargs["picked"])
                current_iteration = int(kwargs["current_iteration"])
                open_path = loop_dir / "open_problems.jsonl"
                open_rows = [
                    row
                    for row in run_loop.read_jsonl(open_path)
                    if str(row.get("id", "")).strip() != str(picked.get("id", "")).strip()
                ]
                write_jsonl_atomic(open_path, open_rows)
                return {
                    "kind": "problem",
                    "iteration": current_iteration,
                    "problem_id": str(picked.get("id", "")),
                    "picked": picked,
                    "report": {
                        "priority_refresh_ran": False,
                        "priority_refresh_error": "",
                        "batch_generator_added_problem_rows": [],
                    },
                    "state_update_report": {
                        "added_problem_rows": [],
                    },
                    "theorem_appended": False,
                    "theorem_name": "",
                    "target_stmt": str(picked.get("stmt", "")),
                }

            run_loop.refresh_open_problem_state = fake_refresh_open_problem_state
            run_loop.run_problem_session = fake_run_problem_session

            run_loop.run_parallel_loop(
                args=args,
                data_dir=data_dir,
                scratch_file=tmp / "Scratch.lean",
                memory_path=loop_dir / "formalization_memory.json",
                derived_path=tmp / "Derived.lean",
                repo_root=REPO_ROOT,
                base_theory_context="",
                derived_entries=[],
                run_id="run-test",
                run_started_at="2026-04-09T00:00:00Z",
                run_started_monotonic=time.monotonic(),
                artifact_paths=artifact_paths,
                compile_metrics=compile_metrics,
                worker_settings={},
                prover_worker_settings={},
                prover_statement_worker_settings={},
                formalize_worker_settings={},
                repair_worker_settings={},
                prioritize_open_problems_worker_settings={},
                derived_runtime_state={},
                record_problem_rows=lambda *_args, **_kwargs: None,
                record_theorem=lambda *_args, **_kwargs: None,
            )
        finally:
            run_loop.refresh_open_problem_state = original_refresh
            run_loop.run_problem_session = original_session

        if refresh_calls:
            raise RuntimeError(f"refresh should not run after max_iterations is exhausted, got calls={refresh_calls}")

        open_rows = run_loop.read_jsonl(loop_dir / "open_problems.jsonl")
        if open_rows:
            raise RuntimeError(f"open problems should remain empty after the budget is exhausted, got {open_rows}")

        summary = json.loads(summary_path.read_text(encoding="utf-8"))
        if summary.get("status") != "max_iterations_reached":
            raise RuntimeError(f"unexpected summary status: {summary}")

    print("run loop max iterations no refresh test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
