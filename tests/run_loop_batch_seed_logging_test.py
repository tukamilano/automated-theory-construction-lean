from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import run_loop
from common import write_jsonl_atomic


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        data_dir = tmp / "data"
        data_dir.mkdir(parents=True, exist_ok=True)
        write_jsonl_atomic(data_dir / "open_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "archived_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])

        captured_events: list[dict[str, object]] = []
        original_batch_generator = run_loop.run_batch_generator_subprocess
        try:
            def fake_batch_generator(**_kwargs):
                return (
                    [
                        {
                            "stmt": "True",
                            "src": "batch_generator",
                        }
                    ],
                    "",
                )

            run_loop.run_batch_generator_subprocess = fake_batch_generator
            added_rows, error = run_loop.maybe_backfill_open_problems_from_batch_generator(
                data_dir=data_dir,
                repo_root=REPO_ROOT,
                theory_file=REPO_ROOT / "AutomatedTheoryConstruction" / "Theory.lean",
                derived_file=REPO_ROOT / "AutomatedTheoryConstruction" / "Derived.lean",
                open_problem_target_min=2,
                seed_count=3,
                reserved_problem_ids=set(),
                phase_logger=lambda **fields: captured_events.append(dict(fields)),
            )
        finally:
            run_loop.run_batch_generator_subprocess = original_batch_generator

        if error:
            raise RuntimeError(f"unexpected backfill error: {error}")
        if len(added_rows) != 1:
            raise RuntimeError(f"unexpected added_rows: {added_rows}")

        begin_events = [event for event in captured_events if event.get("phase") == "batch_seed_generation" and event.get("status") == "begin"]
        result_events = [event for event in captured_events if event.get("phase") == "batch_seed_generation" and event.get("status") == "result"]
        if len(begin_events) != 1:
            raise RuntimeError(f"missing begin event: {captured_events}")
        if len(result_events) != 1:
            raise RuntimeError(f"missing result event: {captured_events}")
        if result_events[0].get("added_count") != 1:
            raise RuntimeError(f"unexpected result event payload: {result_events[0]}")

    print("run loop batch seed logging test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
