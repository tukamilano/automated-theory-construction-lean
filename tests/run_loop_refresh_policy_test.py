from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


from run_loop import (
    needs_bootstrap_priority_refresh,
    normalize_open_problem_row,
    should_force_refresh_before_main_theorem,
    should_refresh_open_problem_priorities,
)


def main() -> int:
    unknown_row = normalize_open_problem_row(
        {
            "id": "op_000001",
            "stmt": "True",
            "priority": "unknown",
            "priority_rationale": "",
            "failure_count": 0,
        }
    )
    high_row = normalize_open_problem_row(
        {
            "id": "op_000002",
            "stmt": "True",
            "priority": "high",
            "priority_rationale": "test",
            "failure_count": 0,
        }
    )

    if not needs_bootstrap_priority_refresh([unknown_row]):
        raise RuntimeError("bootstrap refresh should run before any problem session when unknown priorities exist")
    if needs_bootstrap_priority_refresh([high_row]):
        raise RuntimeError("bootstrap refresh should not run when all priorities are already known")

    if should_refresh_open_problem_priorities(
        derived_theorem_count=0,
        last_refresh_theorem_count=0,
        refresh_interval=0,
    ):
        raise RuntimeError("loop refresh policy should no longer use unknown priorities after startup")
    if not should_refresh_open_problem_priorities(
        derived_theorem_count=3,
        last_refresh_theorem_count=1,
        refresh_interval=2,
    ):
        raise RuntimeError("loop refresh policy should still use theorem-count intervals")

    if not should_force_refresh_before_main_theorem(
        tracked_rows=[high_row],
        derived_theorem_count=1,
        last_refresh_theorem_count=0,
    ):
        raise RuntimeError("main theorem should force a refresh when derived theorems changed since the last refresh")
    if should_force_refresh_before_main_theorem(
        tracked_rows=[high_row],
        derived_theorem_count=1,
        last_refresh_theorem_count=1,
    ):
        raise RuntimeError("main theorem should not force a refresh when priorities already match the current derived state")
    if should_force_refresh_before_main_theorem(
        tracked_rows=[],
        derived_theorem_count=1,
        last_refresh_theorem_count=0,
    ):
        raise RuntimeError("main theorem should not force a refresh when there are no tracked problems")

    print("run loop refresh policy test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
