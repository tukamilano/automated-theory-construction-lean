from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


from run_loop import (
    has_available_solver_eligible_problem,
    is_solver_eligible_open_problem,
    needs_bootstrap_priority_refresh,
    normalize_open_problem_row,
    pick_next_available_problem,
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
    medium_row = normalize_open_problem_row(
        {
            "id": "op_000003",
            "stmt": "True",
            "priority": "medium",
            "priority_rationale": "test",
            "failure_count": 0,
        }
    )
    low_row = normalize_open_problem_row(
        {
            "id": "op_000004",
            "stmt": "True",
            "priority": "low",
            "priority_rationale": "test",
            "failure_count": 0,
        }
    )

    if not needs_bootstrap_priority_refresh([unknown_row]):
        raise RuntimeError("bootstrap refresh should run before any problem session when unknown priorities exist")
    if needs_bootstrap_priority_refresh([high_row]):
        raise RuntimeError("bootstrap refresh should not run when all priorities are already known")

    if is_solver_eligible_open_problem(unknown_row):
        raise RuntimeError("unknown-priority problems should not be solver-eligible")
    if is_solver_eligible_open_problem(low_row):
        raise RuntimeError("low-priority problems should not be solver-eligible")
    if not is_solver_eligible_open_problem(high_row):
        raise RuntimeError("high-priority problems should be solver-eligible")
    if not is_solver_eligible_open_problem(medium_row):
        raise RuntimeError("medium-priority problems should be solver-eligible")

    if pick_next_available_problem([unknown_row, low_row], reserved_problem_ids=set()) is not None:
        raise RuntimeError("solver should not pick unknown/low rows")
    picked = pick_next_available_problem([unknown_row, medium_row, high_row], reserved_problem_ids={"op_000003"})
    if picked != high_row:
        raise RuntimeError(f"solver should skip reserved and ineligible rows, got {picked}")

    if has_available_solver_eligible_problem([unknown_row, low_row], reserved_problem_ids=set()):
        raise RuntimeError("queue with only unknown/low rows should not count as solver-available")
    if not has_available_solver_eligible_problem([unknown_row, medium_row], reserved_problem_ids=set()):
        raise RuntimeError("queue with an unreserved medium row should count as solver-available")
    if has_available_solver_eligible_problem([medium_row], reserved_problem_ids={"op_000003"}):
        raise RuntimeError("reserved medium row should not count as solver-available")

    print("run loop refresh policy test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
