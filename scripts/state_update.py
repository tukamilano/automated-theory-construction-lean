from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from common import (
    next_problem_id,
    normalize_open_problem_row,
    normalize_stmt,
    read_jsonl,
    write_jsonl_atomic,
)


def apply_state_update(
    data_dir: Path,
    problem_id: str,
    result: str,
    verify_success: bool,
    theorem_name: str | None,
    new_problems: list[str],
    current_iteration: int = 0,
) -> dict[str, Any]:
    open_path = data_dir / "open_problems.jsonl"
    solved_path = data_dir / "solved_problems.jsonl"
    counterexamples_path = data_dir / "counterexamples.jsonl"

    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    solved_rows = read_jsonl(solved_path)
    counter_rows = read_jsonl(counterexamples_path)

    target = None
    remaining_open: list[dict[str, Any]] = []
    for row in open_rows:
        if row.get("id") == problem_id and target is None:
            target = dict(row)
        else:
            remaining_open.append(dict(row))

    if target is None:
        raise ValueError(f"problem_id not found in open_problems.jsonl: {problem_id}")

    seen_norms = {
        normalize_stmt(str(row.get("stmt", "")))
        for row in (remaining_open + solved_rows + counter_rows)
        if row.get("stmt")
    }

    all_ids = [str(row.get("id", "")) for row in open_rows + solved_rows + counter_rows]
    added_problem_ids: list[str] = []
    for stmt in new_problems:
        norm = normalize_stmt(stmt)
        if not norm or norm in seen_norms:
            continue
        new_id = next_problem_id(all_ids)
        all_ids.append(new_id)
        seen_norms.add(norm)
        remaining_open.append(
            normalize_open_problem_row(
                {
                    "id": new_id,
                    "stmt": stmt,
                    "src": "generated",
                    "priority": "unknown",
                }
            )
        )
        added_problem_ids.append(new_id)

    moved_to = "open"

    if verify_success and result == "proof":
        if not theorem_name:
            raise ValueError("theorem_name is required when result=proof and verify_success=true")
        solved_rows.append({"id": target["id"], "stmt": target["stmt"], "thm": theorem_name})
        moved_to = "solved"
    elif verify_success and result == "counterexample":
        counter_rows.append({"id": target["id"], "stmt": target["stmt"]})
        moved_to = "counterexample"
    else:
        target["failure_count"] = int(target.get("failure_count", 0) or 0) + 1
        remaining_open.append(target)

    write_jsonl_atomic(open_path, remaining_open)
    write_jsonl_atomic(solved_path, solved_rows)
    write_jsonl_atomic(counterexamples_path, counter_rows)

    return {
        "problem_id": problem_id,
        "moved_to": moved_to,
        "added_problem_ids": added_problem_ids,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Apply deterministic JSONL state updates.")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--problem-id", required=True)
    parser.add_argument("--result", required=True, choices=["proof", "counterexample", "stuck"])
    parser.add_argument("--verify-success", action="store_true")
    parser.add_argument("--theorem-name")
    parser.add_argument("--new-problem", action="append", default=[])
    args = parser.parse_args()

    report = apply_state_update(
        data_dir=Path(args.data_dir),
        problem_id=args.problem_id,
        result=args.result,
        verify_success=args.verify_success,
        theorem_name=args.theorem_name,
        new_problems=args.new_problem,
        current_iteration=0,
    )
    print(report)


if __name__ == "__main__":
    main()
