from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from common import (
    ARCHIVED_PROBLEMS_FILENAME,
    is_active_open_problem,
    next_problem_id,
    normalize_open_problem_row,
    partition_open_problem_rows,
    normalize_stmt,
    read_archived_problem_rows,
    read_jsonl,
    write_jsonl_atomic,
)


def enqueue_new_problems(
    data_dir: Path,
    new_problems: list[str],
    *,
    source: str = "generated",
    source_details: dict[str, Any] | None = None,
    failure_threshold: int = 2,
) -> dict[str, Any]:
    open_path = data_dir / "open_problems.jsonl"
    archived_path = data_dir / ARCHIVED_PROBLEMS_FILENAME
    solved_path = data_dir / "solved_problems.jsonl"
    counterexamples_path = data_dir / "counterexamples.jsonl"

    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    archived_rows = read_archived_problem_rows(data_dir)
    solved_rows = read_jsonl(solved_path)
    counter_rows = read_jsonl(counterexamples_path)

    tracked_rows = [dict(row) for row in open_rows + archived_rows]
    seen_norms = {
        normalize_stmt(str(row.get("stmt", "")))
        for row in (tracked_rows + solved_rows + counter_rows)
        if row.get("stmt")
    }
    all_ids = [str(row.get("id", "")) for row in open_rows + archived_rows + solved_rows + counter_rows]

    added_problem_ids: list[str] = []
    added_problem_rows: list[dict[str, Any]] = []
    normalized_source_details = dict(source_details or {})
    for stmt in new_problems:
        norm = normalize_stmt(stmt)
        if not norm or norm in seen_norms:
            continue
        new_id = next_problem_id(all_ids)
        all_ids.append(new_id)
        seen_norms.add(norm)
        new_row = normalize_open_problem_row(
            {
                "id": new_id,
                "stmt": stmt,
                "src": source,
                "priority": "unknown",
                **normalized_source_details,
            }
        )
        tracked_rows.append(new_row)
        added_problem_ids.append(new_id)
        added_problem_rows.append(dict(new_row))

    active_rows, archived_rows = partition_open_problem_rows(
        tracked_rows,
        failure_threshold=failure_threshold,
    )
    write_jsonl_atomic(open_path, active_rows)
    write_jsonl_atomic(archived_path, archived_rows)

    return {
        "added_problem_ids": added_problem_ids,
        "added_problem_rows": added_problem_rows,
        "active_open_problem_count": len(active_rows),
        "archived_problem_count": len(archived_rows),
    }


def apply_state_update(
    data_dir: Path,
    problem_id: str,
    result: str,
    verify_success: bool,
    theorem_name: str | None,
    new_problems: list[str],
    source_details: dict[str, Any] | None = None,
    result_metadata: dict[str, Any] | None = None,
    failure_threshold: int = 2,
    current_iteration: int = 0,
) -> dict[str, Any]:
    open_path = data_dir / "open_problems.jsonl"
    archived_path = data_dir / ARCHIVED_PROBLEMS_FILENAME
    solved_path = data_dir / "solved_problems.jsonl"
    counterexamples_path = data_dir / "counterexamples.jsonl"

    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    archived_rows = read_archived_problem_rows(data_dir)
    solved_rows = read_jsonl(solved_path)
    counter_rows = read_jsonl(counterexamples_path)

    target = None
    remaining_tracked: list[dict[str, Any]] = []
    for row in open_rows + archived_rows:
        if row.get("id") == problem_id and target is None:
            target = dict(row)
        else:
            remaining_tracked.append(dict(row))

    if target is None:
        raise ValueError(f"problem_id not found in open or archived problem sets: {problem_id}")

    seen_norms = {
        normalize_stmt(str(row.get("stmt", "")))
        for row in (remaining_tracked + solved_rows + counter_rows)
        if row.get("stmt")
    }

    all_ids = [str(row.get("id", "")) for row in open_rows + archived_rows + solved_rows + counter_rows]
    added_problem_ids: list[str] = []
    added_problem_rows: list[dict[str, Any]] = []
    normalized_source_details = dict(source_details or {})
    for stmt in new_problems:
        norm = normalize_stmt(stmt)
        if not norm or norm in seen_norms:
            continue
        new_id = next_problem_id(all_ids)
        all_ids.append(new_id)
        seen_norms.add(norm)
        new_row = normalize_open_problem_row(
            {
                "id": new_id,
                "stmt": stmt,
                "src": "generated",
                "priority": "unknown",
                **normalized_source_details,
            }
        )
        remaining_tracked.append(new_row)
        added_problem_ids.append(new_id)
        added_problem_rows.append(dict(new_row))

    moved_to = "open"
    result_details = dict(result_metadata or {})
    solved_row: dict[str, Any] | None = None
    counterexample_row: dict[str, Any] | None = None

    if verify_success and result == "proof":
        if not theorem_name:
            raise ValueError("theorem_name is required when result=proof and verify_success=true")
        solved_row = {
            "id": target["id"],
            "stmt": target["stmt"],
            "thm": theorem_name,
            **result_details,
        }
        solved_rows.append(solved_row)
        moved_to = "solved"
    elif verify_success and result == "counterexample":
        counterexample_row = {
            "id": target["id"],
            "stmt": target["stmt"],
            **result_details,
        }
        counter_rows.append(counterexample_row)
        moved_to = "counterexample"
    else:
        target["failure_count"] = int(target.get("failure_count", 0) or 0) + 1
        remaining_tracked.append(target)
        if not is_active_open_problem(target, failure_threshold=failure_threshold):
            moved_to = "archived"

    active_rows, archived_rows = partition_open_problem_rows(
        remaining_tracked,
        failure_threshold=failure_threshold,
    )
    write_jsonl_atomic(open_path, active_rows)
    write_jsonl_atomic(archived_path, archived_rows)
    write_jsonl_atomic(solved_path, solved_rows)
    write_jsonl_atomic(counterexamples_path, counter_rows)

    return {
        "problem_id": problem_id,
        "moved_to": moved_to,
        "added_problem_ids": added_problem_ids,
        "added_problem_rows": added_problem_rows,
        "target_row": target,
        "solved_row": solved_row,
        "counterexample_row": counterexample_row,
        "current_iteration": current_iteration,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Apply deterministic JSONL state updates.")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--problem-id", required=True)
    parser.add_argument("--result", required=True, choices=["proof", "counterexample", "stuck"])
    parser.add_argument("--verify-success", action="store_true")
    parser.add_argument("--theorem-name")
    parser.add_argument("--new-problem", action="append", default=[])
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    args = parser.parse_args()

    report = apply_state_update(
        data_dir=Path(args.data_dir),
        problem_id=args.problem_id,
        result=args.result,
        verify_success=args.verify_success,
        theorem_name=args.theorem_name,
        new_problems=args.new_problem,
        failure_threshold=args.open_problem_failure_threshold,
        current_iteration=0,
    )
    print(report)


if __name__ == "__main__":
    main()
