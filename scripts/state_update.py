from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from atc_paths import loop_archived_problems_path
from atc_paths import loop_counterexamples_path
from atc_paths import loop_open_problems_path
from atc_paths import loop_solved_problems_path
from common import (
    ARCHIVED_PROBLEMS_FILENAME,
    dedupe_problem_rows_by_stmt,
    is_active_open_problem,
    merge_archived_problem_rows,
    normalize_open_problem_row,
    partition_open_problem_rows,
    normalize_stmt,
    read_archived_problem_rows,
    read_jsonl,
    write_jsonl_atomic,
)


def apply_state_update(
    data_dir: Path,
    problem_id: str,
    result: str,
    verify_success: bool,
    theorem_name: str | None,
    result_metadata: dict[str, Any] | None = None,
    failure_threshold: int = 2,
    current_iteration: int = 0,
) -> dict[str, Any]:
    open_path = loop_open_problems_path(data_dir)
    archived_path = loop_archived_problems_path(data_dir)
    solved_path = loop_solved_problems_path(data_dir)
    counterexamples_path = loop_counterexamples_path(data_dir)

    open_rows = [normalize_open_problem_row(row) for row in read_jsonl(open_path)]
    archived_rows = read_archived_problem_rows(data_dir)
    solved_rows = read_jsonl(solved_path)
    counter_rows = read_jsonl(counterexamples_path)

    target = None
    target_was_archived = False
    remaining_open_rows: list[dict[str, Any]] = []
    for row in open_rows:
        if row.get("id") == problem_id and target is None:
            target = dict(row)
        else:
            remaining_open_rows.append(dict(row))

    if target is None:
        for row in archived_rows:
            if row.get("id") == problem_id:
                target = dict(row)
                target_was_archived = True
                break

    if target is None:
        raise ValueError(f"problem_id not found in open or archived problem sets: {problem_id}")

    moved_to = "open"
    result_details = dict(result_metadata or {})
    solved_row: dict[str, Any] | None = None
    counterexample_row: dict[str, Any] | None = None
    duplicate_stmt_rows_removed: list[dict[str, Any]] = []
    target_stmt_norm = normalize_stmt(str(target.get("stmt", "")))

    def drop_duplicate_stmt_rows() -> None:
        nonlocal remaining_open_rows, duplicate_stmt_rows_removed
        if not target_stmt_norm:
            return
        kept_rows: list[dict[str, Any]] = []
        for row in remaining_open_rows:
            if normalize_stmt(str(row.get("stmt", ""))) == target_stmt_norm:
                duplicate_stmt_rows_removed.append(dict(row))
                continue
            kept_rows.append(row)
        remaining_open_rows = kept_rows

    if verify_success and result == "proof":
        if not theorem_name:
            raise ValueError("theorem_name is required when result=proof and verify_success=true")
        solved_row = {
            "id": target["id"],
            "stmt": target["stmt"],
            "thm": theorem_name,
            **result_details,
        }
        if not any(normalize_stmt(str(row.get("stmt", ""))) == target_stmt_norm for row in solved_rows):
            solved_rows.append(solved_row)
        drop_duplicate_stmt_rows()
        moved_to = "solved"
    elif verify_success and result == "counterexample":
        counterexample_row = {
            "id": target["id"],
            "stmt": target["stmt"],
            **result_details,
        }
        if not any(normalize_stmt(str(row.get("stmt", ""))) == target_stmt_norm for row in counter_rows):
            counter_rows.append(counterexample_row)
        drop_duplicate_stmt_rows()
        moved_to = "counterexample"
    else:
        if target_was_archived:
            moved_to = "archived"
        else:
            target["failure_count"] = int(target.get("failure_count", 0) or 0) + 1
            remaining_open_rows.append(target)
            if not is_active_open_problem(target, failure_threshold=failure_threshold):
                moved_to = "archived"

    active_rows, new_archived_rows = partition_open_problem_rows(
        dedupe_problem_rows_by_stmt(remaining_open_rows),
        failure_threshold=failure_threshold,
    )
    archived_rows = merge_archived_problem_rows(archived_rows, new_archived_rows)
    write_jsonl_atomic(open_path, active_rows)
    write_jsonl_atomic(archived_path, archived_rows)
    write_jsonl_atomic(solved_path, solved_rows)
    write_jsonl_atomic(counterexamples_path, counter_rows)

    return {
        "problem_id": problem_id,
        "moved_to": moved_to,
        "target_row": target,
        "solved_row": solved_row,
        "counterexample_row": counterexample_row,
        "duplicate_stmt_rows_removed": duplicate_stmt_rows_removed,
        "current_iteration": current_iteration,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Apply deterministic JSONL state updates.")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--problem-id", required=True)
    parser.add_argument("--result", required=True, choices=["proof", "counterexample", "stuck"])
    parser.add_argument("--verify-success", action="store_true")
    parser.add_argument("--theorem-name")
    parser.add_argument("--open-problem-failure-threshold", type=int, default=2)
    args = parser.parse_args()

    report = apply_state_update(
        data_dir=Path(args.data_dir),
        problem_id=args.problem_id,
        result=args.result,
        verify_success=args.verify_success,
        theorem_name=args.theorem_name,
        failure_threshold=args.open_problem_failure_threshold,
        current_iteration=0,
    )
    print(report)


if __name__ == "__main__":
    main()
