from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from common import next_problem_id, normalize_stmt, read_jsonl, resolve_max_attempts, write_jsonl_atomic


def apply_state_update(
    data_dir: Path,
    config_path: Path,
    problem_id: str,
    result: str,
    verify_success: bool,
    theorem_name: str | None,
    new_problems: list[str],
    max_attempts_override: int | None,
) -> dict[str, Any]:
    open_path = data_dir / "open_problems.jsonl"
    solved_path = data_dir / "solved_problems.jsonl"
    counterexamples_path = data_dir / "counterexamples.jsonl"

    open_rows = read_jsonl(open_path)
    solved_rows = read_jsonl(solved_path)
    counter_rows = read_jsonl(counterexamples_path)

    target = None
    remaining_open: list[dict[str, Any]] = []
    for row in open_rows:
        if row.get("id") == problem_id and target is None:
            target = row
        else:
            remaining_open.append(row)

    if target is None:
        raise ValueError(f"problem_id not found in open_problems.jsonl: {problem_id}")

    max_attempts = resolve_max_attempts(max_attempts_override, config_path)

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
        remaining_open.append({"id": new_id, "stmt": stmt, "src": "generated", "n": 0})
        added_problem_ids.append(new_id)

    moved_to = "open"
    updated_n = int(target.get("n", 0))

    if verify_success and result == "proof":
        if not theorem_name:
            raise ValueError("theorem_name is required when result=proof and verify_success=true")
        solved_rows.append({"id": target["id"], "stmt": target["stmt"], "thm": theorem_name})
        moved_to = "solved"
    elif verify_success and result == "counterexample":
        counter_rows.append({"id": target["id"], "stmt": target["stmt"]})
        moved_to = "counterexample"
    else:
        updated_n = min(updated_n + 1, max_attempts)
        target["n"] = updated_n
        remaining_open.append(target)

    write_jsonl_atomic(open_path, remaining_open)
    write_jsonl_atomic(solved_path, solved_rows)
    write_jsonl_atomic(counterexamples_path, counter_rows)

    return {
        "problem_id": problem_id,
        "moved_to": moved_to,
        "updated_n": updated_n,
        "max_attempts": max_attempts,
        "added_problem_ids": added_problem_ids,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Apply deterministic JSONL state updates.")
    parser.add_argument("--data-dir", default="data")
    parser.add_argument("--config", default="config/defaults.json")
    parser.add_argument("--problem-id", required=True)
    parser.add_argument("--result", required=True, choices=["proof", "counterexample", "stuck"])
    parser.add_argument("--verify-success", action="store_true")
    parser.add_argument("--theorem-name")
    parser.add_argument("--new-problem", action="append", default=[])
    parser.add_argument("--max-attempts", type=int)
    args = parser.parse_args()

    report = apply_state_update(
        data_dir=Path(args.data_dir),
        config_path=Path(args.config),
        problem_id=args.problem_id,
        result=args.result,
        verify_success=args.verify_success,
        theorem_name=args.theorem_name,
        new_problems=args.new_problem,
        max_attempts_override=args.max_attempts,
    )
    print(report)


if __name__ == "__main__":
    main()
