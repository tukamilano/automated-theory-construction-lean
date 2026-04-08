from __future__ import annotations

import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import run_loop
from common import read_jsonl, write_jsonl_atomic
from state_update import apply_state_update


def test_priority_refresh_keeps_archived_rows_archived() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        data_dir = Path(tmpdir)
        write_jsonl_atomic(
            data_dir / "open_problems.jsonl",
            [
                {
                    "id": "op_000001",
                    "stmt": "True",
                    "priority": "medium",
                    "priority_rationale": "seed",
                    "failure_count": 0,
                }
            ],
        )
        write_jsonl_atomic(
            data_dir / "archived_problems.jsonl",
            [
                {
                    "id": "op_000002",
                    "stmt": "False",
                    "priority": "low",
                    "priority_rationale": "already archived",
                    "failure_count": 2,
                }
            ],
        )

        original_request = run_loop.request_open_problem_priorities
        original_load_prompt_text = run_loop.load_prompt_text
        original_load_theory_state = run_loop.load_theory_state
        try:
            run_loop.load_prompt_text = lambda _path: ""
            run_loop.load_theory_state = lambda _data_dir: {}

            def fake_request_open_problem_priorities(**_kwargs):
                return (
                    [
                        {
                            "problem_id": "op_000001",
                            "priority": "low",
                            "rationale": "archive this active problem",
                        },
                        {
                            "problem_id": "op_000002",
                            "priority": "high",
                            "rationale": "this would revive archived rows if the bug regressed",
                        },
                    ],
                    "test snapshot",
                    {"label": "test", "guidance": "test", "rationale": "test"},
                    {
                        "desired_summary_changes": [],
                        "current_bottlenecks": [],
                        "overexplored_patterns": [],
                        "missing_bridges": [],
                        "agenda_pressure": [],
                    },
                    {"worker": "archive_write_only_test"},
                )

            run_loop.request_open_problem_priorities = fake_request_open_problem_priorities
            ran, error, _report = run_loop.force_refresh_open_problem_priorities(
                data_dir=data_dir,
                worker_settings={},
                prioritizer_prompt_file="unused",
                derived_entries=[],
                current_iteration=1,
                failure_threshold=2,
                run_id="test_run",
                theory_state_history_path=None,
            )
        finally:
            run_loop.request_open_problem_priorities = original_request
            run_loop.load_prompt_text = original_load_prompt_text
            run_loop.load_theory_state = original_load_theory_state

        if not ran or error:
            raise RuntimeError(f"priority refresh unexpectedly failed: {error}")

        open_rows = read_jsonl(data_dir / "open_problems.jsonl")
        archived_rows = read_jsonl(data_dir / "archived_problems.jsonl")
        if open_rows:
            raise RuntimeError(f"expected no active open rows after archival, got: {open_rows}")

        archived_ids = [str(row.get("id", "")) for row in archived_rows]
        if archived_ids != ["op_000002", "op_000001"]:
            raise RuntimeError(f"archived rows should be preserved and append-only, got ids: {archived_ids}")


def test_state_update_does_not_remove_archived_rows() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        data_dir = Path(tmpdir)
        write_jsonl_atomic(data_dir / "open_problems.jsonl", [])
        write_jsonl_atomic(
            data_dir / "archived_problems.jsonl",
            [
                {
                    "id": "op_000010",
                    "stmt": "True",
                    "priority": "low",
                    "priority_rationale": "archived",
                    "failure_count": 2,
                }
            ],
        )
        write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])

        report = apply_state_update(
            data_dir=data_dir,
            problem_id="op_000010",
            result="proof",
            verify_success=True,
            theorem_name="archived_problem_proved",
            failure_threshold=2,
            current_iteration=1,
        )
        if report.get("moved_to") != "solved":
            raise RuntimeError(f"unexpected move target for archived solved problem: {report}")

        archived_rows = read_jsonl(data_dir / "archived_problems.jsonl")
        solved_rows = read_jsonl(data_dir / "solved_problems.jsonl")
        if [str(row.get("id", "")) for row in archived_rows] != ["op_000010"]:
            raise RuntimeError(f"archived problem should remain in archive after solve, got: {archived_rows}")
        if [str(row.get("id", "")) for row in solved_rows] != ["op_000010"]:
            raise RuntimeError(f"solved row not recorded correctly, got: {solved_rows}")


def test_backfill_does_not_duplicate_pending_expand_candidates() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        data_dir = Path(tmpdir)
        write_jsonl_atomic(data_dir / "open_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "archived_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])
        write_jsonl_atomic(
            data_dir / "expand_candidates.jsonl",
            [
                {
                    "id": "op_000010",
                    "stmt": "True",
                    "src": "expand",
                    "priority": "unknown",
                    "priority_rationale": "",
                    "failure_count": 0,
                }
            ],
        )

        original_batch_generator = run_loop.run_batch_generator_subprocess
        try:
            def fake_batch_generator(**_kwargs):
                return (
                    [
                        {
                            "id": "op_000001",
                            "stmt": "True",
                            "src": "batch_generator",
                            "priority": "unknown",
                            "priority_rationale": "",
                            "failure_count": 0,
                        }
                    ],
                    "",
                )

            run_loop.run_batch_generator_subprocess = fake_batch_generator
            added_rows, error = run_loop.maybe_backfill_open_problems_from_batch_generator(
                data_dir=data_dir,
                repo_root=REPO_ROOT,
                theory_file=Path("AutomatedTheoryConstruction/Theory.lean"),
                derived_file=Path("AutomatedTheoryConstruction/Derived.lean"),
                open_problem_target_min=1,
                seed_count=4,
            )
        finally:
            run_loop.run_batch_generator_subprocess = original_batch_generator

        if error:
            raise RuntimeError(f"unexpected backfill error: {error}")
        if added_rows:
            raise RuntimeError(f"batch generator should not duplicate a pending expand candidate, got: {added_rows}")

        open_rows = read_jsonl(data_dir / "open_problems.jsonl")
        if open_rows:
            raise RuntimeError(f"unexpected open problems after duplicate backfill attempt: {open_rows}")


def test_priority_refresh_promotes_high_expand_candidates() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        data_dir = Path(tmpdir)
        write_jsonl_atomic(data_dir / "open_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "archived_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "solved_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])
        write_jsonl_atomic(
            data_dir / "expand_candidates.jsonl",
            [
                {
                    "id": "op_000003",
                    "stmt": "True",
                    "src": "expand",
                    "mode": "bridge",
                    "summary_delta": "strong bridge candidate",
                    "priority": "unknown",
                    "priority_rationale": "",
                    "failure_count": 0,
                }
            ],
        )

        original_request = run_loop.request_open_problem_priorities
        original_load_prompt_text = run_loop.load_prompt_text
        try:
            run_loop.load_prompt_text = lambda _path: ""

            def fake_request_open_problem_priorities(**_kwargs):
                return (
                    [
                        {
                            "problem_id": "op_000003",
                            "priority": "high",
                            "rationale": "promote expand candidate now",
                        }
                    ],
                    "test snapshot",
                    {"label": "test", "guidance": "test", "rationale": "test"},
                    {
                        "desired_summary_changes": [],
                        "current_bottlenecks": [],
                        "overexplored_patterns": [],
                        "missing_bridges": [],
                        "agenda_pressure": [],
                    },
                    {"worker": "archive_write_only_test"},
                )

            run_loop.request_open_problem_priorities = fake_request_open_problem_priorities
            ran, error, report = run_loop.force_refresh_open_problem_priorities(
                data_dir=data_dir,
                worker_settings={},
                prioritizer_prompt_file="unused",
                derived_entries=[],
                current_iteration=1,
                failure_threshold=2,
                run_id="test_run",
                theory_state_history_path=None,
            )
        finally:
            run_loop.request_open_problem_priorities = original_request
            run_loop.load_prompt_text = original_load_prompt_text

        if not ran or error:
            raise RuntimeError(f"priority refresh unexpectedly failed: {error}")

        open_rows = read_jsonl(data_dir / "open_problems.jsonl")
        if [str(row.get("id", "")) for row in open_rows] != ["op_000003"]:
            raise RuntimeError(f"expand candidate was not promoted into open queue: {open_rows}")

        expand_rows = read_jsonl(data_dir / "expand_candidates.jsonl")
        if expand_rows:
            raise RuntimeError(f"promoted expand candidate should be removed from expand_candidates: {expand_rows}")

        promoted_rows = report.get("promoted_expand_rows", [])
        if [str(row.get("id", "")) for row in promoted_rows] != ["op_000003"]:
            raise RuntimeError(f"priority refresh report missing promoted expand row: {report}")


def main() -> int:
    test_priority_refresh_keeps_archived_rows_archived()
    test_state_update_does_not_remove_archived_rows()
    test_backfill_does_not_duplicate_pending_expand_candidates()
    test_priority_refresh_promotes_high_expand_candidates()
    print("archive write only test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
