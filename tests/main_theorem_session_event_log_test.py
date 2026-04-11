from __future__ import annotations

import json
import sys
import tempfile
import threading
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import main_theorem.main_theorem_session as main_theorem_session
from common import write_jsonl_atomic


def main() -> int:
    original_generate = main_theorem_session.request_main_theorem_candidate_set
    original_select = main_theorem_session.request_main_theorem_selection
    original_process = main_theorem_session.process_main_theorem
    original_guidance = main_theorem_session.load_current_guidance
    try:
        def fake_generate(**_kwargs):
            return (
                [
                    {
                        "candidate_rank_seed": 1,
                        "statement": "True",
                        "theorem_name_stem": "alpha_summary",
                        "docstring_summary": "alpha summary",
                        "rationale": "alpha rationale",
                        "supporting_theorems": [],
                        "missing_lemmas": [],
                        "source_problem_ids": ["op_000001"],
                        "theorem_pattern": "structure_discovery",
                        "context_note": "alpha context",
                        "conceptual_depth_note": "alpha depth",
                    },
                    {
                        "candidate_rank_seed": 2,
                        "statement": "True -> True",
                        "theorem_name_stem": "beta_bridge",
                        "docstring_summary": "beta bridge",
                        "rationale": "beta rationale",
                        "supporting_theorems": [],
                        "missing_lemmas": [],
                        "source_problem_ids": ["op_000001"],
                        "theorem_pattern": "new_theorem",
                        "context_note": "beta context",
                        "conceptual_depth_note": "beta depth",
                    },
                    {
                        "candidate_rank_seed": 3,
                        "statement": "True ∧ True",
                        "theorem_name_stem": "gamma_framework",
                        "docstring_summary": "gamma framework",
                        "rationale": "gamma rationale",
                        "supporting_theorems": [],
                        "missing_lemmas": [],
                        "source_problem_ids": ["op_000001"],
                        "theorem_pattern": "framework_introduction",
                        "context_note": "gamma context",
                        "conceptual_depth_note": "gamma depth",
                    },
                ],
                {"worker": "test"},
            )

        def fake_select(**_kwargs):
            return (
                (
                    2,
                    "beta wins",
                    [
                        {
                            "candidate_rank_seed": 2,
                            "rank": 1,
                            "decision": "select",
                            "reason": "best bridge",
                        },
                        {
                            "candidate_rank_seed": 1,
                            "rank": 2,
                            "decision": "reject",
                            "reason": "less decisive",
                        },
                        {
                            "candidate_rank_seed": 3,
                            "rank": 3,
                            "decision": "reject",
                            "reason": "too broad",
                        },
                    ],
                ),
                {"worker": "test"},
            )

        def fake_process_main_theorem(**kwargs):
            return {
                "processed": True,
                "verify_success": True,
                "candidate_id": kwargs["candidate_id"],
                "status": "ok",
            }

        main_theorem_session.request_main_theorem_candidate_set = fake_generate
        main_theorem_session.request_main_theorem_selection = fake_select
        main_theorem_session.process_main_theorem = fake_process_main_theorem
        main_theorem_session.load_current_guidance = lambda _data_dir: {}

        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            data_dir = root / "data"
            write_jsonl_atomic(data_dir / "open_problems.jsonl", [{"id": "op_000001", "stmt": "True", "src": "seed"}])
            write_jsonl_atomic(data_dir / "archived_problems.jsonl", [])
            session_events_path = data_dir / "runs" / "test-run" / "main_theorem.events.jsonl"

            report = main_theorem_session.run_main_theorem_session(
                worker_settings={},
                scratch_file=root / "Scratch.lean",
                derived_file=root / "Derived.lean",
                derived_entries=[],
                data_dir=data_dir,
                base_theory_context="",
                formalization_memory_path=data_dir / "formalization_memory.json",
                formalize_worker_settings={},
                repair_worker_settings={},
                formalizer_prompt_file="prompts/formalize/formalizer_proof.md",
                repair_prompt_file="prompts/formalize/repair_proof.md",
                generate_prompt_file="prompts/main_theorem/generate.md",
                select_prompt_file="prompts/main_theorem/select.md",
                post_expand_prompt_file="prompts/expander/post_theorem.md",
                prioritize_open_problems_worker_settings={},
                prioritize_open_problems_prompt_file="prompts/prioritizer/open_problem_prioritizer.md",
                theory_file=root / "Theory.lean",
                repo_root=REPO_ROOT,
                batch_generator_seed_count=4,
                batch_generator_open_target_min=2,
                current_iteration=7,
                skip_verify=True,
                verify_timeout_sec=10,
                formalization_retry_budget_sec=10,
                max_same_error_streak=2,
                failure_threshold=2,
                phase_logs=False,
                run_id="test-run",
                phase_attempts_path=None,
                session_events_path=session_events_path,
                compile_metrics={
                    "compile_attempt_count": 0,
                    "compile_success_count": 0,
                    "solved_per_run": 0,
                    "time_to_first_green_ms": None,
                    "wall_clock_to_last_solve_ms": None,
                },
                state_lock=threading.Lock(),
                derived_runtime_state={"generation": 0},
            )

            if report.get("session_events_file") != str(session_events_path):
                raise RuntimeError(f"unexpected session_events_file in report: {report}")
            rows = [json.loads(line) for line in session_events_path.read_text(encoding="utf-8").splitlines() if line.strip()]
            if len(rows) != 2:
                raise RuntimeError(f"expected 2 session events, got {rows}")
            if rows[0].get("event") != "main_theorem_generate_result":
                raise RuntimeError(f"unexpected first event: {rows[0]}")
            if rows[0].get("candidate_count") != 3:
                raise RuntimeError(f"missing candidate_count in generate event: {rows[0]}")
            if rows[0].get("candidates", [])[1].get("theorem_name_stem") != "beta_bridge":
                raise RuntimeError(f"missing candidate summary in generate event: {rows[0]}")
            if rows[1].get("event") != "main_theorem_select_result":
                raise RuntimeError(f"unexpected second event: {rows[1]}")
            if rows[1].get("selected_candidate", {}).get("theorem_name_stem") != "beta_bridge":
                raise RuntimeError(f"missing selected candidate summary in select event: {rows[1]}")
            if rows[1].get("ranking", [])[0].get("rank") != 1:
                raise RuntimeError(f"missing ranking summary in select event: {rows[1]}")
    finally:
        main_theorem_session.request_main_theorem_candidate_set = original_generate
        main_theorem_session.request_main_theorem_selection = original_select
        main_theorem_session.process_main_theorem = original_process
        main_theorem_session.load_current_guidance = original_guidance

    print("main theorem session event log test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
