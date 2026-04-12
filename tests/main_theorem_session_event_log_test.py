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
from guidance import build_guidance_context


def main() -> int:
    original_suggest = main_theorem_session.request_main_theorem_suggestion
    original_retrieve = main_theorem_session.request_main_theorem_retrieval
    original_map = main_theorem_session.request_main_theorem_mapping
    original_evaluate = main_theorem_session.request_main_theorem_evaluation
    original_process = main_theorem_session.process_main_theorem
    original_guidance = main_theorem_session.load_current_guidance
    original_materials_sync = main_theorem_session.ensure_materials_cache_current
    try:
        materials_sync_calls: list[str] = []

        def fake_suggest(**_kwargs):
            return (
                {
                    "candidate_id": "mt_main_theorem_01",
                    "candidate_rank_seed": 1,
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
                {"worker": "test"},
            )

        def fake_retrieve(**_kwargs):
            return (
                {
                    "candidate_id": "mt_main_theorem_01",
                    "closest_items": [
                        {
                            "reference": "beta paper",
                            "kind": "source_link",
                            "relevance": "closest bridge anchor",
                            "confidence": "high",
                        }
                    ],
                    "research_line": "beta bridge line",
                    "coverage_assessment": "sufficient",
                    "missing_angles": [],
                    "need_supplemental_retrieval": False,
                },
                {"worker": "test"},
            )

        def fake_map(**_kwargs):
            return (
                {
                    "candidate_id": "mt_main_theorem_01",
                    "closest_baseline": "beta baseline",
                    "relations": [
                        {
                            "reference": "beta paper",
                            "overlap": "same bridge family",
                            "delta": "sharper title-level bridge",
                            "delta_materiality": "substantial",
                        }
                    ],
                    "overall_novelty_risk": "medium",
                    "variant_objection": "could still look like a nearby bridge variant",
                },
                {"worker": "test"},
            )

        def fake_evaluate(**_kwargs):
            return (
                {
                    "candidate_id": "mt_main_theorem_01",
                    "novelty": "medium",
                    "significance": "high",
                    "paper_unit_viability": "yes",
                    "strongest_objection": "could still look too close to baseline",
                    "objection_answerable": "yes",
                    "minimal_publishable_unit": "bridge note",
                    "salvage_plan": "",
                    "verdict": "pass",
                    "reason": "beta wins",
                },
                {"worker": "test"},
            )

        def fake_process_main_theorem(**kwargs):
            return {
                "processed": True,
                "verify_success": True,
                "candidate_id": kwargs["candidate_id"],
                "status": "ok",
            }

        main_theorem_session.request_main_theorem_suggestion = fake_suggest
        main_theorem_session.request_main_theorem_retrieval = fake_retrieve
        main_theorem_session.request_main_theorem_mapping = fake_map
        main_theorem_session.request_main_theorem_evaluation = fake_evaluate
        main_theorem_session.process_main_theorem = fake_process_main_theorem
        main_theorem_session.ensure_materials_cache_current = lambda materials_dir, **_kwargs: (
            materials_sync_calls.append(str(materials_dir)),
            {"materials_dir": str(materials_dir), "derived": {"reports": []}, "fetch": {"entries": []}, "extract": {"entries": []}},
        )[1]
        main_theorem_session.load_current_guidance = lambda _data_dir: build_guidance_context(
            theory_state={},
            research_agenda={},
            materials={
                "source_link_entries": [
                    {
                        "label": "beta paper",
                        "url": "https://example.com/beta.pdf",
                        "note": "",
                        "source_kind": "repository_pdf",
                        "retrieval_priority": "high",
                        "direct_reading_access": "direct_fulltext",
                        "download_path": "/tmp/materials_cache/downloads/beta.pdf",
                        "paper_record_path": "/tmp/materials_cache/papers/beta.json",
                    }
                ],
                "paper_cache": [
                    {
                        "source_id": "beta_source",
                        "title": "beta paper",
                        "source_url": "https://example.com/beta.pdf",
                        "extract_confidence": "high",
                        "source_kind": "repository_pdf",
                        "retrieval_priority": "high",
                        "direct_reading_access": "direct_fulltext",
                        "abstract": "beta bridge result",
                        "chunks": [
                            {
                                "chunk_id": "chunk_001",
                                "section": "Abstract",
                                "page": None,
                                "text": "beta bridge theorem",
                            }
                        ],
                        "paper_record_relpath": "papers/beta.json",
                        "paper_record_path": "/tmp/materials_cache/papers/beta.json",
                        "download_relpath": "downloads/beta.pdf",
                        "download_path": "/tmp/materials_cache/downloads/beta.pdf",
                    }
                ],
            },
        )

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
                suggester_prompt_file="prompts/main_theorem/suggester.md",
                retriever_prompt_file="prompts/main_theorem/retrieve.md",
                mapper_prompt_file="prompts/main_theorem/map.md",
                evaluator_prompt_file="prompts/main_theorem/evaluate.md",
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
                main_theorem_retry_budget_sec=10,
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
            if not materials_sync_calls:
                raise RuntimeError("main theorem session should trigger materials sync before loading guidance")
            rows = [json.loads(line) for line in session_events_path.read_text(encoding="utf-8").splitlines() if line.strip()]
            if len(rows) != 4:
                raise RuntimeError(f"expected 4 session events, got {rows}")
            if rows[0].get("event") != "main_theorem_suggest_result":
                raise RuntimeError(f"unexpected first event: {rows[0]}")
            if rows[0].get("candidate", {}).get("theorem_name_stem") != "beta_bridge":
                raise RuntimeError(f"missing candidate summary in suggest event: {rows[0]}")
            if rows[1].get("event") != "main_theorem_retrieve_result":
                raise RuntimeError(f"unexpected second event: {rows[1]}")
            if rows[1].get("closest_items", [])[0].get("reference") != "beta paper":
                raise RuntimeError(f"missing retrieval summary in retrieve event: {rows[1]}")
            source_access = rows[1].get("source_access", {})
            if source_access.get("paper_access", [])[0].get("download_path") != "/tmp/materials_cache/downloads/beta.pdf":
                raise RuntimeError(f"missing local paper access in retrieve event: {rows[1]}")
            if source_access.get("source_link_access", [])[0].get("paper_record_path") != "/tmp/materials_cache/papers/beta.json":
                raise RuntimeError(f"missing local source-link access in retrieve event: {rows[1]}")
            if rows[2].get("event") != "main_theorem_map_result":
                raise RuntimeError(f"unexpected third event: {rows[2]}")
            if rows[2].get("closest_baseline") != "beta baseline":
                raise RuntimeError(f"missing mapping summary in map event: {rows[2]}")
            if rows[3].get("event") != "main_theorem_evaluate_result":
                raise RuntimeError(f"unexpected fourth event: {rows[3]}")
            if rows[3].get("verdict") != "pass":
                raise RuntimeError(f"missing evaluation summary in evaluate event: {rows[3]}")
    finally:
        main_theorem_session.request_main_theorem_suggestion = original_suggest
        main_theorem_session.request_main_theorem_retrieval = original_retrieve
        main_theorem_session.request_main_theorem_mapping = original_map
        main_theorem_session.request_main_theorem_evaluation = original_evaluate
        main_theorem_session.process_main_theorem = original_process
        main_theorem_session.load_current_guidance = original_guidance
        main_theorem_session.ensure_materials_cache_current = original_materials_sync

    print("main theorem session event log test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
