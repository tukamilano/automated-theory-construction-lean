from __future__ import annotations

import json
import sys
import tempfile
import threading
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import paper_claim.paper_claim_session as paper_claim_session
from common import write_jsonl_atomic
from guidance import build_guidance_context


def main() -> int:
    original_problem_design_cluster = paper_claim_session.request_problem_design_clusters
    original_problem_design_contextualize = paper_claim_session.request_problem_design_contextualization
    original_problem_design_core_extract = paper_claim_session.request_problem_design_core_extract
    original_paper_claim_select = paper_claim_session.request_paper_claim_select
    original_paper_claim_retrieve = paper_claim_session.request_paper_claim_retrieval
    original_paper_claim_map = paper_claim_session.request_paper_claim_mapping
    original_paper_claim_plan = paper_claim_session.request_paper_claim_plan
    original_process = paper_claim_session.process_paper_claim_formalization_plan
    original_guidance = paper_claim_session.load_current_guidance
    original_materials_sync = paper_claim_session.ensure_materials_cache_current
    try:
        materials_sync_calls: list[str] = []

        def fake_problem_design_cluster(**_kwargs):
            return (
                [
                    {
                        "cluster_id": "cluster_001",
                        "cluster_theme": "semantic bridge cluster",
                        "cluster_summary": "visible theorems already cluster around one bridge family",
                        "member_theorems": [{"name": "visible_bridge", "statement": "True"}],
                        "objects": ["reachable region"],
                        "invariants": ["equivalence"],
                        "algorithms": ["fold"],
                        "suspected_support_layer": ["bounded convergence"],
                    }
                ],
                {"worker": "test"},
            )

        def fake_problem_design_contextualize(**_kwargs):
            return (
                {
                    "cluster_id": "cluster_001",
                    "cluster_theme": "semantic bridge cluster",
                    "external_positioning": {
                        "closest_baselines": [
                            {
                                "reference": "beta paper",
                                "what_it_already_owns": "beta baseline already owns order-insensitivity pressure",
                                "evidence_strength": "direct",
                                "danger_level": "high",
                            }
                        ],
                        "baseline_summary": "beta summary",
                        "what_counts_as_real_delta": ["beta theorem-level external delta"],
                        "unresolved_baseline_risks": ["beta unresolved risk"],
                        "external_baseline_pressure": "high",
                    },
                    "paper_core_analysis": {
                        "no_go_faces": ["beta packaged theorem"],
                        "possible_gap_types": ["boundary"],
                        "most_plausible_gap": "beta sharp boundary",
                        "gap_rationale": "beta rationale",
                        "headline_viability": "promising",
                    },
                    "proposal_guidance": {
                        "allowed_headline_directions": ["beta direct theorem face"],
                        "discouraged_headline_directions": ["beta packaging face"],
                        "must_clear_for_novelty": ["beta novelty gate"],
                    },
                },
                {"worker": "test"},
            )

        def fake_problem_design_core_extract(**_kwargs):
            return (
                {
                    "problem_id": "pd_paper_claim_01",
                    "cluster_id": "cluster_001",
                    "headline_claim": "every admissible partial elimination state computes the same intrinsic semantic object",
                    "core_mathematical_content": "the visible semantic package is governed by one intrinsic partial-state invariant",
                    "literature_context": {
                        "closest_baseline": "beta paper",
                        "routine_reading_risk": "a weaker face could look like fold packaging",
                        "possible_opening": "state the invariant directly rather than through execution machinery",
                    },
                    "supporting_claims": ["final uniqueness corollary", "terminal-frontier failure boundary"],
                    "no_go_faces": ["fold correctness theorem"],
                    "proof_assets": ["bounded convergence", "reverse-topological bookkeeping"],
                    "why_this_face": "the visible theory already clusters around this comparison",
                },
                {"worker": "test"},
            )

        def fake_paper_claim_retrieve(**_kwargs):
            return (
                {
                    "problem_id": "pd_paper_claim_01",
                    "closest_items": [
                        {
                            "reference": "beta paper",
                            "kind": "source_link",
                            "relevance": "closest bridge anchor",
                            "confidence": "high",
                        }
                    ],
                    "directly_read_evidence": [
                        {
                            "reference": "beta paper",
                            "evidence": "direct reading shows broad algorithmic pressure but not this exact invariant theorem face",
                            "supports": "the invariant framing still looks open",
                            "confidence": "high",
                        }
                    ],
                    "coverage_assessment": "sufficient",
                    "missing_angles": [],
                    "need_supplemental_retrieval": False,
                },
                {"worker": "test"},
            )

        def fake_paper_claim_select(**_kwargs):
            return (
                {
                    "selection_id": "paper_claim_select_01",
                    "selected_problem_id": "pd_paper_claim_01",
                    "selection_note": "beta dossier is currently the closest to a paper-publishable unit",
                    "planning_focus": "plan this as a short invariant-first package",
                    "assessments": [
                        {
                            "problem_id": "pd_paper_claim_01",
                            "paper_publishable_fit": "high",
                            "selected": True,
                            "why_selected": "best balance of theorem face and baseline delta",
                            "why_not_selected": "",
                        }
                    ],
                },
                {"worker": "test"},
            )

        def fake_paper_claim_map(**_kwargs):
            return (
                {
                    "problem_id": "pd_paper_claim_01",
                    "closest_baseline": "beta baseline",
                    "relations": [
                        {
                            "reference": "beta paper",
                            "overlap": "same bridge family",
                            "delta": "sharper title-level bridge",
                            "delta_materiality": "substantial",
                        }
                    ],
                    "theorem_face_assessment": "natural if fold packaging stays below the headline",
                    "baseline_delta": "state the intrinsic invariant directly",
                    "outsider_risk": "could still look like a nearby bridge variant",
                },
                {"worker": "test"},
            )

        def fake_paper_claim_plan(**_kwargs):
            return (
                {
                    "plan_id": "paper_claim_plan_for_pd_paper_claim_01",
                    "selected_problem_id": "pd_paper_claim_01",
                    "headline": "intrinsic semantic invariant on partial elimination states",
                    "package_strategy": "split the package into an invariant lemma, then the headline theorem, then corollaries",
                    "theorem_units": [
                        {
                            "unit_id": "u1",
                            "role": "entry_lemma",
                            "kind": "lemma",
                            "name_stem": "beta_partial_state_invariant",
                            "statement": "A concise invariant lemma for partial elimination states.",
                            "docstring_summary": "beta first target",
                            "purpose": "entry lemma that unlocks the package headline",
                            "uses_existing_results": [],
                            "needs_new_ingredients": [],
                            "proof_idea": [
                                "First isolate the support theorem.",
                                "Then rewrite the invariant through it.",
                                "Finally conclude the target.",
                            ],
                            "unlocks": ["u2"],
                        },
                        {
                            "unit_id": "u2",
                            "role": "headline_theorem",
                            "kind": "theorem",
                            "name_stem": "beta_visible_headline",
                            "statement": "The visible theorem derived from the invariant.",
                            "docstring_summary": "beta headline",
                            "purpose": "headline theorem for the selected package",
                            "uses_existing_results": ["beta_partial_state_invariant"],
                            "needs_new_ingredients": [],
                            "proof_idea": [
                                "Apply the entry lemma at the full construction.",
                                "Compare with the visible semantic description.",
                                "Conclude the headline theorem.",
                            ],
                            "unlocks": [],
                        },
                    ],
                    "formalization_order": ["u1", "u2"],
                },
                {"worker": "test"},
            )

        def fake_process_paper_claim_formalization_plan(**kwargs):
            return {
                "processed": True,
                "verify_success": True,
                "candidate_id": kwargs["candidate_id"],
                "status": "proved",
                "theorem_name": "paper_claim_beta_visible_headline",
            }

        paper_claim_session.request_problem_design_clusters = fake_problem_design_cluster
        paper_claim_session.request_problem_design_contextualization = fake_problem_design_contextualize
        paper_claim_session.request_problem_design_core_extract = fake_problem_design_core_extract
        paper_claim_session.request_paper_claim_select = fake_paper_claim_select
        paper_claim_session.request_paper_claim_retrieval = fake_paper_claim_retrieve
        paper_claim_session.request_paper_claim_mapping = fake_paper_claim_map
        paper_claim_session.request_paper_claim_plan = fake_paper_claim_plan
        paper_claim_session.process_paper_claim_formalization_plan = fake_process_paper_claim_formalization_plan
        paper_claim_session.ensure_materials_cache_current = lambda materials_dir, **_kwargs: (
            materials_sync_calls.append(str(materials_dir)),
            {"materials_dir": str(materials_dir), "derived": {"reports": []}, "fetch": {"entries": []}, "extract": {"entries": []}},
        )[1]
        paper_claim_session.load_current_guidance = lambda _data_dir: build_guidance_context(
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
            write_jsonl_atomic(data_dir / "loop" / "open_problems.jsonl", [{"id": "op_000001", "stmt": "True", "src": "seed"}])
            write_jsonl_atomic(data_dir / "loop" / "archived_problems.jsonl", [])
            session_events_path = data_dir / "paper_claim" / "test-run" / "paper_claim.events.jsonl"

            report = paper_claim_session.run_paper_claim_session(
                worker_settings={},
                scratch_file=root / "Scratch.lean",
                derived_file=root / "Derived.lean",
                derived_entries=[],
                data_dir=data_dir,
                base_theory_context="",
                formalize_worker_settings={},
                paper_claim_selector_prompt_file="prompts/paper_claim/select.md",
                paper_claim_retriever_prompt_file="prompts/paper_claim/retrieve.md",
                paper_claim_mapper_prompt_file="prompts/paper_claim/map.md",
                paper_claim_planner_prompt_file="prompts/paper_claim/plan.md",
                paper_claim_codex_prove_prompt_file=".codex/workflow/paper_claim_codex_prove.md",
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
                paper_claim_retry_budget_sec=10,
                failure_threshold=2,
                phase_logs=False,
                run_id="test-run",
                phase_attempts_path=None,
                session_events_path=session_events_path,
                state_lock=threading.Lock(),
                derived_runtime_state={"generation": 0},
            )

            if report.get("session_events_file") != str(session_events_path):
                raise RuntimeError(f"unexpected session_events_file in report: {report}")
            if not materials_sync_calls:
                raise RuntimeError("paper claim session should trigger materials sync before loading guidance")
            rows = [json.loads(line) for line in session_events_path.read_text(encoding="utf-8").splitlines() if line.strip()]
            if len(rows) < 9:
                raise RuntimeError(f"expected at least 9 session events, got {rows}")

            def require_event(name: str) -> dict[str, object]:
                for row in rows:
                    if row.get("event") == name:
                        return row
                raise RuntimeError(f"missing session event {name}: {rows}")

            cluster_result = require_event("problem_design_cluster_result")
            if cluster_result.get("clusters", [])[0].get("cluster_id") != "cluster_001":
                raise RuntimeError(f"missing cluster summary in result event: {cluster_result}")
            contextualize_result = require_event("problem_design_contextualize_result")
            if contextualize_result.get("headline_viability") != "promising":
                raise RuntimeError(f"missing contextualization summary in result event: {contextualize_result}")
            dossier_summary = require_event("problem_design_dossier_summary")
            if dossier_summary.get("problem_id") != "pd_paper_claim_01":
                raise RuntimeError(f"missing dossier summary problem id: {dossier_summary}")
            retrieve_result = require_event("paper_claim_retrieve_result")
            if retrieve_result.get("closest_items", [])[0].get("reference") != "beta paper":
                raise RuntimeError(f"missing retrieval summary in retrieve event: {retrieve_result}")
            source_access = retrieve_result.get("source_access", {})
            if source_access.get("paper_access", [])[0].get("download_path") != "/tmp/materials_cache/downloads/beta.pdf":
                raise RuntimeError(f"missing local paper access in retrieve event: {retrieve_result}")
            map_result = require_event("paper_claim_map_result")
            if map_result.get("closest_baseline") != "beta baseline":
                raise RuntimeError(f"missing mapping summary in map event: {map_result}")
            select_result = require_event("paper_claim_select_result")
            if select_result.get("selected_problem_id") != "pd_paper_claim_01":
                raise RuntimeError(f"missing selection summary in select event: {select_result}")
            plan_result = require_event("paper_claim_plan_result")
            if plan_result.get("selected_problem_id") != "pd_paper_claim_01":
                raise RuntimeError(f"missing planner summary in plan event: {plan_result}")
            if report.get("selected_candidate", {}).get("theorem_name_stem") != "beta_visible_headline":
                raise RuntimeError(f"missing selected candidate summary in report: {report}")
    finally:
        paper_claim_session.request_problem_design_clusters = original_problem_design_cluster
        paper_claim_session.request_problem_design_contextualization = original_problem_design_contextualize
        paper_claim_session.request_problem_design_core_extract = original_problem_design_core_extract
        paper_claim_session.request_paper_claim_select = original_paper_claim_select
        paper_claim_session.request_paper_claim_retrieval = original_paper_claim_retrieve
        paper_claim_session.request_paper_claim_mapping = original_paper_claim_map
        paper_claim_session.request_paper_claim_plan = original_paper_claim_plan
        paper_claim_session.process_paper_claim_formalization_plan = original_process
        paper_claim_session.load_current_guidance = original_guidance
        paper_claim_session.ensure_materials_cache_current = original_materials_sync

    test_resume_from_plan_event()
    print("paper claim session event log test passed")
    return 0


def test_resume_from_plan_event() -> None:
    original_process = paper_claim_session.process_paper_claim_formalization_plan
    original_guidance = paper_claim_session.load_current_guidance
    try:
        captured: dict[str, object] = {}

        def fake_process_paper_claim_formalization_plan(**kwargs):
            captured.update(kwargs)
            return {
                "processed": True,
                "verify_success": True,
                "candidate_id": kwargs["candidate_id"],
                "status": "proved",
                "theorem_name": "paper_claim_beta_visible_headline",
            }

        paper_claim_session.process_paper_claim_formalization_plan = fake_process_paper_claim_formalization_plan
        paper_claim_session.load_current_guidance = lambda _data_dir: build_guidance_context(
            theory_state={},
            research_agenda={},
            materials={},
        )

        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            data_dir = root / "data"
            data_dir.mkdir(parents=True, exist_ok=True)
            session_events_path = data_dir / "resume.events.jsonl"
            rows = [
                {
                    "event": "problem_design_core_extract_result",
                    "status": "ok",
                    "candidate_set_id": "pd_paper_claim_01",
                    "core_dossier": {
                        "problem_id": "pd_paper_claim_01",
                        "cluster_id": "cluster_001",
                        "headline_claim": "intrinsic semantic invariant on partial elimination states",
                        "core_mathematical_content": "beta mathematical core",
                        "literature_context": {
                            "closest_baseline": "beta paper",
                            "routine_reading_risk": "beta routine risk",
                            "possible_opening": "beta opening",
                        },
                        "supporting_claims": ["beta support"],
                        "no_go_faces": ["beta no-go"],
                        "proof_assets": ["beta asset"],
                        "why_this_face": "beta why",
                    },
                },
                {
                    "event": "paper_claim_retrieve_result",
                    "status": "ok",
                    "problem_id": "pd_paper_claim_01",
                    "closest_items": [{"reference": "beta paper", "kind": "source_link", "relevance": "beta", "confidence": "high"}],
                    "directly_read_evidence": [],
                    "coverage_assessment": "sufficient",
                    "missing_angles": [],
                    "need_supplemental_retrieval": False,
                },
                {
                    "event": "paper_claim_map_result",
                    "status": "ok",
                    "problem_id": "pd_paper_claim_01",
                    "closest_baseline": "beta baseline",
                    "relations": [{"reference": "beta paper", "overlap": "same family", "delta": "sharper theorem face", "delta_materiality": "substantial"}],
                    "theorem_face_assessment": "natural",
                    "baseline_delta": "state the invariant directly",
                    "outsider_risk": "could still look nearby",
                },
                {
                    "event": "paper_claim_select_result",
                    "status": "ok",
                    "selection_id": "paper_claim_select_01",
                    "selected_problem_id": "pd_paper_claim_01",
                    "selection_note": "beta dossier is currently the closest to a paper-publishable unit",
                    "planning_focus": "plan this as a short invariant-first package",
                    "assessments": [],
                },
                {
                    "event": "paper_claim_plan_result",
                    "status": "ok",
                    "plan_id": "paper_claim_plan_for_pd_paper_claim_01",
                    "selected_problem_id": "pd_paper_claim_01",
                    "headline": "intrinsic semantic invariant on partial elimination states",
                    "package_strategy": "split the package into an invariant lemma, then the headline theorem",
                    "theorem_units": [
                        {
                            "unit_id": "u1",
                            "role": "entry_lemma",
                            "kind": "lemma",
                            "name_stem": "beta_partial_state_invariant",
                            "statement": "A concise invariant lemma for partial elimination states.",
                            "docstring_summary": "beta first target",
                            "purpose": "entry lemma that unlocks the package headline",
                            "uses_existing_results": [],
                            "needs_new_ingredients": [],
                            "proof_idea": ["First isolate the support theorem.", "Then rewrite the invariant through it."],
                            "unlocks": ["u2"],
                        },
                        {
                            "unit_id": "u2",
                            "role": "headline_theorem",
                            "kind": "theorem",
                            "name_stem": "beta_visible_headline",
                            "statement": "The visible theorem derived from the invariant.",
                            "docstring_summary": "beta headline",
                            "purpose": "headline theorem for the selected package",
                            "uses_existing_results": ["beta_partial_state_invariant"],
                            "needs_new_ingredients": [],
                            "proof_idea": ["Apply the entry lemma at the full construction.", "Conclude the headline theorem."],
                            "unlocks": [],
                        },
                    ],
                    "formalization_order": ["u1", "u2"],
                },
            ]
            session_events_path.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows), encoding="utf-8")

            report = paper_claim_session.resume_paper_claim_session_from_plan_event(
                resume_session_events_path=session_events_path,
                resume_plan_id="paper_claim_plan_for_pd_paper_claim_01",
                worker_settings={},
                scratch_file=root / "Scratch.lean",
                derived_file=root / "Derived.lean",
                derived_entries=[],
                data_dir=data_dir,
                base_theory_context="",
                formalize_worker_settings={},
                paper_claim_planner_prompt_file="prompts/paper_claim/plan.md",
                paper_claim_codex_prove_prompt_file=".codex/workflow/paper_claim_codex_prove.md",
                post_expand_prompt_file="prompts/expander/post_theorem.md",
                prioritize_open_problems_worker_settings={},
                prioritize_open_problems_prompt_file="prompts/prioritizer/open_problem_prioritizer.md",
                theory_file=root / "Theory.lean",
                repo_root=REPO_ROOT,
                batch_generator_seed_count=4,
                batch_generator_open_target_min=2,
                current_iteration=8,
                skip_verify=True,
                verify_timeout_sec=10,
                failure_threshold=2,
                phase_logs=False,
                run_id="resume-test",
                phase_attempts_path=None,
                session_events_path=session_events_path,
                state_lock=threading.Lock(),
                derived_runtime_state={"generation": 0},
            )

            if report.get("selected_candidate", {}).get("theorem_name_stem") != "beta_visible_headline":
                raise RuntimeError(f"unexpected resumed selected candidate: {report}")
            if str(captured.get("selected_problem_id", "")) != "pd_paper_claim_01":
                raise RuntimeError(f"resume should target the selected problem id: {captured}")
            resumed_package = captured.get("selected_dossier_package", {})
            if not isinstance(resumed_package, dict) or resumed_package.get("problem_id") != "pd_paper_claim_01":
                raise RuntimeError(f"resume should reconstruct selected_dossier_package: {captured}")
    finally:
        paper_claim_session.process_paper_claim_formalization_plan = original_process
        paper_claim_session.load_current_guidance = original_guidance


if __name__ == "__main__":
    raise SystemExit(main())
