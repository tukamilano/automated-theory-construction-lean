from __future__ import annotations

import os
import sys
import tempfile
import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "loop"))


import generate_seeds_from_theory
import generate_research_agenda_from_report
import materials_pipeline
import run_loop
from guidance import build_guidance_context
from paper_claim import paper_claim_session
from paper_claim.paper_claim_session import request_paper_claim_mapping
from paper_claim.paper_claim_session import request_paper_claim_plan
from paper_claim.paper_claim_session import request_paper_claim_retrieval
from paper_claim.paper_claim_session import request_paper_claim_select
from materials import load_materials
from materials_pipeline import build_download_metadata
from materials_pipeline import save_download_index
from materials_pipeline import extract_paper_record
from materials_pipeline import classify_source_reference
from materials_pipeline import parse_source_link_entries
from materials_pipeline import save_paper_record
from materials_sync import ensure_materials_derived_current
from research_agenda import DEFAULT_RESEARCH_AGENDA_PATH
from research_agenda import LEGACY_RESEARCH_AGENDA_PATH
from research_agenda import empty_research_agenda
from research_agenda import load_research_agenda
from research_agenda import parse_research_agenda_markdown
from research_agenda import summarize_research_agenda_for_state
from common import write_jsonl_atomic


def test_parse_research_agenda_markdown_extracts_sections() -> None:
    payload = parse_research_agenda_markdown(
        """# Research Agenda

## Themes
- bridge theorem clusters

## Valued Problem Types
- classification results
- separation statements

## Anti-Goals
- cosmetic rewrites

## Canonical Targets
1. exact boundary results

## Soft Constraints
- stay close to the active theory
"""
    )
    if payload["themes"] != ["bridge theorem clusters"]:
        raise RuntimeError(f"unexpected themes: {payload}")
    if payload["valued_problem_types"] != ["classification results", "separation statements"]:
        raise RuntimeError(f"unexpected valued problem types: {payload}")
    if payload["anti_goals"] != ["cosmetic rewrites"]:
        raise RuntimeError(f"unexpected anti-goals: {payload}")
    if payload["canonical_targets"] != ["exact boundary results"]:
        raise RuntimeError(f"unexpected canonical targets: {payload}")
    if payload["soft_constraints"] != ["stay close to the active theory"]:
        raise RuntimeError(f"unexpected soft constraints: {payload}")


def test_parse_research_agenda_markdown_handles_numbered_headings_and_ignores_paragraphs() -> None:
    payload = parse_research_agenda_markdown(
        """# Research Agenda

## 1. Themes

Introductory paragraph that should not become an item.

* **Bridge theorem clusters**
  Supporting explanation that should not become a separate item.
* **Boundary criteria**
  > Example paragraph that should also be ignored.

## 2. Valued Problem Types

Within this agenda, solutions to problems of the following kinds are especially valuable.

1. **Classification results**
   Extended explanation that should not become a second item.
2. **Separation statements**
"""
    )
    if payload["themes"] != ["Bridge theorem clusters", "Boundary criteria"]:
        raise RuntimeError(f"unexpected numbered-heading themes: {payload}")
    if payload["valued_problem_types"] != ["Classification results", "Separation statements"]:
        raise RuntimeError(f"unexpected numbered-heading valued problem types: {payload}")


def test_load_research_agenda_missing_file_is_empty() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        payload = load_research_agenda(Path(tmpdir) / DEFAULT_RESEARCH_AGENDA_PATH)
    if payload != empty_research_agenda():
        raise RuntimeError(f"expected empty research agenda, got: {payload}")


def test_load_research_agenda_falls_back_to_legacy_root_file() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        repo_root = Path(tmpdir)
        legacy_path = repo_root / LEGACY_RESEARCH_AGENDA_PATH
        legacy_path.write_text(
            """# Research Agenda

## Themes
- legacy bridge theorem clusters
""",
            encoding="utf-8",
        )
        payload = load_research_agenda(repo_root / DEFAULT_RESEARCH_AGENDA_PATH)
    if payload["themes"] != ["legacy bridge theorem clusters"]:
        raise RuntimeError(f"expected legacy fallback research agenda, got: {payload}")


def test_seed_prompt_includes_research_agenda_guidance() -> None:
    prompt = generate_seeds_from_theory.build_prompt(
        theory_files=[Path("AutomatedTheoryConstruction/Theory.lean")],
        derived_file=None,
        context_files=[],
        seed_count=2,
        extra_instruction="",
        guidance=build_guidance_context(
            theory_state={},
            research_agenda={
                "themes": ["bridge theorem clusters"],
                "valued_problem_types": ["classification results"],
                "anti_goals": ["cosmetic rewrites"],
                "canonical_targets": ["exact boundary results"],
                "soft_constraints": ["stay close to the active theory"],
            },
        ),
    )
    required_snippets = (
        "Research agenda: treat the following as external value guidance",
        "Themes: bridge theorem clusters",
        "Valued problem types: classification results",
        "Anti-goals: cosmetic rewrites",
        "Canonical targets: exact boundary results",
        "Soft constraints: stay close to the active theory",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing agenda snippet in seed prompt: {snippet}\n{prompt}")


def test_render_research_agenda_user_prompt_substitutes_placeholders() -> None:
    rendered = generate_research_agenda_from_report.render_user_prompt(
        template_text="Title:\n<TITLE>\nField:\n<FIELD>\nStyle:\n<STYLE_ANCHOR_BLOCK>\nPrefs:\n<LOCAL_PREFERENCES_BLOCK>\nReport:\n<REPORT>\n",
        title="Agenda Title",
        field="Agenda Field",
        report_text="Line A\nLine B",
        style_anchor_text="Strict anchor",
        local_preferences=["Prefer exact boundaries."],
    )
    required_snippets = (
        "Title:\nAgenda Title",
        "Field:\nAgenda Field",
        "Style:\nStrict anchor",
        "Prefs:\n- Prefer exact boundaries.",
        "Report:\nLine A\nLine B",
    )
    for snippet in required_snippets:
        if snippet not in rendered:
            raise RuntimeError(f"missing rendered snippet: {snippet}\n{rendered}")


def test_validate_generated_agenda_requires_all_sections() -> None:
    good = """# Research Agenda for Test

## 1. Themes
- theme

## 2. Valued Problem Types
- problem type

## 3. Anti-Goals
- anti-goal

## 4. Canonical Targets
1. target

## 5. Soft Constraints
- soft constraint
"""
    generate_research_agenda_from_report.validate_generated_agenda(good)

    bad = """# Research Agenda for Test

## 1. Themes
- theme
"""
    try:
        generate_research_agenda_from_report.validate_generated_agenda(bad)
    except ValueError as exc:
        message = str(exc)
    else:
        raise RuntimeError("expected validate_generated_agenda to reject missing sections")
    if "missing required section items" not in message:
        raise RuntimeError(f"unexpected validation message: {message}")


def test_seed_prompt_includes_materials_guidance() -> None:
    materials = {
        "documents": [
            {
                "path": "lambek/02_section_map.md",
                "kind": "section_map",
                "title": "Section Map",
                "confidence": "high",
                "content_available": True,
            }
        ],
        "problem_generation": [
            "rigorous separation of expressive power between systems",
            "sharp boundaries of decidability and cut-elimination",
        ],
        "problem_evaluation": [
            "Does this candidate change the summary of the structural theory rather than extend one proof path?",
        ],
        "source_links": [
            "The Lambek Calculus - DSpace, https://dspace.library.uu.nl/bitstream/handle/1874/629/c8.pdf",
        ],
    }
    prompt = generate_seeds_from_theory.build_prompt(
        theory_files=[Path("AutomatedTheoryConstruction/Theory.lean")],
        derived_file=None,
        context_files=[],
        seed_count=2,
        extra_instruction="",
        guidance=build_guidance_context(
            theory_state={},
            research_agenda={},
            materials=materials,
        ),
    )
    required_snippets = (
        "External literature materials are available as optional context. Treat them as external anchors, not as internal state.",
        "Outward-looking problem-generation anchors from materials: rigorous separation of expressive power between systems; sharp boundaries of decidability and cut-elimination",
        "Materials-based evaluation checks: Does this candidate change the summary of the structural theory rather than extend one proof path?",
        "Source links are available for deeper follow-up if a candidate needs literature positioning: The Lambek Calculus - DSpace, https://dspace.library.uu.nl/bitstream/handle/1874/629/c8.pdf",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing materials snippet in seed prompt: {snippet}\n{prompt}")


def test_runtime_initialization_clears_generation_sidecar_files() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir)
        data_dir = tmp_path / "data"
        data_dir.mkdir(parents=True, exist_ok=True)
        seeds_file = tmp_path / "seeds.jsonl"
        scratch_file = tmp_path / "Scratch.lean"
        derived_file = tmp_path / "Derived.lean"
        formalization_memory_file = data_dir / "formalization_memory.json"
        archived_problems_file = data_dir / "archived_problems.jsonl"
        theorem_reuse_memory_file = data_dir / "theorem_reuse_memory.json"
        paper_claim_rejection_memory_file = data_dir / "paper_claim_rejection_memory.json"

        write_jsonl_atomic(
            seeds_file,
            [{"id": "op_000001", "stmt": "True", "src": "seed"}],
        )
        theorem_reuse_memory_file.write_text(
            json.dumps(
                {
                    "entries": [
                        {
                            "candidate_id": "mt_old",
                            "theorem_name": "old_theorem",
                            "statement": "True",
                            "docstring_summary": "",
                            "rationale": "",
                            "plan_summary": "",
                            "supporting_theorems": [],
                            "intermediate_lemmas": [],
                            "iteration": 1,
                            "appended_to_derived": True,
                        }
                    ]
                },
                ensure_ascii=False,
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        paper_claim_rejection_memory_file.write_text(
            json.dumps(
                {
                    "entries": [
                        {
                            "candidate_id": "mt_old",
                            "statement": "True",
                            "theorem_name_stem": "old_reject",
                            "rationale": "",
                            "verdict": "reject",
                            "reason": "too thin",
                        }
                    ]
                },
                ensure_ascii=False,
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )

        run_loop.initialize_runtime_state(
            data_dir=data_dir,
            seeds_file=seeds_file,
            scratch_file=scratch_file,
            reset_scratch=False,
            derived_file=derived_file,
            derived_cleanup_files=(),
            reset_derived=False,
            formalization_memory_file=formalization_memory_file,
            reset_formalization_memory=False,
            archived_problems_file=archived_problems_file,
        )
        theorem_reuse_payload = json.loads(theorem_reuse_memory_file.read_text(encoding="utf-8"))
        if theorem_reuse_payload != {"entries": []}:
            raise RuntimeError("theorem_reuse_memory.json was not cleared on initialization")
        rejection_payload = json.loads(paper_claim_rejection_memory_file.read_text(encoding="utf-8"))
        if rejection_payload != {"entries": []}:
            raise RuntimeError("paper_claim_rejection_memory.json was not cleared on initialization")


def test_worker_payloads_include_research_agenda() -> None:
    agenda = {
        "themes": ["bridge theorem clusters"],
        "valued_problem_types": ["classification results"],
        "anti_goals": ["cosmetic rewrites"],
        "canonical_targets": ["exact boundary results"],
        "soft_constraints": ["stay close to the active theory"],
    }
    materials = {
        "documents": [
            {
                "path": "lambek/00_index.md",
                "kind": "index",
                "title": "Lambek Materials Index",
                "confidence": "high",
                "content_available": True,
            }
        ],
        "problem_generation": ["provability relations among structural rules"],
        "problem_evaluation": ["Down-rank candidates that only produce narrow local continuation."],
        "paper_claim": ["Read `03_source_links.md` when novelty pressure depends on a cited paper."],
        "source_links": ["Substructural logics - https://research-portal.st-andrews.ac.uk/en/publications/substructural-logics/"],
        "source_link_entries": [
            {
                "label": "Substructural logics",
                "url": "https://research-portal.st-andrews.ac.uk/en/publications/substructural-logics/",
                "note": "",
            }
        ],
        "paper_cache": [
            {
                "source_id": "paper_substructural_logics",
                "title": "Substructural logics",
                "source_url": "https://research-portal.st-andrews.ac.uk/en/publications/substructural-logics/",
                "extract_confidence": "high",
                "abstract": "Bridge theorem style overview of substructural logic and structural rules.",
                "chunks": [
                    {
                        "chunk_id": "chunk_001",
                        "section": "Abstract",
                        "page": None,
                        "text": "Substructural logic studies structural rules such as weakening and contraction.",
                    }
                ],
                "paper_relpath": "papers/paper_substructural_logics.json",
            }
        ],
    }
    captured_payloads: dict[str, dict[str, object]] = {}
    original_invoke_worker_json = run_loop.invoke_worker_json
    original_paper_claim_invoke_worker_json = paper_claim_session.invoke_worker_json
    original_load_current_research_agenda = run_loop.load_current_research_agenda

    try:
        run_loop.load_current_research_agenda = lambda: agenda

        def fake_invoke_worker_json(*, settings, task_type, system_prompt, payload, metadata):
            captured_payloads[task_type] = dict(payload)
            if task_type == "prioritize_open_problems":
                return (
                    {
                        "priorities": [
                            {
                                "problem_id": "op_000001",
                                "priority": "high",
                                "rationale": "agenda-aligned bridge problem",
                            }
                        ],
                        "theory_snapshot": "A short theory snapshot.",
                        "next_direction": {
                            "label": "bridge_clusters",
                            "guidance": "Prefer bridge lemmas.",
                            "rationale": "They match the active agenda.",
                        },
                        "desired_summary_changes": [],
                        "current_bottlenecks": [],
                        "overexplored_patterns": [],
                        "missing_bridges": [],
                        "agenda_pressure": [],
                    },
                    {"worker": "research_agenda_test"},
                )
            if task_type == "expand":
                return (
                    {
                        "problem_id": "op_000001",
                        "candidates": [],
                    },
                    {"worker": "research_agenda_test"},
                )
            if task_type == "paper_claim_select":
                return (
                    {
                        "selection_id": "paper_claim_select_01",
                        "selected_problem_id": "pd_paper_claim_01",
                        "selection_note": "The dossier best matches the active agenda in the fixture.",
                        "planning_focus": "Plan this as a short bridge package centered on the clean theorem face.",
                        "assessments": [
                            {
                                "problem_id": "pd_paper_claim_01",
                                "paper_publishable_fit": "high",
                                "selected": True,
                                "why_selected": "cleanest current theorem face in the fixture",
                                "why_not_selected": "",
                            }
                        ],
                    },
                    {"worker": "research_agenda_test"},
                )
            if task_type == "paper_claim_retrieve":
                return (
                    {
                        "problem_id": "pd_paper_claim_01",
                        "closest_items": [
                            {
                                "reference": "placeholder source link",
                                "kind": "source_link",
                                "relevance": "closest structural anchor",
                                "confidence": "high",
                            }
                        ],
                        "directly_read_evidence": [
                            {
                                "reference": "placeholder source link",
                                "evidence": "placeholder directly read evidence",
                                "supports": "placeholder support",
                                "confidence": "medium",
                            }
                        ],
                        "coverage_assessment": "materials are sufficient for mapping in the fixture",
                        "missing_angles": [],
                        "need_supplemental_retrieval": False,
                    },
                    {"worker": "research_agenda_test"},
                )
            if task_type == "paper_claim_map":
                return (
                    {
                        "problem_id": "pd_paper_claim_01",
                        "closest_baseline": "placeholder baseline",
                        "relations": [
                            {
                                "reference": "placeholder source link",
                                "overlap": "same bridge-style theme",
                                "delta": "candidate sharpens the structural bridge",
                                "delta_materiality": "substantial",
                            }
                        ],
                        "theorem_face_assessment": "the dossier reads naturally as a theorem unit in the fixture",
                        "baseline_delta": "the dossier still exposes an external delta in the fixture",
                        "outsider_risk": "A reviewer may still ask whether this is just a nearby bridge reformulation.",
                    },
                    {"worker": "research_agenda_test"},
                )
            if task_type == "paper_claim_plan":
                return (
                    {
                        "plan_id": "paper_claim_plan_for_pd_paper_claim_01",
                        "selected_problem_id": "pd_paper_claim_01",
                        "headline": "fixture headline",
                        "package_strategy": "split the fixture package into a bridge lemma and the visible theorem",
                        "theorem_units": [
                            {
                                "unit_id": "u1",
                                "role": "entry_lemma",
                                "kind": "lemma",
                                "name_stem": "agenda_paper_claim_bridge",
                                "statement": "Fixture bridge lemma.",
                                "docstring_summary": "Agenda bridge placeholder theorem.",
                                "purpose": "entry lemma for the selected fixture package",
                                "uses_existing_results": [],
                                "needs_new_ingredients": [],
                                "proof_idea": [
                                    "First reduce to the available fixture theorem.",
                                    "Then rewrite the target.",
                                ],
                                "unlocks": ["u2"],
                            },
                            {
                                "unit_id": "u2",
                                "role": "headline_theorem",
                                "kind": "theorem",
                                "name_stem": "agenda_fixture_headline",
                                "statement": "Fixture headline theorem.",
                                "docstring_summary": "Fixture headline.",
                                "purpose": "visible theorem for the fixture package",
                                "uses_existing_results": ["agenda_paper_claim_bridge"],
                                "needs_new_ingredients": [],
                                "proof_idea": [
                                    "Apply the bridge lemma to the full fixture statement.",
                                    "Conclude the visible theorem.",
                                ],
                                "unlocks": [],
                            },
                        ],
                        "formalization_order": ["u1", "u2"],
                    },
                    {"worker": "research_agenda_test"},
                )
            if task_type == "problem_design_core_extract":
                return (
                    {
                        "problem_id": "pd_paper_claim_01",
                        "cluster_id": "cluster_001",
                        "headline_claim": "fixture headline",
                        "core_mathematical_content": "fixture mathematical core",
                        "literature_context": {
                            "closest_baseline": "fixture baseline",
                            "routine_reading_risk": "fixture routine reading risk",
                            "possible_opening": "fixture possible opening",
                        },
                        "supporting_claims": [],
                        "no_go_faces": [],
                        "proof_assets": ["fixture asset"],
                        "why_this_face": "fixture why this face",
                    },
                    {"worker": "research_agenda_test"},
                )
            raise RuntimeError(f"unexpected task_type: {task_type}")

        run_loop.invoke_worker_json = fake_invoke_worker_json
        paper_claim_session.invoke_worker_json = fake_invoke_worker_json

        run_loop.request_open_problem_priorities(
            worker_settings={},
            prioritizer_prompt="unused",
            tracked_rows=[{"id": "op_000001", "stmt": "True", "src": "seed"}],
            derived_entries=[],
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda, materials=materials),
        )
        run_loop.request_expand_candidates(
            worker_settings={},
            expand_prompt="unused",
            task_type="expand",
            problem_id="op_000001",
            stmt="True",
            original_stmt="True",
            result="stuck",
            verify_success=False,
            theory_context="",
            open_rows=[],
            existing_new_problems=[],
            verify_error_excerpt="",
            current_iteration_full_logs=[],
            same_problem_history_tail=[],
            theory_state={},
            materials=materials,
            max_candidates=2,
        )
        dossier = {
            "problem_id": "pd_paper_claim_01",
            "cluster_id": "cluster_001",
            "headline_claim": "fixture headline",
            "core_mathematical_content": "fixture mathematical core",
            "literature_context": {
                "closest_baseline": "fixture baseline",
                "routine_reading_risk": "fixture routine reading risk",
                "possible_opening": "fixture possible opening",
            },
            "supporting_claims": [],
            "no_go_faces": [],
            "proof_assets": ["fixture asset"],
            "why_this_face": "fixture why this face",
        }
        retrieval, _ = request_paper_claim_retrieval(
            worker_settings={},
            retriever_prompt="unused",
            dossier=dossier,
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda, materials=materials),
        )
        mapping, _ = request_paper_claim_mapping(
            worker_settings={},
            mapper_prompt="unused",
            dossier=dossier,
            retrieval=retrieval,
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda, materials=materials),
        )
        selection, _ = request_paper_claim_select(
            worker_settings={},
            selector_prompt="unused",
            selection_id="paper_claim_select_01",
            dossier_packages=[
                {
                    "problem_id": "pd_paper_claim_01",
                    "dossier": dossier,
                    "retrieval": retrieval,
                    "mapping": mapping,
                }
            ],
            current_iteration=1,
        )
        request_paper_claim_plan(
            worker_settings={},
            planner_prompt="unused",
            plan_id="paper_claim_plan_for_pd_paper_claim_01",
            selected_dossier_package={
                "problem_id": "pd_paper_claim_01",
                "dossier": dossier,
                "retrieval": retrieval,
                "mapping": mapping,
            },
            selection=selection,
            derived_entries=[],
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda, materials=materials),
        )
        paper_claim_session.request_problem_design_core_extract(
            worker_settings={},
            prompt="unused",
            problem_id="pd_paper_claim_01",
            current_iteration=1,
            cluster_context={
                "cluster_id": "cluster_001",
                "cluster_theme": "fixture cluster",
                "cluster_summary": "fixture summary",
                "member_theorems": [{"name": "fixture", "statement": "True"}],
                "objects": [],
                "invariants": [],
                "algorithms": [],
                "suspected_support_layer": [],
                "retained_positive_signal": "should be scrubbed",
            },
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda, materials=materials),
        )
    finally:
        run_loop.invoke_worker_json = original_invoke_worker_json
        paper_claim_session.invoke_worker_json = original_paper_claim_invoke_worker_json
        run_loop.load_current_research_agenda = original_load_current_research_agenda

    for task_type in (
        "prioritize_open_problems",
        "expand",
        "paper_claim_select",
        "paper_claim_retrieve",
        "paper_claim_map",
        "paper_claim_plan",
    ):
        payload = captured_payloads.get(task_type)
        if payload is None:
            raise RuntimeError(f"missing captured payload for {task_type}")
        if task_type in {"paper_claim_retrieve", "paper_claim_map"}:
            retrieval_materials = payload.get("materials")
            if not isinstance(retrieval_materials, dict):
                raise RuntimeError(f"missing compact review materials payload: {payload}")
            if retrieval_materials.get("materials_dir") != "":
                raise RuntimeError(f"unexpected retrieval materials_dir: {retrieval_materials}")
            paper_excerpt_context = retrieval_materials.get("paper_excerpt_context", [])
            if not isinstance(paper_excerpt_context, list) or len(paper_excerpt_context) != 1:
                raise RuntimeError(f"expected one paper excerpt context entry: {retrieval_materials}")
            if paper_excerpt_context[0].get("reference") != "Substructural logics":
                raise RuntimeError(f"unexpected paper excerpt context reference: {retrieval_materials}")
            paper_cache = retrieval_materials.get("paper_cache", [])
            if not isinstance(paper_cache, list) or len(paper_cache) != 1:
                raise RuntimeError(f"expected one compact retrieval paper entry: {retrieval_materials}")
            if paper_cache[0].get("title") != "Substructural logics":
                raise RuntimeError(f"unexpected compact retrieval paper title: {retrieval_materials}")
        elif task_type not in {"paper_claim_plan", "paper_claim_select"} and payload.get("materials") != materials:
            raise RuntimeError(f"missing materials in {task_type} payload: {payload}")
        if task_type in {"paper_claim_select", "paper_claim_retrieve", "paper_claim_map", "paper_claim_plan"}:
            if "tracked_problems" in payload:
                raise RuntimeError(f"paper claim payload should not include tracked_problems: {payload}")
        if (
            task_type not in {"paper_claim_select", "paper_claim_plan", "problem_design_core_extract", "paper_claim_retrieve", "paper_claim_map"}
            and payload.get("theory_state") != {}
            and task_type != "prioritize_open_problems"
        ):
            raise RuntimeError(f"unexpected theory_state in {task_type} payload: {payload}")
    select_payload = captured_payloads.get("paper_claim_select", {})
    dossier_packages = select_payload.get("dossier_packages", [])
    if not isinstance(dossier_packages, list) or not dossier_packages:
        raise RuntimeError(f"selector payload should include dossier_packages: {select_payload}")
    priority_payload = captured_payloads.get("prioritize_open_problems", {})
    if priority_payload.get("previous_theory_state") != {}:
        raise RuntimeError(f"unexpected previous_theory_state in prioritize_open_problems payload: {priority_payload}")
    planner_payload = captured_payloads.get("paper_claim_plan", {})
    if planner_payload.get("theory_state") != {}:
        raise RuntimeError(f"unexpected theory_state in planner payload: {planner_payload}")
    selected_dossier_package = planner_payload.get("selected_dossier_package", {})
    if not isinstance(selected_dossier_package, dict) or selected_dossier_package.get("problem_id") != "pd_paper_claim_01":
        raise RuntimeError(f"planner payload should include the selected dossier package: {planner_payload}")
    core_extract_payload = captured_payloads.get("problem_design_core_extract", {})
    if core_extract_payload.get("theory_state") != {}:
        raise RuntimeError(f"core_extract should receive only conceptual theory_state in this fixture: {core_extract_payload}")
    if "cluster_context" not in core_extract_payload:
        raise RuntimeError(f"core_extract should receive a single cluster_context: {core_extract_payload}")


def test_load_materials_extracts_sections_and_degrades_pdf_confidence() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        materials_dir = Path(tmpdir) / "materials"
        materials_dir.mkdir(parents=True, exist_ok=True)
        (materials_dir / "domain_research_report.md").write_text(
            """# Domain Research Report

This is a reusable summary that may become out of date.
""",
            encoding="utf-8",
        )
        (materials_dir / "00_index.md").write_text(
            """# Materials Index

## Usage
- Problem generation:
  Use problem seeds first.
- Problem evaluation:
  Use structural checks first.
- Main theorem session:
  Use source links when novelty pressure matters.
""",
            encoding="utf-8",
        )
        (materials_dir / "02_section_map.md").write_text(
            """# Section Map

## Problem Generation
- boundary problems

## Problem Evaluation
- prefer structural bridge claims

## Main Theorem Deep Access
- read source links for closest known result
""",
            encoding="utf-8",
        )
        (materials_dir / "03_source_links.md").write_text(
            """# Source Links

1. Example Paper - https://example.com/paper
2. Another Paper - https://example.com/other
""",
            encoding="utf-8",
        )
        (materials_dir / "paper.pdf").write_bytes(b"%PDF-1.4\n")

        payload = load_materials(materials_dir)

    if payload.get("problem_generation") != ["Use problem seeds first.", "boundary problems"]:
        raise RuntimeError(f"unexpected problem_generation: {payload}")
    if payload.get("problem_evaluation") != [
        "Use structural checks first.",
        "prefer structural bridge claims",
    ]:
        raise RuntimeError(f"unexpected problem_evaluation: {payload}")
    if payload.get("paper_claim") != [
        "Use source links when novelty pressure matters.",
        "read source links for closest known result",
    ]:
        raise RuntimeError(f"unexpected paper_claim: {payload}")
    if payload.get("source_links") != [
        "Example Paper - https://example.com/paper",
        "Another Paper - https://example.com/other",
    ]:
        raise RuntimeError(f"unexpected source_links: {payload}")
    source_link_entries = payload.get("source_link_entries", [])
    if not isinstance(source_link_entries, list) or source_link_entries[0].get("url") != "https://example.com/paper":
        raise RuntimeError(f"unexpected source_link_entries: {payload}")
    documents = payload.get("documents", [])
    pdf_docs = [doc for doc in documents if doc.get("kind") == "pdf"]
    if len(pdf_docs) != 1 or pdf_docs[0].get("content_available") is not False or pdf_docs[0].get("confidence") != "low":
        raise RuntimeError(f"unexpected pdf handling in materials payload: {payload}")
    report_docs = [doc for doc in documents if doc.get("kind") == "report"]
    if len(report_docs) != 1 or report_docs[0].get("confidence") != "medium":
        raise RuntimeError(f"unexpected report confidence in materials payload: {payload}")


def test_ensure_materials_derived_current_generates_files_from_root_report() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        materials_dir = Path(tmpdir) / "materials"
        materials_dir.mkdir(parents=True, exist_ok=True)
        report_path = materials_dir / "Sample_Structural_Theory_Research.md"
        report_path.write_text(
            """# Sample Structural Theory Research

## 1. Structural Correspondences

Some discussion of structural correspondences and language hierarchies.

### Table 1: Summary Grid

Table-like heading that should not become a section-map target.

## 2. Invertibility and Focusing

Some discussion of invertibility in proof search.

## 10. Canonical Objectives and Future Directions

1. **Mapping the Decidability Frontier**: explain the boundary precisely.
2. **Formalizing Structural Preservation**: keep the syntax-semantics interface sharp.

## Works Cited

1. Example Paper, accessed on April 11, 2026, [https://example.com/paper.pdf](https://example.com/paper.pdf)
2. Another Paper, accessed on April 11, 2026, [https://example.com/other](https://example.com/other)
""",
            encoding="utf-8",
        )

        report = ensure_materials_derived_current(materials_dir)
        payload = load_materials(materials_dir)
        reports = report.get("reports", [])
        if not isinstance(reports, list) or reports[0].get("generated_dir") != "sample":
            raise RuntimeError(f"unexpected materials sync report: {report}")
        generated_dir = materials_dir / "sample"
        for filename in ("00_index.md", "02_section_map.md", "03_source_links.md"):
            if not (generated_dir / filename).exists():
                raise RuntimeError(f"missing generated file {(generated_dir / filename)}")
        if (generated_dir / "04_problem_seeds.md").exists():
            raise RuntimeError(f"obsolete generated file should be removed: {generated_dir / '04_problem_seeds.md'}")
        section_map_text = (generated_dir / "02_section_map.md").read_text(encoding="utf-8")
        if "Table 1: Summary Grid" in section_map_text or "Works Cited" in section_map_text:
            raise RuntimeError(f"section map should ignore auxiliary headings: {section_map_text}")
        source_link_entries = payload.get("source_link_entries", [])
        if not isinstance(source_link_entries, list) or source_link_entries[0].get("url") != "https://example.com/paper.pdf":
            raise RuntimeError(f"generated source links not loaded as expected: {payload}")
        if payload.get("paper_claim") == []:
            raise RuntimeError(f"generated paper_claim guidance should not be empty: {payload}")


def test_parse_source_link_entries_extracts_labels_and_urls() -> None:
    entries = parse_source_link_entries(
        [
            "The Lambek Calculus - DSpace, accessed on April 11, 2026, [https://dspace.library.uu.nl/bitstream/handle/1874/629/c8.pdf](https://dspace.library.uu.nl/bitstream/handle/1874/629/c8.pdf)",
            "Substructural logics - https://research-portal.st-andrews.ac.uk/en/publications/substructural-logics/",
        ]
    )
    if len(entries) != 2:
        raise RuntimeError(f"unexpected parsed entry count: {entries}")
    if entries[0]["url"] != "https://dspace.library.uu.nl/bitstream/handle/1874/629/c8.pdf":
        raise RuntimeError(f"unexpected first parsed url: {entries}")
    if "accessed on" in entries[0]["label"].lower():
        raise RuntimeError(f"access date should be stripped from label: {entries}")
    if entries[1]["label"] != "Substructural logics":
        raise RuntimeError(f"unexpected second parsed label: {entries}")


def test_classify_source_reference_marks_qna_and_redirects_low_priority() -> None:
    qna = classify_source_reference(
        label="Substructural Logic: Understanding the roles of Weakening and Contraction",
        url="https://math.stackexchange.com/questions/3356302/substructural-logic-understanding-the-roles-of-weakening-and-contraction",
    )
    if qna["source_kind"] != "qna" or qna["retrieval_priority"] != "exclude":
        raise RuntimeError(f"unexpected qna classification: {qna}")

    redirect = classify_source_reference(
        label="The Lambek Calculus - DSpace",
        url="https://repository.upenn.edu/bitstreams/c318a63b-b658-45b1-a8d3-ff6378032ab1/download",
        content_type="text/html",
        title="DSpace",
        abstract="Redirecting to SSO Login DSpace software copyright © 2002-2026 LYRASIS",
    )
    if redirect["source_kind"] != "portal_redirect" or redirect["retrieval_priority"] != "exclude":
        raise RuntimeError(f"unexpected redirect classification: {redirect}")


def test_load_pdf_reader_class_uses_extra_site_dir() -> None:
    original_env = os.environ.get("ATC_MATERIALS_EXTRA_SITE_DIRS")
    original_sys_path = list(sys.path)
    original_module = sys.modules.pop("pypdf", None)
    try:
        with tempfile.TemporaryDirectory() as tmpdir:
            package_dir = Path(tmpdir) / "pypdf"
            package_dir.mkdir(parents=True, exist_ok=True)
            (package_dir / "__init__.py").write_text(
                "class PdfReader:\n    pass\n",
                encoding="utf-8",
            )
            os.environ["ATC_MATERIALS_EXTRA_SITE_DIRS"] = tmpdir
            reader_class, module_name = materials_pipeline._load_pdf_reader_class()
            if module_name != "pypdf" or reader_class is None or reader_class.__name__ != "PdfReader":
                raise RuntimeError(f"unexpected pdf reader resolution: {(reader_class, module_name)}")
    finally:
        if original_env is None:
            os.environ.pop("ATC_MATERIALS_EXTRA_SITE_DIRS", None)
        else:
            os.environ["ATC_MATERIALS_EXTRA_SITE_DIRS"] = original_env
        sys.path[:] = original_sys_path
        sys.modules.pop("pypdf", None)
        if original_module is not None:
            sys.modules["pypdf"] = original_module


def test_load_materials_includes_cached_paper_records() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        root = Path(tmpdir)
        materials_dir = root / "materials"
        materials_dir.mkdir(parents=True, exist_ok=True)
        (materials_dir / "03_source_links.md").write_text(
            """# Source Links

## Source Links
- Example paper - https://example.com/paper.html
""",
            encoding="utf-8",
        )
        cache_dir = root / "data" / "materials_cache"
        html_path = cache_dir / "downloads" / "example.html"
        html_path.parent.mkdir(parents=True, exist_ok=True)
        html_path.write_text(
            "<html><head><title>Example Paper</title></head><body><h1>Abstract</h1><p>Bridge theorem summary.</p><h2>Introduction</h2><p>More detail.</p></body></html>",
            encoding="utf-8",
        )
        record = extract_paper_record(
            html_path,
            source_id="example_source",
            source_url="https://example.com/paper.html",
            label="Example paper",
            content_type="text/html",
        )
        save_download_index(
            cache_dir,
            [
                build_download_metadata(
                    label="Example paper",
                    url="https://example.com/paper.html",
                    content_type="text/html",
                    local_relpath="downloads/example.html",
                )
            ],
        )
        save_paper_record(cache_dir, record)

        payload = load_materials(materials_dir)

    paper_cache = payload.get("paper_cache", [])
    if not isinstance(paper_cache, list) or len(paper_cache) != 1:
        raise RuntimeError(f"expected one paper_cache record, got: {payload}")
    if paper_cache[0].get("title") != "Example Paper":
        raise RuntimeError(f"unexpected paper_cache title: {payload}")
    if paper_cache[0].get("download_relpath") != "downloads/example.html":
        raise RuntimeError(f"missing cached download relpath on paper record: {payload}")
    if not str(paper_cache[0].get("download_path", "")).endswith("/downloads/example.html"):
        raise RuntimeError(f"missing cached download path on paper record: {payload}")
    source_link_entries = payload.get("source_link_entries", [])
    if not isinstance(source_link_entries, list) or source_link_entries[0].get("download_relpath") != "downloads/example.html":
        raise RuntimeError(f"expected source link entry to be enriched with cache paths: {payload}")


def test_extract_paper_record_discards_portal_redirect_boilerplate() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        html_path = Path(tmpdir) / "redirect.html"
        html_path.write_text(
            "<html><head><title>DSpace</title></head><body><h1>Redirecting to SSO Login</h1><p>DSpace software copyright © 2002-2026 LYRASIS Privacy policy End User Agreement Send Feedback</p></body></html>",
            encoding="utf-8",
        )
        record = extract_paper_record(
            html_path,
            source_id="redirect_source",
            source_url="https://repository.upenn.edu/bitstreams/demo/download",
            label="Repository download",
            content_type="text/html",
        )
    if record.get("source_kind") != "portal_redirect":
        raise RuntimeError(f"unexpected redirect source kind: {record}")
    if record.get("extract_confidence") != "low" or record.get("chunks") != [] or record.get("abstract") != "":
        raise RuntimeError(f"portal redirect should not survive as readable paper content: {record}")


def test_extract_paper_record_marks_scanned_pdf_as_image_only() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        pdf_path = Path(tmpdir) / "scan.pdf"
        pdf_path.write_bytes(
            b"%PDF-1.5\n1 0 obj<</Subtype/Image/Filter/CCITTFaxDecode>>endobj\n2 0 obj<</ProcSet[/PDF/ImageB/ImageI]>>endobj\n"
        )
        record = extract_paper_record(
            pdf_path,
            source_id="scan_source",
            source_url="https://example.com/scan.pdf",
            label="Scanned PDF",
            content_type="application/pdf",
        )
    if record.get("source_kind") != "scanned_pdf":
        raise RuntimeError(f"expected scanned pdf classification: {record}")
    if record.get("direct_reading_access") != "image_only_pdf":
        raise RuntimeError(f"expected image-only direct_reading_access: {record}")


def test_extract_paper_record_marks_scanned_pdf_ocr_when_text_recovered() -> None:
    original_extract_pdf_text = materials_pipeline._extract_pdf_text
    original_is_probably_image_only_pdf = materials_pipeline._is_probably_image_only_pdf
    try:
        materials_pipeline._extract_pdf_text = lambda _path: ("The Lambek Calculus enriched with Additional Connectives Abstract ...", "medium")
        materials_pipeline._is_probably_image_only_pdf = lambda _path: True
        with tempfile.TemporaryDirectory() as tmpdir:
            pdf_path = Path(tmpdir) / "scan.pdf"
            pdf_path.write_bytes(b"%PDF-1.5\n")
            record = extract_paper_record(
                pdf_path,
                source_id="scan_source",
                source_url="https://example.com/scan.pdf",
                label="Scanned PDF",
                content_type="application/pdf",
            )
    finally:
        materials_pipeline._extract_pdf_text = original_extract_pdf_text
        materials_pipeline._is_probably_image_only_pdf = original_is_probably_image_only_pdf
    if record.get("source_kind") != "scanned_pdf_ocr":
        raise RuntimeError(f"expected scanned_pdf_ocr classification: {record}")
    if record.get("direct_reading_access") != "ocr_partial":
        raise RuntimeError(f"expected ocr_partial direct_reading_access: {record}")
    if record.get("extract_confidence") != "medium":
        raise RuntimeError(f"unexpected OCR recovery confidence: {record}")


def test_build_paper_claim_retrieval_materials_prefilters_paper_cache() -> None:
    candidate = {
        "candidate_id": "mt_candidate",
        "statement": "weakening and contraction characterize an affine bridge",
        "docstring_summary": "Bridge theorem for substructural logic fragments.",
        "rationale": "Compare weakening and contraction across nearby calculi.",
        "supporting_theorems": ["weakening_admissible", "contraction_control"],
        "missing_lemmas": [],
        "theorem_pattern": "structure_discovery",
        "context_note": "Position this against substructural logic surveys.",
        "conceptual_depth_note": "The theorem isolates a structural-rule boundary.",
    }
    materials = {
        "documents": [
            {
                "path": "survey.md",
                "kind": "report",
                "title": "Survey",
                "confidence": "high",
                "content_available": True,
                "excerpt": "Survey of weakening and contraction.",
            }
        ],
        "source_links": [
            "Substructural logics - https://example.com/substructural",
            "Completely unrelated - https://example.com/unrelated",
            "StackExchange discussion - https://math.stackexchange.com/questions/3356302/example",
        ],
        "source_link_entries": [
            {
                "label": "Substructural logics",
                "url": "https://example.com/substructural",
                "note": "",
                "source_kind": "repository_pdf",
                "retrieval_priority": "high",
                "direct_reading_access": "direct_fulltext",
            },
            {
                "label": "Unrelated paper",
                "url": "https://example.com/unrelated",
                "note": "",
                "source_kind": "web_page",
                "retrieval_priority": "medium",
                "direct_reading_access": "unclear",
            },
            {
                "label": "StackExchange discussion",
                "url": "https://math.stackexchange.com/questions/3356302/example",
                "note": "",
                "source_kind": "qna",
                "retrieval_priority": "exclude",
                "direct_reading_access": "discussion",
            },
        ],
        "paper_cache": [
            {
                "source_id": "substructural",
                "title": "Substructural logics",
                "source_url": "https://example.com/substructural",
                "extract_confidence": "high",
                "source_kind": "repository_pdf",
                "retrieval_priority": "high",
                "direct_reading_access": "direct_fulltext",
                "abstract": "Weakening and contraction organize substructural logic families.",
                "chunks": [
                    {
                        "chunk_id": "chunk_001",
                        "section": "Abstract",
                        "page": None,
                        "text": "Weakening and contraction mark boundaries among substructural logics.",
                    },
                    {
                        "chunk_id": "chunk_002",
                        "section": "Related Work",
                        "page": None,
                        "text": "This section compares affine and relevant fragments.",
                    },
                ],
                "paper_relpath": "papers/substructural.json",
                "paper_record_relpath": "papers/substructural.json",
                "paper_record_path": "/tmp/materials_cache/papers/substructural.json",
                "download_relpath": "downloads/substructural.pdf",
                "download_path": "/tmp/materials_cache/downloads/substructural.pdf",
            },
            {
                "source_id": "unrelated",
                "title": "A paper about topology",
                "source_url": "https://example.com/unrelated",
                "extract_confidence": "high",
                "source_kind": "web_page",
                "retrieval_priority": "medium",
                "direct_reading_access": "unclear",
                "abstract": "Topological dynamics without structural proof theory.",
                "chunks": [
                    {
                        "chunk_id": "chunk_001",
                        "section": "Abstract",
                        "page": None,
                        "text": "This paper is about compact spaces.",
                    }
                ],
                "paper_relpath": "papers/unrelated.json",
                "paper_record_relpath": "papers/unrelated.json",
                "paper_record_path": "/tmp/materials_cache/papers/unrelated.json",
                "download_relpath": "downloads/unrelated.html",
                "download_path": "/tmp/materials_cache/downloads/unrelated.html",
            },
            {
                "source_id": "qna_source",
                "title": "StackExchange discussion",
                "source_url": "https://math.stackexchange.com/questions/3356302/example",
                "extract_confidence": "high",
                "source_kind": "qna",
                "retrieval_priority": "exclude",
                "direct_reading_access": "discussion",
                "abstract": "Ask Question Asked 6 years ago about weakening and contraction.",
                "chunks": [
                    {
                        "chunk_id": "chunk_001",
                        "section": "Question",
                        "page": None,
                        "text": "I am trying to understand weakening and contraction.",
                    }
                ],
                "paper_relpath": "papers/qna.json",
                "paper_record_relpath": "papers/qna.json",
                "paper_record_path": "/tmp/materials_cache/papers/qna.json",
                "download_relpath": "downloads/qna.html",
                "download_path": "/tmp/materials_cache/downloads/qna.html",
            },
        ],
    }

    payload = paper_claim_session._build_paper_claim_retrieval_materials(candidate, materials)
    paper_cache = payload.get("paper_cache", [])
    if not isinstance(paper_cache, list) or len(paper_cache) != 2:
        raise RuntimeError(f"unexpected compact retrieval paper_cache: {payload}")
    if paper_cache[0].get("title") != "Substructural logics":
        raise RuntimeError(f"expected relevant paper first in compact retrieval payload: {payload}")
    if any(item.get("source_kind") == "qna" for item in paper_cache):
        raise RuntimeError(f"qna source should be filtered from compact retrieval paper cache: {payload}")
    selected_chunks = paper_cache[0].get("chunks", [])
    if not isinstance(selected_chunks, list) or not selected_chunks:
        raise RuntimeError(f"expected selected chunks in compact retrieval payload: {payload}")
    if len(selected_chunks) > 3:
        raise RuntimeError(f"too many selected chunks in compact retrieval payload: {payload}")
    excerpt_context = payload.get("paper_excerpt_context", [])
    if not isinstance(excerpt_context, list) or excerpt_context[0].get("reference") != "Substructural logics":
        raise RuntimeError(f"unexpected paper excerpt context: {payload}")
    paper_reading_context = payload.get("paper_reading_context", [])
    if not isinstance(paper_reading_context, list) or paper_reading_context[0].get("reference") != "Substructural logics":
        raise RuntimeError(f"unexpected paper reading context: {payload}")
    if "Abstract:" not in str(paper_reading_context[0].get("reading_excerpt", "")):
        raise RuntimeError(f"expected flattened reading excerpt in paper_reading_context: {payload}")
    reading_chunks = paper_reading_context[0].get("reading_chunks", [])
    if not isinstance(reading_chunks, list) or not reading_chunks:
        raise RuntimeError(f"expected reading_chunks in paper_reading_context: {payload}")
    if excerpt_context[0].get("download_relpath") != "downloads/substructural.pdf":
        raise RuntimeError(f"expected local download path in paper excerpt context: {payload}")
    if excerpt_context[0].get("paper_record_relpath") != "papers/substructural.json":
        raise RuntimeError(f"expected paper record path in paper excerpt context: {payload}")
    if payload.get("source_links", [None])[0] != "Substructural logics - https://example.com/substructural":
        raise RuntimeError(f"expected relevant source link first: {payload}")
    if any("StackExchange" in item for item in payload.get("source_links", [])):
        raise RuntimeError(f"qna source link should be filtered from compact retrieval source links: {payload}")
    source_link_entries = payload.get("source_link_entries", [])
    if not isinstance(source_link_entries, list) or source_link_entries[0].get("download_relpath") != "downloads/substructural.pdf":
        raise RuntimeError(f"expected source link entries to retain local access paths: {payload}")


def test_build_paper_claim_retrieval_materials_separates_unreadable_baselines() -> None:
    candidate = {
        "candidate_id": "mt_candidate",
        "statement": "reverse-topological folds characterize exact residual acceptance",
        "docstring_summary": "Canonical computation theorem for reachable residual states.",
        "rationale": "Compare exact residual evaluation against focused proof-search baselines.",
        "supporting_theorems": ["reachable_acceptance_exact"],
        "missing_lemmas": [],
        "theorem_pattern": "framework_introduction",
        "context_note": "Novelty pressure sits near Lambek parsing and focused proof search.",
        "conceptual_depth_note": "Need a theorem-level comparison, not just source-link names.",
    }
    materials = {
        "paper_claim": ["Use source links when novelty pressure matters."],
        "source_link_entries": [
            {
                "label": "Readable baseline",
                "url": "https://example.com/readable.pdf",
                "note": "",
                "source_kind": "repository_pdf",
                "retrieval_priority": "high",
                "direct_reading_access": "direct_fulltext",
            },
            {
                "label": "Unreadable baseline",
                "url": "https://example.com/unreadable.pdf",
                "note": "",
                "source_kind": "scanned_pdf",
                "retrieval_priority": "high",
                "direct_reading_access": "image_only_pdf",
            },
        ],
        "paper_cache": [
            {
                "source_id": "readable",
                "title": "Readable baseline",
                "source_url": "https://example.com/readable.pdf",
                "extract_confidence": "high",
                "source_kind": "repository_pdf",
                "retrieval_priority": "high",
                "direct_reading_access": "direct_fulltext",
                "abstract": "A readable baseline about focused proof search.",
                "chunks": [
                    {
                        "chunk_id": "chunk_001",
                        "section": "Abstract",
                        "page": None,
                        "text": "Focused proof search yields canonical derivations.",
                    }
                ],
                "paper_record_relpath": "papers/readable.json",
                "paper_record_path": "/tmp/materials_cache/papers/readable.json",
                "download_relpath": "downloads/readable.pdf",
                "download_path": "/tmp/materials_cache/downloads/readable.pdf",
            },
            {
                "source_id": "unreadable",
                "title": "Unreadable baseline",
                "source_url": "https://example.com/unreadable.pdf",
                "extract_confidence": "low",
                "source_kind": "scanned_pdf",
                "retrieval_priority": "high",
                "direct_reading_access": "image_only_pdf",
                "abstract": "",
                "chunks": [],
                "paper_record_relpath": "papers/unreadable.json",
                "paper_record_path": "/tmp/materials_cache/papers/unreadable.json",
                "download_relpath": "downloads/unreadable.pdf",
                "download_path": "/tmp/materials_cache/downloads/unreadable.pdf",
            },
        ],
    }

    payload = paper_claim_session._build_paper_claim_retrieval_materials(candidate, materials)
    paper_cache = payload.get("paper_cache", [])
    if not isinstance(paper_cache, list) or len(paper_cache) != 1:
        raise RuntimeError(f"expected only readable paper_cache entries: {payload}")
    if paper_cache[0].get("title") != "Readable baseline":
        raise RuntimeError(f"unexpected readable paper retained: {payload}")
    excerpt_context = payload.get("paper_excerpt_context", [])
    if not isinstance(excerpt_context, list) or len(excerpt_context) != 1:
        raise RuntimeError(f"expected only readable excerpt context entries: {payload}")
    limitations = payload.get("literature_limitations", [])
    if not isinstance(limitations, list) or len(limitations) != 1:
        raise RuntimeError(f"expected one literature limitation entry: {payload}")
    if limitations[0].get("reference") != "Unreadable baseline":
        raise RuntimeError(f"unexpected literature limitation reference: {payload}")
    if limitations[0].get("direct_reading_access") != "image_only_pdf":
        raise RuntimeError(f"expected image-only limitation metadata: {payload}")
    paper_claim_notes = payload.get("paper_claim", [])
    if not any("unresolved novelty risk" in str(item) for item in paper_claim_notes):
        raise RuntimeError(f"expected paper_claim note about unresolved novelty risk: {payload}")


def test_retrieval_scoring_penalizes_incidental_body_overlap_without_title_match() -> None:
    query_terms = {"weakening", "contraction", "substructural"}
    relevant_record = {
        "title": "Substructural logics with weakening and contraction",
        "abstract": "Weakening and contraction classify nearby substructural systems.",
        "extract_confidence": "high",
        "source_kind": "preprint_pdf",
        "retrieval_priority": "high",
        "direct_reading_access": "direct_fulltext",
        "chunks": [
            {"chunk_id": "c1", "section": "Abstract", "page": None, "text": "Weakening and contraction classify systems."}
        ],
    }
    incidental_record = {
        "title": "Logical inferentialism and classical logic",
        "abstract": "A background section briefly mentions Lambek and substructural traditions.",
        "extract_confidence": "high",
        "source_kind": "preprint_pdf",
        "retrieval_priority": "high",
        "direct_reading_access": "direct_fulltext",
        "chunks": [
            {"chunk_id": "c1", "section": "Background", "page": None, "text": "Lambek and substructural traditions are mentioned in passing."}
        ],
    }
    relevant_score = paper_claim_session._score_retrieval_paper(query_terms, relevant_record)
    incidental_score = paper_claim_session._score_retrieval_paper(query_terms, incidental_record)
    if relevant_score <= incidental_score:
        raise RuntimeError(
            f"title-matched paper should outrank incidental overlap: relevant={relevant_score}, incidental={incidental_score}"
        )


def test_force_refresh_writes_research_agenda_to_theory_state() -> None:
    agenda = {
        "themes": ["bridge theorem clusters"],
        "valued_problem_types": ["classification results"],
        "anti_goals": ["cosmetic rewrites"],
        "canonical_targets": ["exact boundary results"],
        "soft_constraints": ["stay close to the active theory"],
    }
    with tempfile.TemporaryDirectory() as tmpdir:
        data_dir = Path(tmpdir)
        write_jsonl_atomic(
            data_dir / "open_problems.jsonl",
            [
                {
                    "id": "op_000001",
                    "stmt": "True",
                    "priority": "unknown",
                    "priority_rationale": "",
                    "failure_count": 0,
                }
            ],
        )
        write_jsonl_atomic(data_dir / "archived_problems.jsonl", [])
        write_jsonl_atomic(data_dir / "counterexamples.jsonl", [])

        original_request = run_loop.request_open_problem_priorities
        original_load_prompt_text = run_loop.load_prompt_text
        original_load_current_guidance = run_loop.load_current_guidance
        try:
            run_loop.load_prompt_text = lambda _path: ""
            run_loop.load_current_guidance = lambda _data_dir: build_guidance_context(
                theory_state={},
                research_agenda=agenda,
            )

            def fake_request_open_problem_priorities(**_kwargs):
                return (
                    [
                        {
                            "problem_id": "op_000001",
                            "priority": "high",
                            "rationale": "agenda-aligned bridge problem",
                        }
                    ],
                    "Agenda-shaped snapshot.",
                    {
                        "label": "bridge_clusters",
                        "guidance": "Prefer bridge lemmas.",
                        "rationale": "They match the active agenda.",
                    },
                    {
                        "desired_summary_changes": [],
                        "current_bottlenecks": [],
                        "overexplored_patterns": [],
                        "missing_bridges": [],
                        "agenda_pressure": [],
                    },
                    {"worker": "research_agenda_test"},
                )

            run_loop.request_open_problem_priorities = fake_request_open_problem_priorities
            ran, error, _ = run_loop.force_refresh_open_problem_priorities(
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
            run_loop.load_current_guidance = original_load_current_guidance

        if not ran or error:
            raise RuntimeError(f"priority refresh unexpectedly failed: {error}")

        theory_state = json.loads((data_dir / "theory_state.json").read_text(encoding="utf-8"))
        expected_summary = summarize_research_agenda_for_state(agenda)
        if theory_state.get("research_agenda") != expected_summary:
            raise RuntimeError(f"unexpected research_agenda in theory_state: {theory_state}")


def test_run_llm_uses_env_model_and_retries_without_model_on_capacity() -> None:
    original_run_llm_exec = generate_seeds_from_theory.run_llm_exec
    original_model = os.environ.get("ATC_CODEX_MODEL")
    calls: list[str | None] = []

    try:
        os.environ["ATC_CODEX_MODEL"] = "gpt-5.4"

        def fake_run_llm_exec(
            *,
            provider,
            prompt,
            sandbox,
            model=None,
            cwd=None,
            output_schema_path=None,
            output_last_message_path=None,
            timeout_sec=None,
            capture_output=True,
        ):
            calls.append(model)
            if len(calls) == 1:
                return subprocess.CompletedProcess(
                    args=["codex"],
                    returncode=1,
                    stdout="",
                    stderr="Selected model is at capacity",
                )
            if output_last_message_path is not None:
                Path(output_last_message_path).write_text('{"seeds":["seed A"]}', encoding="utf-8")
            return subprocess.CompletedProcess(
                args=["codex"],
                returncode=0,
                stdout="",
                stderr="",
            )

        generate_seeds_from_theory.run_llm_exec = fake_run_llm_exec
        output = generate_seeds_from_theory.run_llm(
            prompt="prompt",
            schema={"type": "object"},
            repo_root=REPO_ROOT,
            sandbox="read-only",
            provider="codex",
            model=None,
        )
    finally:
        generate_seeds_from_theory.run_llm_exec = original_run_llm_exec
        if original_model is None:
            os.environ.pop("ATC_CODEX_MODEL", None)
        else:
            os.environ["ATC_CODEX_MODEL"] = original_model

    if output != '{"seeds":["seed A"]}':
        raise RuntimeError(f"unexpected output: {output}")
    if calls != ["gpt-5.4", None]:
        raise RuntimeError(f"expected capacity fallback to clear model, got calls={calls}")


def test_run_llm_includes_stderr_when_final_message_missing() -> None:
    original_run_llm_exec = generate_seeds_from_theory.run_llm_exec

    try:
        def fake_run_llm_exec(
            *,
            provider,
            prompt,
            sandbox,
            model=None,
            cwd=None,
            output_schema_path=None,
            output_last_message_path=None,
            timeout_sec=None,
            capture_output=True,
        ):
            return subprocess.CompletedProcess(
                args=["codex"],
                returncode=0,
                stdout="",
                stderr="transport closed before final response",
            )

        generate_seeds_from_theory.run_llm_exec = fake_run_llm_exec
        try:
            generate_seeds_from_theory.run_llm(
                prompt="prompt",
                schema={"type": "object"},
                repo_root=REPO_ROOT,
                sandbox="read-only",
                provider="codex",
                model="gpt-5.4",
            )
        except RuntimeError as exc:
            message = str(exc)
        else:
            raise RuntimeError("expected run_llm to fail on missing final message")
    finally:
        generate_seeds_from_theory.run_llm_exec = original_run_llm_exec

    if "returned no final message" not in message:
        raise RuntimeError(f"missing base diagnostic: {message}")
    if "stderr=transport closed before final response" not in message:
        raise RuntimeError(f"missing stderr diagnostic: {message}")
    if "model=gpt-5.4" not in message:
        raise RuntimeError(f"missing model diagnostic: {message}")


def main() -> int:
    test_parse_research_agenda_markdown_extracts_sections()
    test_parse_research_agenda_markdown_handles_numbered_headings_and_ignores_paragraphs()
    test_load_research_agenda_missing_file_is_empty()
    test_load_research_agenda_falls_back_to_legacy_root_file()
    test_render_research_agenda_user_prompt_substitutes_placeholders()
    test_validate_generated_agenda_requires_all_sections()
    test_ensure_materials_derived_current_generates_files_from_root_report()
    test_seed_prompt_includes_research_agenda_guidance()
    test_runtime_initialization_clears_generation_sidecar_files()
    test_worker_payloads_include_research_agenda()
    test_build_paper_claim_retrieval_materials_prefilters_paper_cache()
    test_build_paper_claim_retrieval_materials_separates_unreadable_baselines()
    test_force_refresh_writes_research_agenda_to_theory_state()
    test_run_llm_uses_env_model_and_retries_without_model_on_capacity()
    test_run_llm_includes_stderr_when_final_message_missing()
    print("research agenda test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
