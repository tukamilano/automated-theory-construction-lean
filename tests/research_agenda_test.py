from __future__ import annotations

import sys
import tempfile
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import generate_seeds_from_theory
import run_loop
from guidance import build_guidance_context
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


def test_runtime_initialization_clears_generation_sidecar_files() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir)
        data_dir = tmp_path / "data"
        seeds_file = tmp_path / "seeds.jsonl"
        scratch_file = tmp_path / "Scratch.lean"
        derived_file = tmp_path / "Derived.lean"
        formalization_memory_file = data_dir / "formalization_memory.json"
        archived_problems_file = data_dir / "archived_problems.jsonl"
        theorem_reuse_memory_file = data_dir / "theorem_reuse_memory.json"

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


def test_worker_payloads_include_research_agenda() -> None:
    agenda = {
        "themes": ["bridge theorem clusters"],
        "valued_problem_types": ["classification results"],
        "anti_goals": ["cosmetic rewrites"],
        "canonical_targets": ["exact boundary results"],
        "soft_constraints": ["stay close to the active theory"],
    }
    captured_payloads: dict[str, dict[str, object]] = {}
    original_invoke_worker_json = run_loop.invoke_worker_json
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
            if task_type == "main_theorem_suggest":
                return (
                    {
                        "candidate_id": "mt_manual",
                        "result": "stuck",
                        "statement": "",
                        "theorem_name_stem": "",
                        "docstring_summary": "",
                        "rationale": "agenda-aligned but not yet ready",
                        "supporting_theorems": [],
                        "missing_lemmas": [],
                    },
                    {"worker": "research_agenda_test"},
                )
            raise RuntimeError(f"unexpected task_type: {task_type}")

        run_loop.invoke_worker_json = fake_invoke_worker_json

        run_loop.request_open_problem_priorities(
            worker_settings={},
            prioritizer_prompt="unused",
            tracked_rows=[{"id": "op_000001", "stmt": "True", "src": "seed"}],
            derived_entries=[],
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda),
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
            max_candidates=2,
        )
        run_loop.request_main_theorem_suggestion(
            worker_settings={},
            suggester_prompt="unused",
            candidate_id="mt_manual",
            derived_entries=[],
            theory_context="",
            tracked_rows=[{"id": "op_000001", "stmt": "True", "src": "seed"}],
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda),
        )
    finally:
        run_loop.invoke_worker_json = original_invoke_worker_json
        run_loop.load_current_research_agenda = original_load_current_research_agenda

    for task_type in ("prioritize_open_problems", "expand", "main_theorem_suggest"):
        payload = captured_payloads.get(task_type)
        if payload is None:
            raise RuntimeError(f"missing captured payload for {task_type}")
        if payload.get("research_agenda") != agenda:
            raise RuntimeError(f"missing research_agenda in {task_type} payload: {payload}")
        if payload.get("theory_state") != {} and task_type != "prioritize_open_problems":
            raise RuntimeError(f"unexpected theory_state in {task_type} payload: {payload}")
    priority_payload = captured_payloads.get("prioritize_open_problems", {})
    if priority_payload.get("previous_theory_state") != {}:
        raise RuntimeError(f"unexpected previous_theory_state in prioritize_open_problems payload: {priority_payload}")


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
        original_load_current_research_agenda = run_loop.load_current_research_agenda
        try:
            run_loop.load_prompt_text = lambda _path: ""
            run_loop.load_current_research_agenda = lambda: agenda

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
            run_loop.load_current_research_agenda = original_load_current_research_agenda

        if not ran or error:
            raise RuntimeError(f"priority refresh unexpectedly failed: {error}")

        theory_state = json.loads((data_dir / "theory_state.json").read_text(encoding="utf-8"))
        expected_summary = summarize_research_agenda_for_state(agenda)
        if theory_state.get("research_agenda") != expected_summary:
            raise RuntimeError(f"unexpected research_agenda in theory_state: {theory_state}")


def main() -> int:
    test_parse_research_agenda_markdown_extracts_sections()
    test_parse_research_agenda_markdown_handles_numbered_headings_and_ignores_paragraphs()
    test_load_research_agenda_missing_file_is_empty()
    test_load_research_agenda_falls_back_to_legacy_root_file()
    test_seed_prompt_includes_research_agenda_guidance()
    test_runtime_initialization_clears_generation_sidecar_files()
    test_worker_payloads_include_research_agenda()
    test_force_refresh_writes_research_agenda_to_theory_state()
    print("research agenda test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
