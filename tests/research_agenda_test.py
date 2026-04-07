from __future__ import annotations

import sys
import tempfile
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import generate_seeds_from_theory
import run_loop
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
        theory_state={},
        research_agenda={
            "themes": ["bridge theorem clusters"],
            "valued_problem_types": ["classification results"],
            "anti_goals": ["cosmetic rewrites"],
            "canonical_targets": ["exact boundary results"],
            "soft_constraints": ["stay close to the active theory"],
        },
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
            raise RuntimeError(f"unexpected task_type: {task_type}")

        run_loop.invoke_worker_json = fake_invoke_worker_json

        run_loop.request_open_problem_priorities(
            worker_settings={},
            prioritizer_prompt="unused",
            tracked_rows=[{"id": "op_000001", "stmt": "True", "src": "seed"}],
            derived_entries=[],
            current_iteration=1,
            previous_theory_state={},
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
        )
    finally:
        run_loop.invoke_worker_json = original_invoke_worker_json
        run_loop.load_current_research_agenda = original_load_current_research_agenda

    for task_type in ("prioritize_open_problems", "expand"):
        payload = captured_payloads.get(task_type)
        if payload is None:
            raise RuntimeError(f"missing captured payload for {task_type}")
        if payload.get("research_agenda") != agenda:
            raise RuntimeError(f"missing research_agenda in {task_type} payload: {payload}")


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
    test_load_research_agenda_missing_file_is_empty()
    test_load_research_agenda_falls_back_to_legacy_root_file()
    test_seed_prompt_includes_research_agenda_guidance()
    test_worker_payloads_include_research_agenda()
    test_force_refresh_writes_research_agenda_to_theory_state()
    print("research agenda test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
