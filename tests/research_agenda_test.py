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
import run_loop
from guidance import build_guidance_context
from main_theorem import main_theorem_session
from main_theorem.main_theorem_session import request_main_theorem_candidate_set
from main_theorem.main_theorem_session import request_main_theorem_selection
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
        data_dir.mkdir(parents=True, exist_ok=True)
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
    original_main_theorem_invoke_worker_json = main_theorem_session.invoke_worker_json
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
            if task_type == "main_theorem_generate":
                return (
                    {
                        "candidate_set_id": "mt_main_theorem",
                        "candidates": [
                            {
                                "candidate_rank_seed": 1,
                                "statement": "True",
                                "theorem_name_stem": "agenda_main_theorem_summary",
                                "docstring_summary": "Agenda summary placeholder theorem.",
                                "rationale": "agenda-aligned structural summary candidate",
                                "supporting_theorems": [],
                                "missing_lemmas": [],
                                "source_problem_ids": ["op_000001"],
                                "theorem_pattern": "structure_discovery",
                                "context_note": "The summary candidate is positioned as a compression of the active queue and visible derived cluster.",
                                "conceptual_depth_note": "The summary candidate is treated as a structural summary, not a local technical lemma.",
                            },
                            {
                                "candidate_rank_seed": 2,
                                "statement": "True -> True",
                                "theorem_name_stem": "agenda_main_theorem_bridge",
                                "docstring_summary": "Agenda bridge placeholder theorem.",
                                "rationale": "agenda-aligned bridge candidate",
                                "supporting_theorems": [],
                                "missing_lemmas": [],
                                "source_problem_ids": ["op_000001"],
                                "theorem_pattern": "new_theorem",
                                "context_note": "The bridge candidate is positioned as the strongest title-level summary theorem in the placeholder fixture.",
                                "conceptual_depth_note": "The bridge candidate is treated as a reusable structural bridge.",
                            },
                            {
                                "candidate_rank_seed": 3,
                                "statement": "True ∧ True",
                                "theorem_name_stem": "agenda_main_theorem_framework",
                                "docstring_summary": "Agenda framework placeholder theorem.",
                                "rationale": "agenda-aligned framework candidate",
                                "supporting_theorems": [],
                                "missing_lemmas": [],
                                "source_problem_ids": ["op_000001"],
                                "theorem_pattern": "framework_introduction",
                                "context_note": "The framework candidate is positioned as a framework consequence of the placeholder theory.",
                                "conceptual_depth_note": "The framework candidate is treated as a conceptual interface rather than a technical step.",
                            },
                        ],
                    },
                    {"worker": "research_agenda_test"},
                )
            if task_type == "main_theorem_select":
                return (
                    {
                        "candidate_set_id": "mt_main_theorem",
                        "selected_candidate_rank_seed": 2,
                        "selection_summary": "The bridge-style placeholder candidate best matches the active agenda.",
                        "ranking": [
                            {
                                "candidate_rank_seed": 2,
                                "rank": 1,
                                "decision": "select",
                                "reason": "Best matches the agenda's structural bridge pressure.",
                            },
                            {
                                "candidate_rank_seed": 1,
                                "rank": 2,
                                "decision": "reject",
                                "reason": "Good summary, but less decisive than the selected bridge theorem.",
                            },
                            {
                                "candidate_rank_seed": 3,
                                "rank": 3,
                                "decision": "reject",
                                "reason": "More framework-oriented and less direct than the selected theorem.",
                            },
                        ],
                    },
                    {"worker": "research_agenda_test"},
                )
            raise RuntimeError(f"unexpected task_type: {task_type}")

        run_loop.invoke_worker_json = fake_invoke_worker_json
        main_theorem_session.invoke_worker_json = fake_invoke_worker_json

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
        candidates, _ = request_main_theorem_candidate_set(
            worker_settings={},
            generator_prompt="unused",
            candidate_set_id="mt_main_theorem",
            derived_entries=[],
            theory_context="",
            tracked_rows=[{"id": "op_000001", "stmt": "True", "src": "seed"}],
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda),
        )
        request_main_theorem_selection(
            worker_settings={},
            selector_prompt="unused",
            candidate_set_id="mt_main_theorem",
            candidates=candidates,
            derived_entries=[],
            theory_context="",
            tracked_rows=[{"id": "op_000001", "stmt": "True", "src": "seed"}],
            current_iteration=1,
            guidance=build_guidance_context(theory_state={}, research_agenda=agenda),
        )
    finally:
        run_loop.invoke_worker_json = original_invoke_worker_json
        main_theorem_session.invoke_worker_json = original_main_theorem_invoke_worker_json
        run_loop.load_current_research_agenda = original_load_current_research_agenda

    for task_type in ("prioritize_open_problems", "expand", "main_theorem_generate", "main_theorem_select"):
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
    test_seed_prompt_includes_research_agenda_guidance()
    test_runtime_initialization_clears_generation_sidecar_files()
    test_worker_payloads_include_research_agenda()
    test_force_refresh_writes_research_agenda_to_theory_state()
    test_run_llm_uses_env_model_and_retries_without_model_on_capacity()
    test_run_llm_includes_stderr_when_final_message_missing()
    print("research agenda test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
