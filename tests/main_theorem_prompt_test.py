from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


def test_generate_prompt_preserves_main_theorem_language() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "generate.md").read_text(encoding="utf-8")
    required_snippets = (
        "conceptual compression",
        "corollaries, helpers, or special cases",
        "mature relative to the currently verified material",
        "desired_summary_changes",
        "missing_bridges",
        "overexplored_patterns",
        "Build 3 materially distinct candidates",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing preserved generator guidance: {snippet}")


def test_generate_prompt_adds_candidate_set_guidance() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "generate.md").read_text(encoding="utf-8")
    required_snippets = (
        "paper-worthy summary theorem candidate",
        "Use `Derived.lean` as the primary grounding source",
        "raw material, negative evidence, and dominance-check context",
        "reconstruct a stronger summary theorem",
        "Do not behave like a local problem expander.",
        "title-level result",
        "\"candidate_set_id\": \"<match input>\"",
        "\"candidate_rank_seed\": 1",
        "\"source_problem_ids\": [\"tracked problem ids that seeded this reconstructed summary theorem\"]",
        "admissible_main_theorem_patterns",
        "research_quality_standard",
        "correctness_boundary",
        "\"theorem_pattern\": \"new_theorem|structure_discovery|framework_introduction\"",
        "\"context_note\": \"short note on relation to known results and boundary evidence\"",
        "\"conceptual_depth_note\": \"short note on the central idea rather than mere technicality\"",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing generator candidate-set guidance: {snippet}")


def test_select_prompt_adds_explicit_ranking_guidance() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "select.md").read_text(encoding="utf-8")
    required_snippets = (
        "You must choose only from the provided `candidates`.",
        "Do not invent a new candidate.",
        "There is no abstain path.",
        "explicit ranking",
        "\"selected_candidate_rank_seed\": 2",
        "\"rank\": 1",
        "\"decision\": \"select\"",
        "\"decision\": \"reject\"",
        "Rejected reasons should explain why the candidate lost relative to the winner",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing selector ranking guidance: {snippet}")


def test_suggester_prompt_uses_rejection_memory() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "suggester.md").read_text(encoding="utf-8")
    required_snippets = (
        "Use `rejected_candidates` as explicit anti-targets.",
        "Treat `rejected_candidates` as hard negative evidence",
        "Do not recycle a previously rejected statement",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing suggester rejection-memory guidance: {snippet}")


def test_evaluator_prompt_is_fail_closed() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "evaluate.md").read_text(encoding="utf-8")
    required_snippets = (
        "Fail-closed evaluator",
        "Default to `reject` unless the evidence clearly supports `pass`.",
        "Treat `pass` as exceptional.",
        "If any pass-gate item is weak, uncertain, or unsupported, do not return `pass`.",
        "\"verdict\": \"pass|revise|reject\"",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing evaluator strictness guidance: {snippet}")


def test_retriever_prompt_uses_prefiltered_paper_excerpt_context() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "retrieve.md").read_text(encoding="utf-8")
    required_snippets = (
        "If `materials.paper_excerpt_context` is available",
        "`paper_excerpt_context`",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing retriever paper excerpt guidance: {snippet}")


def test_planner_prompt_is_removed() -> None:
    planner_prompt = REPO_ROOT / "prompts" / "main_theorem" / "planner.md"
    if planner_prompt.exists():
        raise RuntimeError(f"planner prompt should be removed, but still exists: {planner_prompt}")


def main() -> int:
    test_generate_prompt_preserves_main_theorem_language()
    test_generate_prompt_adds_candidate_set_guidance()
    test_select_prompt_adds_explicit_ranking_guidance()
    test_suggester_prompt_uses_rejection_memory()
    test_evaluator_prompt_is_fail_closed()
    test_retriever_prompt_uses_prefiltered_paper_excerpt_context()
    test_planner_prompt_is_removed()
    print("main theorem prompt test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
