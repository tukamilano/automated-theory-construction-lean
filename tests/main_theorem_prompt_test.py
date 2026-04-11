from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


def test_suggester_prompt_preserves_main_theorem_language() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "suggester.md").read_text(encoding="utf-8")
    required_snippets = (
        "conceptual compression",
        "corollaries, helpers, or special cases",
        "mature relative to the currently verified material",
        "desired_summary_changes",
        "missing_bridges",
        "overexplored_patterns",
        "There is no abstain path.",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing preserved suggester guidance: {snippet}")


def test_suggester_prompt_adds_selector_publishability_guidance() -> None:
    prompt = (REPO_ROOT / "prompts" / "main_theorem" / "suggester.md").read_text(encoding="utf-8")
    required_snippets = (
        "paper-worthy summary theorem candidate",
        "Use `Derived.lean` as the primary grounding source",
        "raw material, negative evidence, and dominance-check context",
        "reconstruct a stronger summary theorem",
        "Do not behave like a local problem expander.",
        "title-level result",
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
            raise RuntimeError(f"missing new selector guidance: {snippet}")


def test_planner_prompt_is_removed() -> None:
    planner_prompt = REPO_ROOT / "prompts" / "main_theorem" / "planner.md"
    if planner_prompt.exists():
        raise RuntimeError(f"planner prompt should be removed, but still exists: {planner_prompt}")


def main() -> int:
    test_suggester_prompt_preserves_main_theorem_language()
    test_suggester_prompt_adds_selector_publishability_guidance()
    test_planner_prompt_is_removed()
    print("main theorem prompt test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
