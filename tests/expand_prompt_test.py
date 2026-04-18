from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


def test_solved_proof_prompt_limits_statement_bloat() -> None:
    prompt = (REPO_ROOT / "prompts" / "expander" / "solved_proof.md").read_text(encoding="utf-8")
    required_snippets = (
        "Prefer the shortest statement that captures the reusable idea.",
        "Do not bundle multiple conclusions, regimes, or case splits into one candidate.",
        "Avoid long hypothesis stacks unless each hypothesis is essential to a single sharp claim.",
        "If a candidate can be split into a cleaner core theorem and a later corollary, return only the core theorem.",
        "statements that combine several theorem-sized ideas into one candidate",
        "statements with long scaffolding or multiple nonessential qualifiers",
        "conjunction-style candidates that should be split into separate problems",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing solved-proof expand guidance: {snippet}")


def test_post_theorem_prompt_limits_statement_bloat() -> None:
    prompt = (REPO_ROOT / "prompts" / "expander" / "post_theorem.md").read_text(encoding="utf-8")
    required_snippets = (
        "Prefer the shortest statement that captures the reusable idea.",
        "Do not bundle multiple conclusions, regimes, or case splits into one candidate.",
        "Avoid long hypothesis stacks unless each hypothesis is essential to a single sharp claim.",
        "If a candidate can be split into a cleaner core theorem and a later corollary, return only the core theorem.",
        "statements that combine several theorem-sized ideas into one candidate",
        "statements with long scaffolding or multiple nonessential qualifiers",
        "conjunction-style candidates that should be split into separate problems",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing post-theorem expand guidance: {snippet}")


def main() -> int:
    test_solved_proof_prompt_limits_statement_bloat()
    test_post_theorem_prompt_limits_statement_bloat()
    print("expand prompt test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
