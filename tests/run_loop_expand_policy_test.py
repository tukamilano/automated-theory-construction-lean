from __future__ import annotations

import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))


import run_loop


def test_expand_prompts_include_soft_diversity_guidance() -> None:
    solved_prompt = run_loop.load_prompt_text("prompts/expander/solved_proof.md")
    post_theorem_prompt = run_loop.load_prompt_text("prompts/expander/post_theorem.md")

    common_snippets = (
        "When multiple strong candidates are available, prefer a diverse spread",
        "`generalization`, `converse`, `boundary`, `separation`, `criterion`, `reusable_lemma`",
        "Treat each candidate by one dominant role only.",
        "Do not count shallow variants from the same family as meaningfully distinct.",
        "Do not return multiple candidates that repeat the same obstruction, the same repair idea, or the same near-neighbor statement unless those are clearly the strongest options.",
        "Do not sacrifice the strongest candidate merely to create role spread.",
    )
    for snippet in common_snippets:
        if snippet not in solved_prompt:
            raise RuntimeError(f"missing solved_proof diversity snippet: {snippet}")
        if snippet not in post_theorem_prompt:
            raise RuntimeError(f"missing post_theorem diversity snippet: {snippet}")

    post_theorem_specific = (
        "Around a newly resolved main theorem, prefer covering `converse`, `boundary`, `separation`, and `criterion` before adding multiple candidates from the same family.",
    )
    for snippet in post_theorem_specific:
        if snippet not in post_theorem_prompt:
            raise RuntimeError(f"missing post_theorem-specific diversity snippet: {snippet}")


def main() -> int:
    test_expand_prompts_include_soft_diversity_guidance()

    if not run_loop.is_verified_resolution(verify_success=True, result="proof"):
        raise RuntimeError("verified proof should count as a resolved outcome")

    if not run_loop.is_verified_resolution(verify_success=True, result="counterexample"):
        raise RuntimeError("verified counterexample should count as a resolved outcome")

    if run_loop.is_verified_resolution(verify_success=False, result="proof"):
        raise RuntimeError("unverified proof must not count as a resolved outcome")

    if run_loop.is_verified_resolution(verify_success=True, result="stuck"):
        raise RuntimeError("stuck results must not count as a resolved outcome")

    if not run_loop.should_generate_expand_candidates(verify_success=True, result="proof"):
        raise RuntimeError("verified proof should trigger expand generation")

    if not run_loop.should_generate_expand_candidates(verify_success=True, result="counterexample"):
        raise RuntimeError("verified counterexample should trigger expand generation")

    if run_loop.should_generate_expand_candidates(verify_success=True, result="stuck"):
        raise RuntimeError("stuck results must not trigger expand generation")

    if run_loop.should_generate_expand_candidates(verify_success=False, result="proof"):
        raise RuntimeError("unverified proof must not trigger expand generation")

    if run_loop.should_generate_expand_candidates(verify_success=False, result="counterexample"):
        raise RuntimeError("unverified counterexample must not trigger expand generation")

    accepted = run_loop.validate_problem_candidates_output(
        {
            "problem_id": "op_000001",
            "candidates": [
                {"statement": "A", "rationale": "r1"},
                {"statement": "B", "rationale": "r2"},
                {"statement": "C", "rationale": "r3"},
            ],
        },
        expected_problem_id="op_000001",
        max_candidates=run_loop.MAX_EXPAND_CANDIDATES_PER_SOLVED_PROOF,
    )
    if len(accepted) != 3:
        raise RuntimeError(f"solved-proof expand should accept 3 candidates, got {accepted}")

    try:
        run_loop.validate_problem_candidates_output(
            {
                "problem_id": "op_000001",
                "candidates": [
                    {"statement": "A", "rationale": "r1"},
                    {"statement": "B", "rationale": "r2"},
                    {"statement": "C", "rationale": "r3"},
                    {"statement": "D", "rationale": "r4"},
                ],
            },
            expected_problem_id="op_000001",
            max_candidates=run_loop.MAX_EXPAND_CANDIDATES_PER_SOLVED_PROOF,
        )
    except ValueError:
        pass
    else:
        raise RuntimeError("solved-proof expand should reject more than 3 candidates")

    print("run loop expand policy test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
