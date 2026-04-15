from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


def test_problem_design_prompts_exist_and_are_strict() -> None:
    core_extract_prompt = (REPO_ROOT / "prompts" / "problem_design" / "core_extract.md").read_text(encoding="utf-8")
    for snippet in (
        "Builder of one paper-facing dossier for one literature-contextualized theorem cluster.",
        "Given one `cluster_context`, produce one clean theorem-face dossier.",
        "Do not judge whether it should be accepted or rejected.",
        "`core_mathematical_content` should explain what the theorem really says mathematically",
        "\"cluster_id\": \"<match input cluster_id>\"",
        "\"headline_claim\": \"title-level theorem face\"",
        "\"core_mathematical_content\": \"the mathematical core without packaging language\"",
        "\"proof_assets\": [\"relevant verified theorem names, generated assets, or support labels\"]",
    ):
        if snippet not in core_extract_prompt:
            raise RuntimeError(f"missing problem_design core_extract guidance: {snippet}")

    cluster_prompt = (REPO_ROOT / "prompts" / "problem_design" / "cluster.md").read_text(encoding="utf-8")
    for snippet in (
        "Clusterer of the currently visible `Derived` theorem inventory.",
        "Partition the visible verified results into a small number of conceptual clusters.",
        "Return 2-4 clusters.",
        "\"cluster_id\": \"cluster_001\"",
        "\"suspected_support_layer\": [\"claims that likely belong in support rather than as headline theorems\"]",
    ):
        if snippet not in cluster_prompt:
            raise RuntimeError(f"missing problem_design cluster guidance: {snippet}")

    contextualize_prompt = (REPO_ROOT / "prompts" / "problem_design" / "contextualize.md").read_text(encoding="utf-8")
    for snippet in (
        "Literature contextualizer for one verified theorem cluster.",
        "Use `materials.paper_reading_context` and `materials.paper_excerpt_context` as the main direct-reading evidence.",
        "produce `no_go_faces` aggressively",
        "Do not use proximity to `Derived` as negative evidence by itself.",
        "\"headline_viability\": \"promising|unclear|weak\"",
        "\"what_counts_as_real_delta\": [\"theorem-level deltas that would still count from the outside\"]",
        "\"must_clear_for_novelty\": [\"conditions the later proposal must satisfy\"]",
    ):
        if snippet not in contextualize_prompt:
            raise RuntimeError(f"missing problem_design contextualize guidance: {snippet}")


def test_paper_claim_retrieve_prompt_uses_direct_reading_evidence() -> None:
    prompt = (REPO_ROOT / "prompts" / "paper_claim" / "retrieve.md").read_text(encoding="utf-8")
    required_snippets = (
        "Retriever for one paper-claim dossier.",
        "Use `materials.paper_excerpt_context` and `materials.paper_reading_context` as the main direct-reading evidence",
        "If `download_path` or `paper_record_path` is present",
        "Use `materials.literature_limitations` as unresolved risk",
        "\"directly_read_evidence\": [",
        "\"kind\": \"paper_excerpt|paper_record|source_link|report\"",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing paper_claim retrieve guidance: {snippet}")


def test_paper_claim_map_prompt_centers_baseline_delta_and_theorem_face() -> None:
    prompt = (REPO_ROOT / "prompts" / "paper_claim" / "map.md").read_text(encoding="utf-8")
    required_snippets = (
        "baseline delta` and `theorem face` naturalness the main evaluation axes",
        "If `materials.paper_excerpt_context` is available",
        "If `download_path` or `paper_record_path` is present",
        "If the closest dangerous anchor is only title-level or summary-level",
        "Do not say that novelty is wholly unjudgeable merely because one cited anchor is unreadable.",
        "\"theorem_face_assessment\": \"does the dossier read naturally as a theorem unit?\"",
        "\"baseline_delta\": \"best external-facing delta still available\"",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing paper_claim map guidance: {snippet}")


def test_paper_claim_select_prompt_chooses_best_publishable_fit() -> None:
    prompt = (REPO_ROOT / "prompts" / "paper_claim" / "select.md").read_text(encoding="utf-8")
    required_snippets = (
        "Selector for the paper-claim session.",
        "Choose the single dossier that is currently most likely to become a paper-publishable unit.",
        "Do not write a theorem package plan yet.",
        "Judge dossiers by paper-publishable fit",
        "Reuse the old strict paper-unit mindset, but do not fail closed: always choose the best current dossier.",
        "Treat `significance` as: if this dossier were correct, would it change how an outsider organizes or summarizes the theory?",
        "makes several existing results look subordinate or corollary-level",
        "\"paper_publishable_fit\": \"high|medium|low\"",
        "\"selected\": true",
        "\"why_selected\": \"why this dossier was chosen over the others\"",
        "\"why_not_selected\": \"\"",
        "\"planning_focus\": \"one-line instruction for how the next planner should frame the dossier\"",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing paper_claim select guidance: {snippet}")


def test_paper_claim_plan_prompt_writes_sequence_and_proof_flow() -> None:
    prompt = (REPO_ROOT / "prompts" / "paper_claim" / "plan.md").read_text(encoding="utf-8")
    required_snippets = (
        "Planner for the paper-claim session.",
        "Take the already selected dossier package",
        "Write a natural-language package decomposition and proof design.",
        "Do not write Lean tactics or code.",
        "Do not reconsider dossier selection.",
        "Write the package plan as a sequence of theorem units.",
        "Each theorem unit should read like one plausible declaration, but be described in natural language.",
        "`proof_idea` should be a short sequence of concrete mathematical moves, not a slogan.",
        "reducing the claim to an existing characterization,",
        "proving that a local update preserves an invariant,",
        "Bad proof-idea moves include vague phrases like:",
        "Prefer 3-5 proof-idea steps per unit.",
        "Prefer a short entry unit over an overbundled headline theorem.",
        "\"theorem_units\": [",
        "\"role\": \"entry_lemma|support_lemma|headline_theorem|corollary|definition\"",
        "\"kind\": \"lemma|theorem|definition|equivalence\"",
        "\"statement\": \"natural-language statement specific enough to formalize later\"",
        "\"proof_idea\": [",
        "\"First reduce the claim to an existing semantic characterization ...\"",
        "\"formalization_order\": [\"u1\", \"u2\"]",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing paper_claim plan guidance: {snippet}")


def test_paper_claim_codex_prove_workflow_prompt_exists() -> None:
    prompt = (REPO_ROOT / ".codex" / "workflow" / "paper_claim_codex_prove.md").read_text(encoding="utf-8")
    required_snippets = (
        "Work only on `AutomatedTheoryConstruction/Scratch.lean`.",
        "You may refine the theorem statement if needed.",
        "Do not edit `AutomatedTheoryConstruction/Derived.lean`.",
        "Do not edit sidecar theorem files; edit `AutomatedTheoryConstruction/Derived.lean` only.",
        "Use `lake env lean AutomatedTheoryConstruction/Scratch.lean` to check progress.",
        "avoid theorem-local wrappers like `have h : <same statement> := by ...; exact h`",
        "Return exactly one JSON object.",
        "`status`: `ok` or `blocked` or `timeout`",
        "`current_focus_unit_id`",
        "`completed_unit_ids`",
        "`refuted_unit_ids`",
        "`final_theorem_name`",
        "`final_statement`",
        "`helper_theorems`",
    )
    for snippet in required_snippets:
        if snippet not in prompt:
            raise RuntimeError(f"missing paper_claim codex prove guidance: {snippet}")


def main() -> int:
    test_problem_design_prompts_exist_and_are_strict()
    test_paper_claim_retrieve_prompt_uses_direct_reading_evidence()
    test_paper_claim_map_prompt_centers_baseline_delta_and_theorem_face()
    test_paper_claim_select_prompt_chooses_best_publishable_fit()
    test_paper_claim_plan_prompt_writes_sequence_and_proof_flow()
    test_paper_claim_codex_prove_workflow_prompt_exists()
    print("paper claim prompt test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
