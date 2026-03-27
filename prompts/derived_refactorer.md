# Derived Refactorer

You refactor `AutomatedTheoryConstruction/Derived.lean` into a smaller, more reusable theorem inventory.

Primary goal:
- Return one full replacement file for `Derived.lean` that still typechecks and reduces clutter from duplicate, equivalent, or low-value closure lemmas.
- Prefer a compact, library-like theorem file rather than a chronological theorem dump.

Hard constraints:
- Output a full Lean file in `refactored_code`, not a patch, diff, markdown block, or prose.
- Preserve a valid standalone Lean module shape: imports, namespace, theorem declarations, and closing `end`.
- Do not introduce `sorry`.
- If you cannot confidently produce a valid replacement file, return `stuck`.

Refactoring policy:
- Treat `derived_code` as the current source of truth and `theory_context` as the ambient base theory.
- Prefer one canonical theorem per mathematical fact.
- Merge exact duplicates and near-duplicates when one theorem clearly subsumes the others.
- Reduce one-line closure lemmas and mechanical restatements when they do not add reusable theory content.
- If removing a theorem name would likely hurt compatibility, keep it as a very short alias theorem pointing to the canonical result.
- Prefer keeping stronger and more reusable statements over weaker wrappers.
- Strengthen the dependency structure of the file: prefer a small base of reusable core lemmas and derive downstream statements from those lemmas rather than reproving similar facts repeatedly.
- Reorder declarations aggressively when it improves the dependency graph, locality, and theorem reuse.
- Prefer a style closer to a curated library file such as Mathlib's `Basic.lean`: small canonical lemmas first, theorem families grouped by concept, lightweight aliases only when compatibility is important, and minimal theorem spam.
- Prefer a bottom-up arrangement: foundational equivalence/monotonicity lemmas first, then structural existence/uniqueness lemmas, then consequence theorems and specialized corollaries.
- If several theorems express the same fact at different strengths, keep the best reusable version as canonical and make weaker variants aliases only if they are still worth keeping.
- For main-theorem-style results, prefer proofs that explicitly reuse existing `Derived.lean` theorems rather than reproving the same structure directly from axioms whenever a stable reuse path exists.
- Preserve semantically useful theorem names when possible; avoid renaming everything just for style.
- If `exact_duplicate_statement_groups` is non-empty, treat those groups as high-priority cleanup targets.
- Use `refactor_goals` as strict guidance for style and structure.
- If `repair_round > 0`, treat `current_candidate_code` / `previous_refactored_code` as the current candidate and repair that file incrementally rather than regenerating from scratch.
- On repair rounds, make the smallest edits that address the current Lean diagnostics, keep already-working regions intact, and preserve the current theorem ordering unless diagnostics or dependency cleanup require a local reorder.
- Follow `repair_strategy` strictly: produce one improved candidate, expect the outer loop to run `lake env lean`, then use the next diagnostics for the next small repair.
- `change_notes` should mention the main theorem clusters you merged, dropped, or kept as aliases.

Output schema:
{
  "result": "ok|stuck",
  "refactored_code": "full replacement Derived.lean file, or empty when stuck",
  "summary": "short summary of the refactor",
  "change_notes": ["short note", "short note"]
}
