You are running the paper-claim proof session for this repository.

Follow `.codex/AGENTS.md`, `.codex/skills/lean-rule/SKILL.md`, and `.codex/skills/mathlib-usage/SKILL.md`.

Work only on `AutomatedTheoryConstruction/Scratch.lean`.

Rules:
- Use a skeleton-first workflow.
- Start by writing a small, realistic theorem/lemma skeleton in `Scratch.lean`, then refine it through Lean feedback.
- You may refine the theorem statement if needed.
- You may add helper lemmas or local definitions.
- Keep the final Lean code tight:
  - avoid theorem-local wrappers like `have h : <same statement> := by ...; exact h`,
  - avoid `by exact h` when `exact h` is enough,
  - if the target is a direct corollary of an existing theorem with the same shape, prefer `simpa using ...` directly in the theorem body,
  - introduce a `have` only when it changes the goal shape, records a reusable intermediate fact, or makes the proof materially clearer.
- Temporary `sorry` is allowed during exploration when it helps expose dependencies or unblock local proof search.
- Do not edit `AutomatedTheoryConstruction/Derived.lean`.
- Do not edit files under `AutomatedTheoryConstruction/Generated/`.
- Use `lake env lean AutomatedTheoryConstruction/Scratch.lean` to check progress.
- `status = ok` requires that `Scratch.lean` verifies and contains no relevant `sorry`.
- If you return `blocked`, briefly explain the remaining holes or blockers in `notes`.

Goal:
- Starting from the current unit in the selected paper-claim plan, make real Lean proof progress in `Scratch.lean`.
- Treat `paper_claim_plan.formalization_order` as the package order. The orchestrator will call you repeatedly for later units after earlier verified units are committed.
- Focus on the current unit, but you may introduce small local defs/abbrevs if they shorten the theorem face or unblock proof search.
- Only report a unit as refuted when `Scratch.lean` itself verifies a genuine mathematical contradiction, obstruction, or counterexample direction against that unit.
- Stop only when either:
  - `Scratch.lean` verifies cleanly without relevant `sorry`, or
  - you are genuinely blocked.

Output:
- Return exactly one JSON object.
- Use this schema:
  - `status`: `ok` or `blocked` or `timeout`
  - `current_focus_unit_id`: the unit you worked on in this attempt
  - `completed_unit_ids`: plan unit ids that are now genuinely completed by the verified scratch result
  - `refuted_unit_ids`: plan unit ids that the verified scratch result genuinely refutes; keep this empty for ordinary Lean failure or missing lemmas
  - `final_theorem_name`: final primary theorem name in `Scratch.lean`
  - `final_statement`: final primary theorem statement as a single string
  - `helper_theorems`: array of helper theorem names added in `Scratch.lean`
  - `verify_success`: boolean self-report
  - `error_excerpt`: short Lean error excerpt when blocked, else empty string
  - `notes`: short summary of what changed or where progress stopped
