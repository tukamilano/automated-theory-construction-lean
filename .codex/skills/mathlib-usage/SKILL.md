---
name: mathlib-usage
description: Mathlib usage principles (imports, search, existence checks, confirmation) for all `.lean` files in this repo.
---

# Mathlib usage principles

## Basics

- Assume `import Mathlib`. Use Mathlib defs/lemmas/theorems without extra imports.
- Add imports sparingly (aim 1–3 lines) and comment why.
- Prefer `open` / `open scoped` / `local` instead of extra imports.
- Do not add imports for one-off experiments.
- Try existing Mathlib lemmas first; only if absent, add a minimal helper lemma (1–3 lines to close).
- Never invent lemma names; confirm they exist before use.
- Do not ask the user which lemma to try if the answer can be found from local search, diagnostics, or a small confirmation snippet.

## Suggested search flow

0. If `.lake/packages/mathlib/Mathlib` is missing, run `lake update`.
1. Build keywords.
   - Use synonyms (JP/EN, case variants).
   - Include typeclass/structure names.
   - When notation is involved, search by string as needed.
2. Narrow with `rg -n "<keyword>" .lake/packages/mathlib/Mathlib`.
3. Read hits; check prerequisites, related lemmas, and `[simp]` attributes.
4. Confirm existence via `#check` or a tiny snippet.
5. Confirm finally with `lake env lean path/to/File.lean`.
6. Only ask the user for guidance if the statement direction or intended API choice remains genuinely ambiguous after the above checks.

## Tactic preference order

### 1. Local cleanup

- `rw`
- `simpa`
- `simp only [...]`
- `simp_rw [...]`

Handle subgoal rewrites here first.

### 2. Specialized tactics

- `fun_prop`
- `measurability`
- `positivity`
- `finiteness`
- `ring_nf`
- `field_simp`
- `linarith`
- `nlinarith`
- `omega`
- `gcongr`
- `linear_combination`

### 3. Helper automation

- `aesop`
- `grind`

Use these only for small first-order goals; avoid as main weapons for measure/integral/CFC/spectrum goals.

## `simp` rules

- Do not routinely use `simp [*]` on subgoals.
- Do not flood `simp` with AC lemmas like `mul_assoc` / `mul_comm` / `add_assoc` / `add_comm`.
- Do not throw in large definition unfolds without purpose.
- Do not chain fragile `rw` right after `simp`; insert a `have` and `simpa using` it when needed.
- If `simp?` suggests `simp only`, consider pinning it.
- Under binders, use `simp_rw` when order matters.

## Field-specific patterns

### `Continuous*` / `Measurable*` / `Differentiable*`

- Try `fun_prop` first.
- For measure goals, try `measurability`.
- If side goals are order constraints, add `positivity` or short `linarith`.

### `ENNReal` / integrals / measure

- Use `positivity` for nonnegativity.
- Use `finiteness` for finiteness.
- Under binders, prefer `simp_rw`.
- Do not smash `lintegral`, `integral`, `Measure.restrict`, `indicator` with raw `simp [*]`.

### Commutative ring algebra

- Prefer `ring_nf` for normalization.
- Isolate `field_simp` for denominators into tiny helpers.
- Consider `linear_combination` when applicable.

### Matrices / operators / inequalities

- Reduce to scalar side goals first.
- Then try `gcongr` / `positivity` / `linarith` / `nlinarith`.
- For noncommutative products, do not hand AC lemmas to `simp`; use targeted `rw [mul_assoc]` locally.

## LSP helpers

- `lean_term_goal`: expected type at a line
- `lean_goal`: goal/context
- `lean_diagnostic_messages`: distinguish import/typeclass issues
- `lean_multi_attempt`: trial of multiple tactics

Final confirmation is via `rg` / `#check` / `lake env lean`.
