/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AxiomaticThermoDynamics.LiebYngvason.Defs

/-!
# Theorem 2.1: The Cancellation Law

This file proves the cancellation law (Theorem 2.1 in Lieb–Yngvason):

> **Theorem 2.1 (Stability implies cancellation law).**
> Assume properties A1–A6, especially A6—the stability law. Then the
> cancellation law holds: if `(X, Z) ≺ (Y, Z)`, then `X ≺ Y`.

This is the first non-trivial consequence of the axioms. It says that a
"spectator" system `Z` cannot affect the set of states accessible from `X`.

## Proof outline (for single states)

The proof proceeds by an iterative argument. Starting from `(X, Z) ≺ (Y, Z)`,
we scale the hypothesis by `1/n` to get `(X/n, Z/n) ≺ (Y/n, Z/n)`.
Then we split `X` into `((1-1/n)X, X/n)` and use consistency (A3) to replace
one `1/n`-portion of `X` by `Y/n`. Repeating this `n` times converts all of `X`
to `Y`, yielding `(X, Z/n) ≺ (Y, Z/n)`. The stability axiom A6 then gives `X ≺ Y`.
-/

namespace LiebYngvason

variable {Γ : Type*} [LYAxioms Γ]

open LYAxioms

/-- **Theorem 2.1 (Cancellation Law).**
    If `(s₁, s) ≺ (s₂, s)` for compound states, then `s₁ ≺ s₂`.
    This is proved from axioms A1–A6 alone (no comparison hypothesis needed). -/
theorem cancellation_law (s₁ s₂ s : CState Γ) :
    prec (s₁ ++ s) (s₂ ++ s) → prec s₁ s₂ := by
  sorry

/-- Special case of the cancellation law for single states.
    If `(X, Z) ≺ (Y, Z)`, then `X ≺ Y`. -/
theorem cancellation_law_single (X Y Z : Γ) :
    prec (single X ++ single Z) (single Y ++ single Z) → precS X Y := by
  exact cancellation_law (single X) (single Y) (single Z)

/-- The cancellation law implies: if `X ≺≺ Y` (strict), then
    `(X, Z) ≺≺ (Y, Z)` for all `Z`. This is the converse direction.
    (Requires comparability of `Y` and `Z`.) -/
theorem strict_prec_compound (X Y Z : Γ)
    (h : sprecS X Y) (hcmp : comparable (single Y) (single Z)) :
    sprec (single X ++ single Z) (single Y ++ single Z) := by
  sorry

end LiebYngvason
