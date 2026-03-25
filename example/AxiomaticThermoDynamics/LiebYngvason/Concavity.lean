/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AxiomaticThermoDynamics.LiebYngvason.Entropy

/-!
# Concavity of Entropy and Irreversibility

This file contains results from Sections II.F and II.G of Lieb–Yngvason:

- **Theorem 2.6**: Forward sectors are convex
- **Theorem 2.7**: Convexity of the sets `Sλ`
- **Theorem 2.8**: Concavity of entropy
- **Theorem 2.9**: Carathéodory's principle and irreversible processes
- **Theorem 2.10**: The relation on `Γ × Γ` determines the entropy
- **Theorem 2.11**: Corollary of Theorem 2.10
- **Theorem 2.12**: Diagonal sets determine entropy

## Forward sectors and convexity

The **forward sector** of a state `X` is `Aₓ = { Y ∈ Γ : X ≺ Y }`.
Axiom A7 (convex combination) implies that forward sectors are convex,
and this leads to the concavity of entropy.
-/

namespace LiebYngvason

variable {Γ : Type*} [LYAxioms Γ] [ComparisonHypothesis Γ]

open LYAxioms

/-! ### Theorem 2.6: Forward sectors are convex -/

/-- **Theorem 2.6 (Forward sectors are convex).**
    If `Γ` is a convex state space satisfying A1–A5 and A7 (convex combination),
    then the forward sector `Aₓ = { Y : X ≺ Y }` is a convex subset of `Γ`
    for each `X ∈ Γ`.

    Proof outline: If `X ≺ Y₁` and `X ≺ Y₂`, then by A5 `X ≺ (tX, (1-t)X)`,
    by A3 and A4 `(tX, (1-t)X) ≺ (tY₁, (1-t)Y₂)`, and by A7
    `(tY₁, (1-t)Y₂) ≺ tY₁ + (1-t)Y₂`. -/
theorem forward_sector_convex [AddCommGroup Γ] [Module ℝ Γ]
    (X : Γ) :
    Convex ℝ (forwardSector X) := by
  sorry

/-! ### Theorem 2.8: Concavity of entropy -/

/-- **Theorem 2.8 (Concavity of entropy).**
    If `Γ` is a convex state space and axiom A7 holds in addition to A1–A6 and CH,
    then the canonical entropy `S` is a concave function on `Γ`.

    That is, `S(tX + (1-t)Y) ≥ t·S(X) + (1-t)·S(Y)` for all `X, Y ∈ Γ`
    and `t ∈ [0, 1]`.

    Conversely, if `S` is concave, then axiom A7 holds automatically. -/
theorem entropy_concave [AddCommGroup Γ] [Module ℝ Γ]
    (X₀ X₁ : Γ) (h : sprecS X₀ X₁) :
    ConcaveOn ℝ Set.univ (canonicalEntropy X₀ X₁) := by
  sorry

/-! ### Theorem 2.9: Carathéodory's principle -/

/-- **Theorem 2.9 (Carathéodory's principle and irreversible processes).**
    Under axioms A1–A7, the following are related:

    (1) **Existence of irreversible processes:** For every `X ∈ Γ`,
        there exists `Y ∈ Γ` with `X ≺≺ Y`.

    (2) **Carathéodory's principle:** In every neighborhood of every `X ∈ Γ`,
        there exists `Z ∈ Γ` such that `X ~ Z` is false.

    Statement (1) always implies (2). If forward sectors have nonempty
    interiors, then (2) implies (1). -/
theorem caratheodory_from_irreversibility [TopologicalSpace Γ]
    (h_irrev : ∀ X : Γ, ∃ Y : Γ, sprecS X Y) :
    ∀ X : Γ, ∀ U ∈ nhds X, ∃ Z ∈ U, ¬ equivS X Z := by
  sorry

/-! ### Theorem 2.10: The relation on Γ × Γ determines entropy -/

/-- **Theorem 2.10 (The relation on `Γ × Γ` determines the entropy).**
    If `Γ` is a convex state space, S and S* are two entropy functions
    satisfying certain conditions, and they agree on `Γ × Γ`, then
    `S* = a·S + B` for constants `a > 0, B`.

    This strengthens Theorem 2.4 by using convexity. -/
theorem gamma_squared_determines_entropy
    (X₀ X₁ : Γ) (h : sprecS X₀ X₁) (S_star : Γ → ℝ)
    (hS₁ : ∀ X Y : Γ, precS X Y ↔ canonicalEntropy X₀ X₁ X ≤ canonicalEntropy X₀ X₁ Y)
    (hS₂ : ∀ X Y : Γ, precS X Y ↔ S_star X ≤ S_star Y)
    (h_agree : ∀ X Y X' Y' : Γ,
      prec (single X ++ single Y) (single X' ++ single Y') ↔
        canonicalEntropy X₀ X₁ X + canonicalEntropy X₀ X₁ Y ≤
        canonicalEntropy X₀ X₁ X' + canonicalEntropy X₀ X₁ Y')
    (h_agree' : ∀ X Y X' Y' : Γ,
      prec (single X ++ single Y) (single X' ++ single Y') ↔
        S_star X + S_star Y ≤ S_star X' + S_star Y') :
    ∃ a B : ℝ, a > 0 ∧ ∀ X : Γ, S_star X = a * canonicalEntropy X₀ X₁ X + B := by
  sorry

end LiebYngvason
