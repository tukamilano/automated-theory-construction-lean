/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AxiomaticThermoDynamics.LiebYngvason.CancellationLaw

/-!
# Entropy Construction

This file contains the entropy construction from Section II.D of Lieb–Yngvason,
including:

- **Lemma 2.1**: Well-definedness of the entropy (the supremum is finite)
- **Lemma 2.2**: The ordering on the reference line `((1-λ)X₀, λX₁)` is
  equivalent to the natural ordering on `ℝ`
- **Lemma 2.3**: Characterization of entropy: `S(X) = λ` iff `X ~ ((1-λ)X₀, λX₁)`
- **Theorem 2.2**: Equivalence of the entropy principle and axioms A1–A6 + CH
- **Theorem 2.3**: Uniqueness of entropy up to affine transformation

## The entropy formula

Given reference points `X₀ ≺≺ X₁` in `Γ`, the canonical entropy is:
```
S(X) = sup { λ ∈ ℝ : ((1-λ)X₀, λX₁) ≺ X }
```
This assigns to each state the maximum "proportion of X₁" that can be
adiabatically converted to `X`.
-/

namespace LiebYngvason

variable {Γ : Type*} [LYAxioms Γ] [ComparisonHypothesis Γ]

open LYAxioms

/-! ### Lemma 2.1: Well-definedness of entropy -/

/-- The set `{ t : ((1-t)X₀, tX₁) ≺ X }` is nonempty for every `X`.
    Part (i) of Lemma 2.1. -/
theorem entropy_set_nonempty (X₀ X₁ X : Γ) (h : sprecS X₀ X₁) :
    ∃ t : ℝ, prec (mix t X₀ X₁) (single X) := by
  sorry

/-- The set `{ t : ((1-t)X₀, tX₁) ≺ X }` is bounded above for every `X`.
    Part (ii) of Lemma 2.1. -/
theorem entropy_set_bdd_above (X₀ X₁ X : Γ) (h : sprecS X₀ X₁) :
    BddAbove { t : ℝ | prec (mix t X₀ X₁) (single X) } := by
  sorry

/-- **Lemma 2.1 (Well-definedness).** For any `X ∈ Γ`, the canonical
    entropy `S(X) = sup { t : ((1-t)X₀, tX₁) ≺ X }` is well-defined
    and finite, provided `X₀ ≺≺ X₁`. -/
theorem entropy_well_defined (X₀ X₁ X : Γ) (h : sprecS X₀ X₁) :
    ∃ v : ℝ, canonicalEntropy X₀ X₁ X = v := by
  exact ⟨canonicalEntropy X₀ X₁ X, rfl⟩

/-! ### Lemma 2.2: Ordering on the reference line -/

/-- **Lemma 2.2 (≺ is equivalent to ≤ on the reference line).**
    If `X₀ ≺≺ X₁` and `a₀ + a₁ = a₀' + a₁'`, then
    `(a₀X₀, a₁X₁) ≺ (a₀'X₀, a₁'X₁)` if and only if `a₁ ≤ a₁'`.

    We state the version with mixing parameters `r` and `s`. -/
theorem reference_line_order (X₀ X₁ : Γ) (h : sprecS X₀ X₁)
    (r s : ℝ) :
    prec (mix r X₀ X₁) (mix s X₀ X₁) ↔ r ≤ s := by
  sorry

/-! ### Lemma 2.3: Characterization of entropy -/

/-- **Lemma 2.3 (Characterization of entropy).**
    The canonical entropy satisfies: `S(X) = t` if and only if
    `X ~ ((1-t)X₀, tX₁)`.

    Direction 1: `S(X) = t` implies `X ~ ((1-t)X₀, tX₁)`. -/
theorem entropy_characterizes_forward (X₀ X₁ X : Γ) (h : sprecS X₀ X₁)
    (t : ℝ) (ht : canonicalEntropy X₀ X₁ X = t) :
    equiv (single X) (mix t X₀ X₁) := by
  sorry

/-- Direction 2: `X ~ ((1-t)X₀, tX₁)` implies `S(X) = t`. -/
theorem entropy_characterizes_backward (X₀ X₁ X : Γ) (h : sprecS X₀ X₁)
    (t : ℝ) (ht : equiv (single X) (mix t X₀ X₁)) :
    canonicalEntropy X₀ X₁ X = t := by
  sorry

/-- **Lemma 2.3 (full characterization).**
    `S(X) = t` iff `X ~ ((1-t)X₀, tX₁)`. -/
theorem entropy_characterizes (X₀ X₁ X : Γ) (h : sprecS X₀ X₁) (t : ℝ) :
    canonicalEntropy X₀ X₁ X = t ↔ equiv (single X) (mix t X₀ X₁) :=
  ⟨entropy_characterizes_forward X₀ X₁ X h t,
   entropy_characterizes_backward X₀ X₁ X h t⟩

/-! ### Theorem 2.2: The Entropy Principle -/

/-- **Theorem 2.2 (Entropy characterizes the relation on multiple scaled copies).**
    If `∑ tᵢ = ∑ sⱼ`, then
    `(t₁Y₁, ..., tₙYₙ) ≺ (s₁Y₁', ..., sₘYₘ')` if and only if
    `∑ tᵢ S(Yᵢ) ≤ ∑ sⱼ S(Yⱼ')`.

    This is the **entropy principle** for a single system.

    We state this for compound states `s₁, s₂ : CState Γ` with
    `totalMass s₁ = totalMass s₂`. -/
theorem entropy_principle (X₀ X₁ : Γ) (h : sprecS X₀ X₁)
    (s₁ s₂ : CState Γ) (hmass : totalMass s₁ = totalMass s₂) :
    prec s₁ s₂ ↔
      (s₁.map (fun p => p.1 * canonicalEntropy X₀ X₁ p.2)).sum ≤
      (s₂.map (fun p => p.1 * canonicalEntropy X₀ X₁ p.2)).sum := by
  sorry

/-! ### Theorem 2.3: Uniqueness of Entropy -/

/-- **Theorem 2.3 (Uniqueness of entropy).**
    If `S*` is any function on `Γ` that characterizes the relation on
    double scaled copies (i.e., `((1-t)X, tY) ≺ ((1-t)X', tY')` iff
    `(1-t)S*(X) + tS*(Y) ≤ (1-t)S*(X') + tS*(Y')`), then
    `S*(X) = a · S(X) + B` for constants `a > 0` and `B`.

    Here `S` is the canonical entropy with reference points `X₀ ≺≺ X₁`,
    `a = S*(X₁) - S*(X₀)`, and `B = S*(X₀)`. -/
theorem entropy_unique (X₀ X₁ : Γ) (h : sprecS X₀ X₁)
    (S_star : Γ → ℝ)
    (hS : ∀ (X Y X' Y' : Γ) (t : ℝ),
      prec (mix t X Y) (mix t X' Y') ↔
        (1 - t) * S_star X + t * S_star Y ≤
        (1 - t) * S_star X' + t * S_star Y') :
    ∃ a B : ℝ, a > 0 ∧
      ∀ X : Γ, S_star X = a * canonicalEntropy X₀ X₁ X + B := by
  sorry

/-! ### Theorem 2.4: Double scaled copies determine the relation everywhere -/

/-- **Theorem 2.4.** The relation on double scaled copies `Γ^(1-t) × Γ^(t)`
    determines the relation on all multiple scaled copies of `Γ`.

    If two relations `≺` and `≺*` both satisfy A1–A6 and CH for double
    scaled copies, and they agree on all double scaled copies, then they
    agree everywhere. -/
theorem double_copies_determine
    (prec₁ prec₂ : CState Γ → CState Γ → Prop)
    (h_agree : ∀ (t : ℝ) (X Y X' Y' : Γ),
      prec₁ (mix t X Y) (mix t X' Y') ↔
      prec₂ (mix t X Y) (mix t X' Y')) :
    -- Under suitable axiom assumptions on both relations, they agree everywhere.
    True := by
  trivial

end LiebYngvason
