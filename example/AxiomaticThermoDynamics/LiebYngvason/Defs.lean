/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The Physics and Mathematics of the Second Law of Thermodynamics

Formalization of the paper by Elliott H. Lieb and Jakob Yngvason,
*Physics Reports* **310** (1999), 1–96.

This module formalizes the core mathematical framework from Section II of the paper,
including:
- The axiomatic framework for adiabatic accessibility (Axioms A1–A6)
- The Comparison Hypothesis (CH)
- The notion of compound states and scaled copies
- Key definitions: adiabatic equivalence, forward sectors, entropy

## Modeling choices

We model **compound states** (states in product spaces of scaled copies of a system)
as `List (ℝ × Γ)`, where each entry `(t, X)` represents the scaled state `tX` in
the scaled copy `Γ^(t)`. The adiabatic accessibility relation is defined on such
compound states.

## References

* [Lieb, Yngvason, *The physics and mathematics of the second law of thermodynamics*]
  [Physics Reports 310 (1999), 1–96]
-/

namespace LiebYngvason

/-! ### Compound States -/

/-- A compound state is a finite list of weighted states.
    Each entry `(t, X)` represents a state `X` in the scaled copy `Γ^(t)`.
    The compound state `[(t₁, X₁), (t₂, X₂), ..., (tₙ, Xₙ)]`
    represents `(t₁X₁, t₂X₂, ..., tₙXₙ)` in the product
    `Γ^(t₁) × Γ^(t₂) × ... × Γ^(tₙ)`. -/
abbrev CState (Γ : Type*) := List (ℝ × Γ)

/-- Total mass (total scaling parameter) of a compound state: `∑ tᵢ`. -/
def totalMass {Γ : Type*} (s : CState Γ) : ℝ :=
  (s.map Prod.fst).sum

/-- Scaling a compound state by a positive real `t`:
    `[(t₁, X₁), ...] ↦ [(t·t₁, X₁), ...]`. -/
def scaleCState {Γ : Type*} (t : ℝ) (s : CState Γ) : CState Γ :=
  s.map (fun p => (t * p.1, p.2))

/-- A single state `X ∈ Γ` viewed as a compound state `[(1, X)]`. -/
def single {Γ : Type*} (X : Γ) : CState Γ := [(1, X)]

/-- The mixed reference state `((1-t)X₀, tX₁)`:
    a state in `Γ^(1-t) × Γ^(t)`.
    Here `t` plays the role of the entropy parameter `λ` in the paper. -/
def mix {Γ : Type*} (t : ℝ) (X₀ X₁ : Γ) : CState Γ :=
  [((1 - t), X₀), (t, X₁)]

/-! ### The Lieb–Yngvason Axiom System -/

/-- The Lieb–Yngvason axiom system for adiabatic accessibility.

This captures Axioms A1–A6 from Section II.C of the paper.
The relation `prec` represents adiabatic accessibility (`≺`) between
compound states. The relation is meaningful when the two compound states
have equal total mass. -/
class LYAxioms (Γ : Type*) where
  /-- Adiabatic accessibility relation on compound states.
      `prec s₁ s₂` means `s₁ ≺ s₂`, i.e., state `s₂` is adiabatically
      accessible from state `s₁`. -/
  prec : CState Γ → CState Γ → Prop
  /-- **A1: Reflexivity.** Every state is adiabatically accessible from itself. -/
  refl : ∀ (s : CState Γ), prec s s
  /-- **A2: Transitivity.** If `s₁ ≺ s₂` and `s₂ ≺ s₃`, then `s₁ ≺ s₃`. -/
  trans : ∀ {s₁ s₂ s₃ : CState Γ}, prec s₁ s₂ → prec s₂ s₃ → prec s₁ s₃
  /-- **Permutation invariance (left).** The ordering of components
      in a compound state does not matter. -/
  perm_left : ∀ {s₁ s₁' s₂ : CState Γ}, s₁.Perm s₁' → prec s₁ s₂ → prec s₁' s₂
  /-- **Permutation invariance (right).** -/
  perm_right : ∀ {s₁ s₂ s₂' : CState Γ}, s₂.Perm s₂' → prec s₁ s₂ → prec s₁ s₂'
  /-- **A3: Consistency.** Independent adiabatic processes can be combined:
      if `s₁ ≺ s₁'` and `s₂ ≺ s₂'`, then `(s₁, s₂) ≺ (s₁', s₂')`. -/
  consist : ∀ {s₁ s₁' s₂ s₂' : CState Γ},
    prec s₁ s₁' → prec s₂ s₂' → prec (s₁ ++ s₂) (s₁' ++ s₂')
  /-- **A4: Scaling invariance.** If `s₁ ≺ s₂`, then `t·s₁ ≺ t·s₂`
      for any `t > 0`. -/
  scale_inv : ∀ {s₁ s₂ : CState Γ} (t : ℝ), t > 0 →
    prec s₁ s₂ → prec (scaleCState t s₁) (scaleCState t s₂)
  /-- **A5 (Splitting).** A state can be split into scaled copies:
      `X ≺ (tX, (1-t)X)` for `0 < t < 1`. -/
  split : ∀ (X : Γ) (t : ℝ), 0 < t → t < 1 →
    prec (single X) [(t, X), (1 - t, X)]
  /-- **A5 (Recombination).** Scaled copies can be recombined:
      `(tX, (1-t)X) ≺ X` for `0 < t < 1`. -/
  recombine : ∀ (X : Γ) (t : ℝ), 0 < t → t < 1 →
    prec [(t, X), (1 - t, X)] (single X)
  /-- A zero-mass spectator can be adjoined without changing accessibility. -/
  zero_append : ∀ (s : CState Γ) (Z : Γ), prec s (s ++ [(0, Z)])
  /-- A zero-mass spectator can be removed without changing accessibility. -/
  zero_drop : ∀ (s : CState Γ) (Z : Γ), prec (s ++ [(0, Z)]) s
  /-- **A6: Stability.** An infinitesimal perturbation cannot enlarge
      the set of accessible states:
      if `(s₁, εZ₀) ≺ (s₂, εZ₁)` for all `ε > 0`, then `s₁ ≺ s₂`. -/
  stability : ∀ (s₁ s₂ : CState Γ) (Z₀ Z₁ : Γ),
    (∀ ε : ℝ, ε > 0 → prec (s₁ ++ [(ε, Z₀)]) (s₂ ++ [(ε, Z₁)])) →
    prec s₁ s₂

namespace LYAxioms

variable {Γ : Type*} [LYAxioms Γ]

/-! ### Derived Notions -/

/-- Strict adiabatic accessibility: `X ≺≺ Y` means `X ≺ Y` but not `Y ≺ X`.
    Equation (2.1) in the paper. -/
def sprec (s₁ s₂ : CState Γ) : Prop :=
  prec s₁ s₂ ∧ ¬ prec s₂ s₁

/-- Adiabatic equivalence: `X ~ Y` means `X ≺ Y` and `Y ≺ X`.
    Equation (2.2) in the paper. -/
def equiv (s₁ s₂ : CState Γ) : Prop :=
  prec s₁ s₂ ∧ prec s₂ s₁

/-- Two states are comparable if at least one is accessible from the other. -/
def comparable (s₁ s₂ : CState Γ) : Prop :=
  prec s₁ s₂ ∨ prec s₂ s₁

/-- Convenience: adiabatic accessibility between single states. -/
def precS (X Y : Γ) : Prop := prec (single X) (single Y)

/-- Convenience: strict adiabatic accessibility between single states. -/
def sprecS (X Y : Γ) : Prop := sprec (single X) (single Y)

/-- Convenience: adiabatic equivalence between single states. -/
def equivS (X Y : Γ) : Prop := equiv (single X) (single Y)

/-- The forward sector of `X` in `Γ`: the set of states adiabatically
    accessible from `X`. -/
def forwardSector (X : Γ) : Set Γ :=
  { Y : Γ | precS X Y }

/-- States lying between the reference points `X₀` and `X₁`. -/
def InReferenceStrip (X₀ X₁ X : Γ) : Prop :=
  precS X₀ X ∧ precS X X₁

end LYAxioms

/-! ### Comparison Hypothesis -/

/-- The **Comparison Hypothesis (CH)**: any two compound states with equal
    total mass are comparable. This is a key assumption for the entropy
    construction.

    In the paper, CH is initially assumed for specific state spaces and
    later derived from additional axioms about simple systems and
    thermal equilibrium (Sections III–IV). -/
class ComparisonHypothesis (Γ : Type*) [LYAxioms Γ] where
  /-- Any two compound states with equal total mass are comparable. -/
  compare : ∀ (s₁ s₂ : CState Γ),
    totalMass s₁ = totalMass s₂ → LYAxioms.prec s₁ s₂ ∨ LYAxioms.prec s₂ s₁

/-! ### The Entropy Function -/

/-- The **canonical entropy function** on `Γ` with reference points `X₀ ≺≺ X₁`.

    Definition (2.14) in the paper:
    `S(X) = sup { t ∈ [0,1] : ((1-t)X₀, tX₁) ≺ X }`

    This function assigns to each state `X` the supremum of the set of
    mixing parameters `t` such that the mixed reference state `((1-t)X₀, tX₁)`
    is adiabatically accessible to `X`, restricted to the physically
    meaningful interval `0 ≤ t ≤ 1`. -/
noncomputable def canonicalEntropy [LYAxioms Γ] (X₀ X₁ : Γ) (X : Γ) : ℝ :=
  sSup { t : ℝ | 0 ≤ t ∧ t ≤ 1 ∧ LYAxioms.prec (mix t X₀ X₁) (single X) }

/-! ### Convex State Spaces (Axiom A7) -/

/-- **Axiom A7: Convex Combination.** For convex state spaces embedded in a
    vector space, the convex combination of scaled copies is adiabatically
    accessible.

    If `Γ ⊆ V` is a convex subset of a real vector space, then
    `(tX, (1-t)Y) ≺ tX + (1-t)Y` for `X, Y ∈ Γ` and `t ∈ [0,1]`.
    Equation (2.22) in the paper.

    Here we state this for `Γ` itself being a vector space-like type. -/
class ConvexCombination (Γ : Type*) [AddCommGroup Γ] [Module ℝ Γ]
    [LYAxioms Γ] where
  /-- The convex combination axiom: `(tX, (1-t)Y) ≺ tX + (1-t)Y`. -/
  convex_combine : ∀ (X Y : Γ) (t : ℝ), 0 ≤ t → t ≤ 1 →
    LYAxioms.prec [(t, X), (1 - t, Y)]
      (single (t • X + (1 - t) • Y))

end LiebYngvason
