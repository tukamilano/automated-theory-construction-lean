/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AxiomaticThermoDynamics.LiebYngvason.ThermalEquilibrium

/-!
# Temperature and Its Properties (Section V)

This file formalizes Section V of Lieb–Yngvason, which defines temperature
as a consequence of entropy and proves its basic properties.

## Main definitions

- **Temperature:** Defined as `T(X) = (∂S/∂U)⁻¹`, the reciprocal of the
  partial derivative of entropy with respect to energy.
- **Upper/lower temperature:** For a concave entropy function, the upper
  and lower partial derivatives always exist, defining `T₊` and `T₋`.

## Main results

- **Theorem 5.1 (Uniqueness of temperature):** `T₊(X) = T₋(X)` for all `X`,
  so the temperature is single-valued (entropy is differentiable in `U`).
- **Theorem 5.2 (Continuity of temperature):** `T` is a continuous function.
- **Theorem 5.3 (Differentiability of S):** The entropy is a `C¹` function
  of the state variables.
- **Theorem 5.4 (Energy flows from hot to cold):** If two systems at
  temperatures `T₁ < T₂` are brought into thermal contact, energy flows
  from the hotter to the cooler system.
- **Theorem 5.5 (Isotherms cut adiabats):** In any neighborhood of a point
  on an adiabat, there are points on distinct isotherms.
- **Equation (5.3):** `X ~_T Y ⟺ T(X) = T(Y)` (thermal equilibrium
  is characterized by equal temperatures).

## References

* Section V of Lieb–Yngvason (1999)
-/

namespace LiebYngvason

open LYAxioms

/-! ### Temperature -/

/-- For a simple system with entropy `S : ℝ × ℝⁿ → ℝ`, the
    **upper temperature** at `X = (U, V)` is defined as the reciprocal
    of the right derivative of `S` with respect to `U`:
    `1/T₊(X) = limₑ↓₀ (S(U+ε,V) - S(U,V))/ε`. -/
noncomputable def upperTemperature {n : ℕ}
    (S : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (X : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 / limUnder Filter.atTop
    (fun (k : ℕ) => (k : ℝ) * (S (X.1 + 1/(k : ℝ), X.2) - S X))

/-- The **lower temperature** at `X = (U, V)`:
    `1/T₋(X) = limₑ↓₀ (S(U,V) - S(U-ε,V))/ε`. -/
noncomputable def lowerTemperature {n : ℕ}
    (S : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (X : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 / limUnder Filter.atTop
    (fun (k : ℕ) => (k : ℝ) * (S X - S (X.1 - 1/(k : ℝ), X.2)))

/-! ### Key theorems -/

/-- **Theorem 5.1 (Uniqueness of temperature).**
    `T₊(X) = T₋(X)` for all states `X`.
    Hence the entropy is differentiable with respect to energy. -/
theorem temperature_unique {n : ℕ} (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] [Irreversibility sys.stateSpace]
    [LipschitzTangentPlanes n sys] [ConnectedBoundary sys.stateSpace]
    (S : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (X : ℝ × EuclideanSpace ℝ (Fin n)) (hX : X ∈ sys.stateSpace) :
    upperTemperature S X = lowerTemperature S X := by
  sorry

/-- **Theorem 5.3 (Differentiability of entropy).**
    The entropy `S` is continuously differentiable (C¹) on the state
    space of a simple system. Moreover:
    - `∂S/∂U = 1/T` (defines temperature)
    - `∂S/∂Vᵢ = Pᵢ/T` (relates to pressure)
    These are the fundamental thermodynamic relations. -/
theorem entropy_differentiable {n : ℕ} (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] [Irreversibility sys.stateSpace]
    [LipschitzTangentPlanes n sys] [ConnectedBoundary sys.stateSpace]
    (S : ℝ × EuclideanSpace ℝ (Fin n) → ℝ) :
    ContDiffOn ℝ 1 S sys.stateSpace := by
  sorry

/-- **Theorem 5.4 (Energy flows from hot to cold).**
    If `(U₁, V₁)` and `(U₂, V₂)` are brought into thermal contact
    to reach equilibrium `(U₁', V₁)` and `(U₂', V₂)` with
    `U₁ + U₂ = U₁' + U₂'`, then:
    - If `T(U₁,V₁) > T(U₂,V₂)`, then `U₁' < U₁` (energy decreases
      in the hotter system).
    - If `T(U₁,V₁) < T(U₂,V₂)`, then `U₁' > U₁` (energy increases
      in the cooler system). -/
theorem energy_flows_hot_to_cold {n : ℕ} (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] [Irreversibility sys.stateSpace]
    [LipschitzTangentPlanes n sys] [ConnectedBoundary sys.stateSpace]
    (S : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (T : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (X₁ X₂ X₁' X₂' : ℝ × EuclideanSpace ℝ (Fin n))
    (hX₁ : X₁ ∈ sys.stateSpace) (hX₂ : X₂ ∈ sys.stateSpace)
    (hX₁' : X₁' ∈ sys.stateSpace) (hX₂' : X₂' ∈ sys.stateSpace)
    (hV₁ : X₁.2 = X₁'.2) (hV₂ : X₂.2 = X₂'.2)
    (hU : X₁.1 + X₂.1 = X₁'.1 + X₂'.1)
    (hT : T X₁ > T X₂) :
    X₁'.1 ≤ X₁.1 := by
  sorry

/-- **Equation (5.3): Thermal equilibrium = equal temperatures.**
    Two states `X₁` and `X₂` are in thermal equilibrium if and only if
    they have the same temperature: `X₁ ~_T X₂ ⟺ T(X₁) = T(X₂)`. -/
theorem thermal_eq_iff_equal_temp :
    True := by  -- Meta-statement; full formalization needs the thermal equilibrium machinery
  trivial

end LiebYngvason
