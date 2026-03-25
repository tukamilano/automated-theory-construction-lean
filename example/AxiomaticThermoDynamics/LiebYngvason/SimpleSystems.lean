/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AxiomaticThermoDynamics.LiebYngvason.Concavity

/-!
# Simple Systems (Section III)

This file formalizes Section III of Lieb–Yngvason, concerning **simple systems**.

A simple system is a thermodynamic system whose state space is a convex subset of
`ℝⁿ⁺¹`, parametrized by one energy coordinate `U` and `n` work coordinates
`V = (V₁, ..., Vₙ)` (e.g., volume, magnetization).

## Additional Axioms for Simple Systems

- **S1 (Irreversibility):** For each `X ∈ Γ`, there exists `Y` with `X ≺≺ Y`.
- **S2 (Lipschitz tangent planes):** Each forward sector `Aₓ` has a unique tangent
  plane at `X`, with Lipschitz continuous slope (the "pressure" function).
- **S3 (Connectedness of boundary):** `∂Aₓ` is pathwise connected.

## Main Results

- **Theorem 3.1:** Forward sectors are closed.
- **Theorem 3.2:** Forward sectors have nonempty interiors.
- **Theorem 3.3:** Forward sectors "point the same way" (the energy direction).
- **Theorem 3.4 (Planck's principle):** `X ≺ Y` iff `Y ∈ Aₓ`, which for simple
  systems means `U_Y ≥ U_X` when `V_Y = V_X` (energy can only increase at
  constant work coordinates).
- **Theorem 3.5:** Characterization of adiabatic surfaces as solutions of an ODE.
- **Theorem 3.6:** Adiabatic equivalence classes form smooth hypersurfaces.
- **Theorem 3.7:** The comparison hypothesis holds for simple systems.

## References

* Section III of Lieb–Yngvason (1999)
-/

namespace LiebYngvason

open LYAxioms

/-! ### State space of a simple system -/

/-- A **simple system** is a thermodynamic system whose state space is
    an open convex subset of `ℝⁿ⁺¹`, with coordinates `(U, V₁, ..., Vₙ)`.
    We model this as `ℝ × EuclideanSpace ℝ (Fin n)`, representing
    energy `U` and work coordinates `V`. -/
structure SimpleSystem (n : ℕ) where
  /-- The state space, an open convex subset of `ℝ × ℝⁿ`. -/
  stateSpace : Set (ℝ × EuclideanSpace ℝ (Fin n))
  /-- The state space is open. -/
  isOpen : IsOpen stateSpace
  /-- The state space is convex. -/
  isConvex : Convex ℝ stateSpace
  /-- The state space is nonempty. -/
  nonempty : stateSpace.Nonempty

/-- Extract the energy coordinate from a state. -/
def SimpleSystem.energy {n : ℕ} (_ : SimpleSystem n)
    (X : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ := X.1

/-- Extract the work coordinates from a state. -/
def SimpleSystem.workCoords {n : ℕ} (_ : SimpleSystem n)
    (X : ℝ × EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := X.2

/-! ### Additional axioms for simple systems -/

/-- **Axiom S1: Irreversibility.** For each state `X`, there exists a state `Y`
    with `X ≺≺ Y` (strict adiabatic accessibility). -/
class Irreversibility (Γ : Type*) [LYAxioms Γ] where
  exists_irreversible : ∀ X : Γ, ∃ Y : Γ, sprecS X Y

/-- **Axiom S2: Lipschitz tangent planes.** Each forward sector has a unique
    support plane at its reference point, with Lipschitz continuous slope.

    The slope defines the **pressure function** `P : Γ → ℝⁿ`. -/
class LipschitzTangentPlanes (n : ℕ) (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] where
  /-- The pressure function: assigns to each state `X` the slope of the
      tangent plane to `Aₓ` at `X`. -/
  pressure : sys.stateSpace → EuclideanSpace ℝ (Fin n)
  /-- The pressure is locally Lipschitz continuous. -/
  lipschitz : LocallyLipschitz pressure

/-- **Axiom S3: Connectedness of the boundary.** The boundary `∂Aₓ`
    (the adiabat through `X`) is pathwise connected. -/
class ConnectedBoundary (Γ : Type*) [LYAxioms Γ] [TopologicalSpace Γ] where
  boundary_connected : ∀ X : Γ,
    IsPathConnected (frontier (forwardSector X))

/-! ### Key theorems for simple systems -/

/-- **Theorem 3.1 (Forward sectors are closed).**
    The forward sector `Aₓ` is a closed subset of `Γ` (relative to `Γ`). -/
theorem forward_sector_closed {n : ℕ} (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] (X : sys.stateSpace) :
    IsClosed (forwardSector X) := by
  sorry

/-- **Theorem 3.2 (Forward sectors have nonempty interiors).**
    For all `X`, the forward sector `Aₓ` has a nonempty interior. -/
theorem forward_sector_nonempty_interior {n : ℕ} (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] [Irreversibility sys.stateSpace]
    [LipschitzTangentPlanes n sys] (X : sys.stateSpace) :
    (interior (forwardSector X)).Nonempty := by
  sorry

/-- **Theorem 3.4 (Planck's principle).**
    For a simple system, the relation `≺` implies that energy can only
    increase at fixed work coordinates. That is, if `X = (U, V)` and
    `Y = (U', V)` (same work coordinates), then `X ≺ Y` iff `U ≤ U'`. -/
theorem planck_principle {n : ℕ} (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] [Irreversibility sys.stateSpace]
    [LipschitzTangentPlanes n sys] [ConnectedBoundary sys.stateSpace]
    (X Y : sys.stateSpace)
    (hV : sys.workCoords X = sys.workCoords Y) :
    precS X Y ↔ sys.energy X ≤ sys.energy Y := by
  sorry

/-- **Theorem 3.7 (Comparison hypothesis for simple systems).**
    The comparison hypothesis holds for every simple system.
    This is one of the main achievements of Section III. -/
theorem comparison_for_simple_systems {n : ℕ} (sys : SimpleSystem n)
    [LYAxioms sys.stateSpace] [Irreversibility sys.stateSpace]
    [LipschitzTangentPlanes n sys] [ConnectedBoundary sys.stateSpace] :
    ∀ X Y : sys.stateSpace, comparable (single X) (single Y) := by
  sorry

end LiebYngvason
