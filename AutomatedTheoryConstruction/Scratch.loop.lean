import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_number_adagger_pow_ket_eigenvalue_000006 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (m n : ℕ), bc.number ((bc.aDagger ^ m) (bc.ket n)) = (↑(m + n) : ℂ) • (bc.aDagger ^ m) (bc.ket n) := by
  intro V _ _ bc m n
  have hEq : (bc.aDagger ^ m) (bc.ket n) = bc.ket (m + n) := by
    simp [BosonCore.ket, pow_add]
  have hEig : ∀ k : ℕ, bc.number (bc.ket k) = (↑k : ℂ) • bc.ket k := by
    intro k
    cases k with
    | zero =>
        simpa [BosonCore.ket] using bc.number_vacuum
    | succ k =>
        calc
          bc.number (bc.ket (k + 1)) = bc.aDagger (bc.a (bc.ket (k + 1))) := by rfl
          _ = bc.aDagger ((↑(k + 1) : ℂ) • bc.ket k) := by rw [bc.a_ket_succ]
          _ = (↑(k + 1) : ℂ) • bc.aDagger (bc.ket k) := by rw [map_smul]
          _ = (↑(k + 1) : ℂ) • bc.ket (k + 1) := by rw [bc.aDagger_ket]
  simpa [hEq] using hEig (m + n)

end AutomatedTheoryConstruction
