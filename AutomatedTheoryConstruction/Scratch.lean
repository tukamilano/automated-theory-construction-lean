import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_number_ket_eigenvalue_000001 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number (bc.ket n) = (n : ℂ) • bc.ket n := by
  intro V _ _ bc n
  cases n with
  | zero =>
      rw [bc.ket_zero, bc.number_vacuum]
      simp
  | succ n =>
      calc
        bc.number (bc.ket (n + 1))
            = bc.aDagger (bc.a (bc.ket (n + 1))) := rfl
        _ = bc.aDagger ((↑(n + 1) : ℂ) • bc.ket n) := by
          rw [bc.a_ket_succ]
        _ = (↑(n + 1) : ℂ) • bc.aDagger (bc.ket n) := by
          rw [map_smul]
        _ = (↑(n + 1) : ℂ) • bc.ket (n + 1) := by
          rw [bc.aDagger_ket]

end AutomatedTheoryConstruction
