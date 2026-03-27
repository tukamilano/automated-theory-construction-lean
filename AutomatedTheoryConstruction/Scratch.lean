import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_number_ket_eigenvalue_000001 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number (bc.ket n) = (n : ℂ) • bc.ket n := by
  intro V _ _ bc n
  cases n with
  | zero =>
      simpa [BosonCore.ket_zero] using bc.number_vacuum
  | succ n =>
      rw [BosonCore.number, Module.End.mul_apply, bc.a_ket_succ, map_smul, bc.aDagger_ket]

end AutomatedTheoryConstruction
