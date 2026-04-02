import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_ket_injective_of_vacuum_ne_zero_000009_is_false : ¬(∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (m n : ℕ), m ≠ n → bc.ket m ≠ bc.ket n) := by
  intro h
  let V0 := ULift ↥(⊥ : Submodule ℂ ℂ)
  let bc : BosonCore V0 :=
    { a := 0
      aDagger := 0
      vacuum := 0
      ccr := Subsingleton.elim _ _
      vacuum_annihilate := by simp }
  have hneq : (0 : ℕ) ≠ 1 := by decide
  have hcontra := h (bc := bc) (m := 0) (n := 1) hneq
  apply hcontra
  exact Subsingleton.elim _ _

end AutomatedTheoryConstruction
