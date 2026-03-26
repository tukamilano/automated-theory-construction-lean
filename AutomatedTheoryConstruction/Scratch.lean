import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_eigenvalue_from_annihilation_length_000034 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) {v : V} {μ : ℂ} (n : ℕ), bc.number v = μ • v → (bc.a ^ (n + 1)) v = 0 → (bc.a ^ n) v ≠ 0 → μ = (n : ℂ) := by
  intro V _ _ bc v μ n hμ hnil hnon
  have ha : bc.a ((bc.a ^ n) v) = 0 := by
    simpa [pow_succ'] using hnil
  have hnum_zero : bc.number ((bc.a ^ n) v) = 0 := by
    unfold BosonCore.number
    change bc.aDagger (bc.a ((bc.a ^ n) v)) = 0
    rw [ha, map_zero]
  have hdown :
      bc.number ((bc.a ^ n) v) = (μ - (n : ℂ)) • ((bc.a ^ n) v) := by
    simpa using thm_a_pow_shifts_eigenvalue_down_000008 (bc := bc) (v := v) (μ := μ) n hμ
  have hsmul : (μ - (n : ℂ)) • ((bc.a ^ n) v) = 0 := by
    rw [← hdown]
    exact hnum_zero
  have hsub : μ - (n : ℂ) = 0 := by
    exact (smul_eq_zero.mp hsmul).resolve_right hnon
  exact sub_eq_zero.mp hsub

end AutomatedTheoryConstruction
