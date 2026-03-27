import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_annihilated_polynomial_state_is_constant_000122 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (p : Polynomial ℂ), bc.vacuum ≠ 0 → bc.a ((Polynomial.aeval bc.aDagger p) bc.vacuum) = 0 → ∃ c : ℂ, p = Polynomial.C c := by
  intro V _ _ bc p hvac ha
  have hderiv :
      ∀ q : Polynomial ℂ,
        bc.a ((Polynomial.aeval bc.aDagger q) bc.vacuum) =
          (Polynomial.aeval bc.aDagger (Polynomial.derivative q)) bc.vacuum := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr =>
        simp [Polynomial.derivative_add, hq, hr]
    | monomial n c =>
        cases n with
        | zero =>
            simp [AutomatedTheoryConstruction.thm_aeval_a_dagger_vacuum_support_sum_000060,
              bc.vacuum_annihilate]
        | succ n =>
            rw [AutomatedTheoryConstruction.thm_aeval_a_dagger_vacuum_support_sum_000060,
              Polynomial.derivative_monomial_succ,
              AutomatedTheoryConstruction.thm_aeval_a_dagger_vacuum_support_sum_000060]
            simp [bc.a_ket_succ, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have hz : (Polynomial.aeval bc.aDagger (Polynomial.derivative p)) bc.vacuum = 0 := by
    simpa [hderiv p] using ha
  have hdp : Polynomial.derivative p = 0 := by
    apply
      (AutomatedTheoryConstruction.thm_aeval_vacuum_injective_of_vacuum_ne_zero_000017
        (bc := bc) hvac)
    simpa using hz
  exact ⟨p.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hdp⟩

end AutomatedTheoryConstruction
