import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_aeval_vacuum_kernel_mul_derivative_stable_000102 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), let Phi : Polynomial ℂ →ₗ[ℂ] V := (LinearMap.applyₗ (R := ℂ) bc.vacuum).comp (Polynomial.aeval bc.aDagger).toLinearMap; (∀ p q : Polynomial ℂ, Phi p = 0 → Phi (q * p) = 0) ∧ (∀ p : Polynomial ℂ, Phi p = 0 → Phi (Polynomial.derivative p) = 0) := by
  intro V _ _ bc
  let Phi : Polynomial ℂ →ₗ[ℂ] V :=
    (LinearMap.applyₗ (R := ℂ) bc.vacuum).comp (Polynomial.aeval bc.aDagger).toLinearMap
  change
    (∀ p q : Polynomial ℂ, Phi p = 0 → Phi (q * p) = 0) ∧
      (∀ p : Polynomial ℂ, Phi p = 0 → Phi (Polynomial.derivative p) = 0)
  constructor
  · intro p q hp
    change (Polynomial.aeval bc.aDagger p) bc.vacuum = 0 at hp
    change (Polynomial.aeval bc.aDagger (q * p)) bc.vacuum = 0
    rw [Polynomial.aeval_mul]
    simp [hp]
  · intro p hp
    change (Polynomial.aeval bc.aDagger p) bc.vacuum = 0 at hp
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
    change (Polynomial.aeval bc.aDagger (Polynomial.derivative p)) bc.vacuum = 0
    simpa [hderiv p] using congrArg bc.a hp

end AutomatedTheoryConstruction
