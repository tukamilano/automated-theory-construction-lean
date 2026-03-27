import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem main_thm_fock_span_linear_equiv_polynomial : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), bc.vacuum ≠ 0 → ∃ Φ : Polynomial ℂ ≃ₗ[ℂ] Submodule.span ℂ (Set.range bc.ket), ∀ p : Polynomial ℂ, (Φ p : V) = (Polynomial.aeval bc.aDagger p) bc.vacuum := by
  intro V _ _ bc hvac
  have hnum : ∀ n : ℕ, bc.number (bc.ket n) = (n : ℂ) • bc.ket n := by
    intro n
    cases n with
    | zero =>
        rw [bc.ket_zero, bc.number_vacuum]
        simp
    | succ n =>
        calc
          bc.number (bc.ket (n + 1)) = bc.aDagger (bc.a (bc.ket (n + 1))) := rfl
          _ = bc.aDagger ((↑(n + 1) : ℂ) • bc.ket n) := by rw [bc.a_ket_succ]
          _ = (↑(n + 1) : ℂ) • bc.aDagger (bc.ket n) := by rw [map_smul]
          _ = (↑(n + 1) : ℂ) • bc.ket (n + 1) := by rw [bc.aDagger_ket]
  have hket_ne : ∀ n : ℕ, bc.ket n ≠ 0 := by
    intro n
    induction n with
    | zero =>
        simpa [bc.ket_zero] using hvac
    | succ n ih =>
        intro hsucc
        have hdown : (↑(n + 1) : ℂ) • bc.ket n = 0 := by
          simpa [hsucc] using (bc.a_ket_succ n).symm
        have hscalar : (↑(n + 1) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        rcases smul_eq_zero.mp hdown with hzero | hzero
        · exact hscalar hzero
        · exact ih hzero
  have hμ : Function.Injective (fun n : ℕ => (n : ℂ)) := by
    intro m n hmn
    exact Nat.cast_injective (R := ℂ) hmn
  have h_eigenvec : ∀ n : ℕ, bc.number.HasEigenvector (n : ℂ) (bc.ket n) := by
    intro n
    refine ⟨?_, hket_ne n⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hnum n
  have hli : LinearIndependent ℂ (fun n : ℕ => bc.ket n) := by
    simpa using Module.End.eigenvectors_linearIndependent' bc.number (fun n : ℕ => (n : ℂ)) hμ (fun n : ℕ => bc.ket n) h_eigenvec
  refine ⟨(Polynomial.toFinsuppIsoLinear ℂ).trans hli.linearCombinationEquiv, ?_⟩
  intro p
  change (Finsupp.linearCombination ℂ (fun n : ℕ => bc.ket n) (Polynomial.toFinsupp p) : V) =
    (Polynomial.aeval bc.aDagger p) bc.vacuum
  rw [Finsupp.linearCombination_apply]
  simpa [Polynomial.sum_def, Polynomial.support_toFinsupp, Polynomial.toFinsupp_apply, BosonCore.ket] using
    (Polynomial.aeval_endomorphism bc.aDagger bc.vacuum p).symm

end AutomatedTheoryConstruction
