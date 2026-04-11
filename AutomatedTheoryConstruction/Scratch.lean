import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem main_thm_support_closure_residual_obstruction : ∀ (Γ : List Tp) (A : Tp), SupportClosure Γ A ↔ ((Γ ⇒ A) ∨ ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ (∃ B ∈ Δ, occurs_atom s B) ∧ ¬ AtomicResidualGraphAccepts (Δ, s)) := by
  intro Γ A
  constructor
  · intro hsup
    rcases ((thm_residual_support_normal_form_000050 Γ A).2).mp hsup with ⟨Δ, s, hres, hocc⟩
    by_cases hacc : AtomicResidualGraphAccepts (Δ, s)
    · left
      exact (thm_residual_graph_recognizes_sequent_000062 Γ A).2 ⟨Δ, s, hres, hacc⟩
    · right
      exact ⟨Δ, s, hres, hocc, hacc⟩
  · intro h
    rcases h with hseq | ⟨Δ, s, hres, hocc, _hacc⟩
    · rw [thm_support_closure_matches_support_ok_000036]
      exact thm_derivable_support_ok_000032 hseq
    · exact ((thm_residual_support_normal_form_000050 Γ A).2).mpr ⟨Δ, s, hres, hocc⟩

end AutomatedTheoryConstruction
