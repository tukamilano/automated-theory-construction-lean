import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

-- Temporary Lean code generated for verification is written here.

theorem paper_claim_support_closure_iff_support_ok
    (Γ : List Tp) (A : Tp) :
    SupportClosure Γ A ↔ support_ok Γ A := by
  simpa using thm_support_closure_matches_support_ok_000036 Γ A

theorem paper_claim_handed_support_closure_iff_derivable
    (Γ : List Tp) (A : Tp) :
    HandedSupportClosure Γ A ↔ (Γ ⇒ A) := by
  have hExact : HandedSupportClosure Γ A ↔ (Γ ⇒ A) := by
    simpa using thm_handed_support_closure_iff_sequent_000048 Γ A
  exact hExact

theorem paper_claim_support_closure_not_exact_for_derivability :
    ¬(∀ (Γ : List Tp) (A : Tp), SupportClosure Γ A ↔ (Γ ⇒ A)) := by
  simpa using thm_support_closure_exact_complete_000041_is_false

theorem paper_claim_handedness_is_exact_support_invariant :
    (∀ (Γ : List Tp) (A : Tp), HandedSupportClosure Γ A ↔ (Γ ⇒ A)) ∧
      ¬(∀ (Γ : List Tp) (A : Tp), SupportClosure Γ A ↔ (Γ ⇒ A)) := by
  constructor
  · intro Γ A
    simpa using paper_claim_handed_support_closure_iff_derivable Γ A
  · exact paper_claim_support_closure_not_exact_for_derivability

theorem paper_claim_residual_handed_normal_form
    (Γ : List Tp) (A : Tp) :
    HandedSupportClosure Γ A ↔
      ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ AtomicCandidateTree Δ s := by
  have hResidual :
      HandedSupportClosure Γ A ↔
        ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ AtomicCandidateTree Δ s := by
    simpa using (thm_residual_support_normal_form_000050 Γ A).1
  exact hResidual

theorem paper_claim_residual_support_occurs_normal_form
    (Γ : List Tp) (A : Tp) :
    SupportClosure Γ A ↔
      ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ ∃ B ∈ Δ, occurs_atom s B := by
  have hResidual :
      SupportClosure Γ A ↔
        ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ ∃ B ∈ Δ, occurs_atom s B := by
    simpa using (thm_residual_support_normal_form_000050 Γ A).2
  exact hResidual

theorem paper_claim_residual_support_boundary_normal_form
    (Γ : List Tp) (A : Tp) :
    (HandedSupportClosure Γ A ↔
      ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ AtomicCandidateTree Δ s) ∧
    (SupportClosure Γ A ↔
      ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ ∃ B ∈ Δ, occurs_atom s B) := by
  constructor
  · simpa using paper_claim_residual_handed_normal_form Γ A
  · simpa using paper_claim_residual_support_occurs_normal_form Γ A

def ResidualAtomicWitness (Γ : List Tp) (A : Tp) :=
  { p : List Tp × String //
      residualAtomicState Γ A = some p ∧ AtomicCandidateTree p.1 p.2 }

theorem residualAtomicWitness_reconstruct_bijective
    (Γ : List Tp) (A : Tp) :
    ∃ reconstruct : ResidualAtomicWitness Γ A → CandidateTree Γ A,
      Function.Bijective reconstruct := by
  simpa [ResidualAtomicWitness] using
    (thm_residual_candidate_tree_bijection_000055 Γ A)

theorem paper_claim_residual_atomic_witness_reconstructs_candidate_tree
    (Γ : List Tp) (A : Tp) :
    ∃ reconstruct : ResidualAtomicWitness Γ A → CandidateTree Γ A,
      Function.Bijective reconstruct := by
  have hReconstruct :
      ∃ reconstruct : ResidualAtomicWitness Γ A → CandidateTree Γ A,
        Function.Bijective reconstruct := by
    simpa using residualAtomicWitness_reconstruct_bijective Γ A
  exact hReconstruct

theorem paper_claim_one_sided_handed_boundary_persists :
    ((∀ (Γ : List Tp) (A : Tp),
        (∀ x ∈ Γ, isLeftOnly x) →
        isLeftOnly A →
        (HandedSupportClosure Γ A ↔ leftTranslatedHandedSupportClosure Γ A)) ∧
      (∀ (Γ : List Tp) (A : Tp),
        (∀ x ∈ Γ, isRightOnly x) →
        isRightOnly A →
        (HandedSupportClosure Γ A ↔ rightTranslatedHandedSupportClosure Γ A))) ∧
      ¬((∀ (Γ : List Tp) (A : Tp),
          (∀ x ∈ Γ, isLeftOnly x) →
          isLeftOnly A →
          (SupportClosure Γ A ↔ HandedSupportClosure Γ A)) ∧
        (∀ (Γ : List Tp) (A : Tp),
          (∀ x ∈ Γ, isRightOnly x) →
          isRightOnly A →
          (SupportClosure Γ A ↔ HandedSupportClosure Γ A))) := by
  have hOneSided :
      (∀ (Γ : List Tp) (A : Tp),
        (∀ x ∈ Γ, isLeftOnly x) →
        isLeftOnly A →
        (HandedSupportClosure Γ A ↔ leftTranslatedHandedSupportClosure Γ A)) ∧
      (∀ (Γ : List Tp) (A : Tp),
        (∀ x ∈ Γ, isRightOnly x) →
        isRightOnly A →
        (HandedSupportClosure Γ A ↔ rightTranslatedHandedSupportClosure Γ A)) := by
    simpa using thm_one_sided_handed_conservativity_000051
  have hGap :
      ¬((∀ (Γ : List Tp) (A : Tp),
          (∀ x ∈ Γ, isLeftOnly x) →
          isLeftOnly A →
          (SupportClosure Γ A ↔ HandedSupportClosure Γ A)) ∧
        (∀ (Γ : List Tp) (A : Tp),
          (∀ x ∈ Γ, isRightOnly x) →
          isRightOnly A →
          (SupportClosure Γ A ↔ HandedSupportClosure Γ A))) := by
    simpa using thm_same_handed_support_exactness_000059_is_false
  exact ⟨hOneSided, hGap⟩

end AutomatedTheoryConstruction
