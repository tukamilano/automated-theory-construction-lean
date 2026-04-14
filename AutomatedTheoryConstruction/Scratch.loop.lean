import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_rightrep_atom_reduction_000078 : ∀ (Γ : List Tp) (s : String), RightRep Γ (# s) ↔ (Γ = [# s] ∨ ∃ (pi delta lam : List Tp) (A B : Tp), Γ = pi ++ [B ⧸ A] ++ delta ++ lam ∧ RightRep delta A ∧ RightRep (pi ++ [B] ++ lam) (# s)) := by
  intro Γ s
  constructor
  · intro hRight
    have hExact := (thm_right_oriented_derivation_exact_000059 Γ (# s)).mp hRight
    rcases thm_atom_sequent_decompose_000009 (Γ := Γ) (s := s) hExact.2 with hAx | hCases
    · exact Or.inl hAx
    · rcases hCases with ⟨pi, B, A, delta, lam, hΓ, hDeltaSeq, hMainSeq⟩ | ⟨pi, delta, A, B, lam, hΓ, hDeltaSeq, hMainSeq⟩
      · have hBA : RightDivisionOnly B ∧ RightDivisionOnly A := by
          have hDiv : RightDivisionOnly (B ⧸ A) := by
            exact hExact.1 _ (by simp [hΓ])
          simpa [RightDivisionOnly] using hDiv
        have hDeltaRight : ∀ x ∈ A :: delta, RightDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxDelta
          · exact hBA.2
          · exact hExact.1 x (by simp [hΓ, hxDelta])
        have hMainRight : ∀ x ∈ (# s) :: (pi ++ [B] ++ lam), RightDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxMain
          · exact hExact.1 _ (by simp)
          · have hxMain' : x ∈ pi ∨ x = B ∨ x ∈ lam := by
              simpa [List.mem_append, List.mem_singleton, or_assoc] using hxMain
            rcases hxMain' with hxPi | rfl | hxLam
            · exact hExact.1 x (by simp [hΓ, hxPi])
            · exact hBA.1
            · exact hExact.1 x (by simp [hΓ, hxLam])
        refine Or.inr ⟨pi, delta, lam, A, B, hΓ, ?_, ?_⟩
        · exact (thm_uniform_orientation_implies_oriented_derivation_000055 delta A).2 ⟨hDeltaRight, hDeltaSeq⟩
        · exact (thm_uniform_orientation_implies_oriented_derivation_000055 (pi ++ [B] ++ lam) (# s)).2 ⟨hMainRight, hMainSeq⟩
      · have hBad : RightDivisionOnly (A ⧹ B) := by
          exact hExact.1 _ (by simp [hΓ])
        simp [RightDivisionOnly] at hBad
  · rintro (rfl | ⟨pi, delta, lam, A, B, hΓ, hDeltaRight, hMainRight⟩)
    · refine (thm_uniform_orientation_implies_oriented_derivation_000055 [# s] (# s)).2 ?_
      constructor
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [RightDivisionOnly]
        · rcases List.mem_singleton.mp hx with rfl
          simp [RightDivisionOnly]
      · exact Mathling.Lambek.ProductFree.Sequent.ax
    · subst hΓ
      have hDeltaExact := (thm_right_oriented_derivation_exact_000059 delta A).mp hDeltaRight
      have hMainExact := (thm_right_oriented_derivation_exact_000059 (pi ++ [B] ++ lam) (# s)).mp hMainRight
      refine (thm_uniform_orientation_implies_oriented_derivation_000055 (pi ++ [B ⧸ A] ++ delta ++ lam) (# s)).2 ?_
      constructor
      · intro x hx
        have hx' : x = # s ∨ x ∈ pi ∨ x = B ⧸ A ∨ x ∈ delta ∨ x ∈ lam := by
          simpa [List.mem_cons, List.mem_append, List.mem_singleton, or_assoc, or_left_comm, or_comm] using hx
        rcases hx' with rfl | hxPi | rfl | hxDelta | hxLam
        · simp [RightDivisionOnly]
        · exact hMainExact.1 x (by simp [hxPi])
        · exact ⟨hMainExact.1 B (by simp), hDeltaExact.1 A (by simp)⟩
        · exact hDeltaExact.1 x (by simp [hxDelta])
        · exact hMainExact.1 x (by simp [hxLam])
      · simpa [List.append_assoc] using
          (Mathling.Lambek.ProductFree.Sequent.rdiv_l
            (Δ := delta) (A := A) (Γ := pi) (B := B) (Λ := lam) (C := # s)
            hDeltaExact.2 hMainExact.2)

end AutomatedTheoryConstruction
