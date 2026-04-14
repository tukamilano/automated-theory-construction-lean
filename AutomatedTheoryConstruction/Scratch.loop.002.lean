import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_leftrep_iff_left_sequent_000086 : ∀ (Γ : List Tp) (A : Tp), LeftRep Γ A ↔ ∃ ΓL : List Mathling.Lambek.ProductFree.Left.Tp, ∃ AL : Mathling.Lambek.ProductFree.Left.Tp, Γ = ΓL.map Mathling.Lambek.ProductFree.Left.Tp.toProductFree ∧ A = AL.toProductFree ∧ Mathling.Lambek.ProductFree.Left.Sequent ΓL AL := by
  intro Γ A
  constructor
  · intro h
    rcases h with ⟨ΓL, AL, hΓ, hA, hseq⟩
    refine ⟨ΓL, AL, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Left.ctxToProductFree] using hΓ.symm
    · simpa using hA.symm
  · intro h
    rcases h with ⟨ΓL, AL, hΓ, hA, hseq⟩
    refine ⟨ΓL, AL, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Left.ctxToProductFree] using hΓ.symm
    · simpa using hA.symm

end AutomatedTheoryConstruction
