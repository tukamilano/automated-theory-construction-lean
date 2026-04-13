import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_singleton_sequent_classification_000017 : ∀ {A B : Tp}, ([A] ⇒ B) ↔ A = B ∨ (∃ C : Tp, ∃ D : Tp, B = D ⧸ C ∧ ([A] ++ [C] ⇒ D)) ∨ (∃ C : Tp, ∃ D : Tp, B = C ⧹ D ∧ ([C] ++ [A] ⇒ D)) := by
  intro A B
  constructor
  · intro h
    cases B with
    | atom s =>
        exact Or.inl (thm_singleton_atom_iff_eq_000008.mp h)
    | rdiv D C =>
        exact Or.inr <| Or.inl ⟨C, D, rfl, rdiv_invertible h⟩
    | ldiv C D =>
        exact Or.inr <| Or.inr ⟨C, D, rfl, ldiv_invertible h⟩
  · intro h
    rcases h with hEq | ⟨C, D, rfl, hDC⟩ | ⟨C, D, rfl, hCD⟩
    · cases hEq
      exact Sequent.ax
    · exact Sequent.rdiv_r (Γ := [A]) (A := C) (B := D) (by simp) hDC
    · exact Sequent.ldiv_r (Γ := [A]) (A := C) (B := D) (by simp) hCD

end AutomatedTheoryConstruction
