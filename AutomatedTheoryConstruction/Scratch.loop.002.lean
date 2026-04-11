import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_same_atom_finite_iff_bounded_000084 : ∀ (src : List Tp) (s : String) (S : Set AtomicResidualState), S ⊆ { p : AtomicResidualState | p.2 = s ∧ (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) } → (S.Finite ↔ ∃ N : Nat, ∀ p ∈ S, list_degree p.1 ≤ N) := by
  intro src s S hSub
  constructor
  · intro hfin
    have hfinImg :
        Set.Finite ((fun p : AtomicResidualState => list_degree p.1) '' S) :=
      Set.Finite.image (fun p : AtomicResidualState => list_degree p.1) hfin
    rcases (Set.finite_iff_bddAbove.mp hfinImg) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro p hp
    exact hN ⟨p, hp, rfl⟩
  · rintro ⟨N, hN⟩
    refine (thm_degree_bounded_subformula_slice_finite_000072 src s N).subset ?_
    intro p hp
    have hp' := hSub hp
    exact ⟨hp'.1, hN p hp, hp'.2⟩

end AutomatedTheoryConstruction
