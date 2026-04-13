import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_atomic_focused_tree_exists_000016 : ∀ {Γ : List Tp} {s : String}, Γ ⇒ Tp.atom s → ∃ n : Nat, proveAux n Γ (Tp.atom s) = true := by
  intro Γ s h
  refine ⟨list_degree Γ + tp_degree (Tp.atom s) + 1, ?_⟩
  have h' : prove2 Γ (Tp.atom s) :=
    (prove2_iff_sequent (Γ := Γ) (A := Tp.atom s)).2 h
  simpa [prove2] using h'

end AutomatedTheoryConstruction
