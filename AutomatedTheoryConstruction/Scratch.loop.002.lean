import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_support_closure_exact_complete_000041_is_false : ¬(∀ (Γ : List Tp) (A : Tp), SupportClosure Γ A ↔ (Γ ⇒ A)) := by
  intro h
  let bad : Tp := #"p" ⧹ #"p"
  have hsc : SupportClosure [bad] (#"p") := by
    simpa [bad] using
      (SupportClosure.replace
        (Γ := []) (L := []) (R := []) (Λ := [])
        (B := #"p") (B' := bad) (C := #"p")
        (fun s hs => by
          simp [occurs_atom, bad] at hs ⊢
          exact hs)
        (SupportClosure.self (#"p")))
  have hseq : [bad] ⇒ #"p" := (h [bad] (#"p")).mp hsc
  have heq : bad = #"p" :=
    (thm_singleton_atomic_sequent_iff_000011 (A := bad) (s := "p")).mp hseq
  simp [bad] at heq

end AutomatedTheoryConstruction
