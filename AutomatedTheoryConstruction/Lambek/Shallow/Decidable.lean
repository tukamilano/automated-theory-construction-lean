import AutomatedTheoryConstruction.Lambek.Decidable
import AutomatedTheoryConstruction.Lambek.Shallow.Basic

namespace Mathling.Lambek.ProductFree.Shallow

@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.prove1 (ctxToProductFree Γ) A.toProductFree

@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.proveAux n (ctxToProductFree Γ) A.toProductFree

@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.prove2 (ctxToProductFree Γ) A.toProductFree

@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  simpa [proveAux, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_mono
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)

@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  simpa [proveAux, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_mono_le
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h hp)

@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  simpa [prove1, proveAux, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_sound
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)

@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  simpa [prove1, prove2, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_complete
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)

lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  simpa [prove1, prove2, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_iff_prove2
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree))

@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_sound
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)

@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_complete
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)

@[grind .]
lemma prove1_iff_sequent {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ Γ ⇒ A := by
  constructor <;> [apply prove1_sound; apply prove1_complete]

@[grind .]
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  rw [← prove1_iff_prove2, prove1_iff_sequent]

instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent

example : [Tp.atom "p", Tp.ldiv "p" "q"] ⇒ Tp.atom "q" := by decide

example : [Tp.rdiv "q" "p", Tp.atom "p"] ⇒ Tp.atom "q" := by decide

end Mathling.Lambek.ProductFree.Shallow
