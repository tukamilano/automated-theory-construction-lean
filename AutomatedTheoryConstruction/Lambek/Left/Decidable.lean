import AutomatedTheoryConstruction.Lambek.Left.Basic
import AutomatedTheoryConstruction.Lambek.Decidable

namespace Mathling.Lambek.ProductFree.Left

@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  _root_.Mathling.Lambek.ProductFree.translatedProve1 Tp.toProductFree Γ A

@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  _root_.Mathling.Lambek.ProductFree.translatedProveAux Tp.toProductFree n Γ A

@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  _root_.Mathling.Lambek.ProductFree.translatedProve2 Tp.toProductFree Γ A

@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  simpa [proveAux] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_mono Tp.toProductFree h)

@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  simpa [proveAux] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_mono_le Tp.toProductFree h hp)

@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  simpa [prove1, proveAux] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_sound Tp.toProductFree h)

@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  simpa [prove1, prove2] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_complete Tp.toProductFree h)

lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  simpa [prove1, prove2] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve1_iff_Prove2 Tp.toProductFree
      (Γ := Γ) (A := A))

@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve1_sound Tp.toProductFree h)

@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve1_complete Tp.toProductFree h)

@[grind .]
lemma prove1_iff_sequent {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ Γ ⇒ A := by
  constructor <;> [apply prove1_sound; apply prove1_complete]

@[grind .]
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  simpa [prove2, Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve2_iff_Sequent Tp.toProductFree
      (Γ := Γ) (A := A))

instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent

example : [Tp.atom "p", Tp.ldiv (Tp.atom "p") (Tp.atom "q")] ⇒ Tp.atom "q" := by decide

end Mathling.Lambek.ProductFree.Left
