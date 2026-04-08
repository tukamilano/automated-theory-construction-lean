import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_atom_context_sequent_iff_000007_is_false : ¬(∀ {Γ : List Mathling.Lambek.ProductFree.Tp} {A : Mathling.Lambek.ProductFree.Tp}, (∀ x ∈ Γ, Mathling.Lambek.ProductFree.is_atom x) → (Mathling.Lambek.ProductFree.Sequent Γ A ↔ ∃ s : String, Γ = [Mathling.Lambek.ProductFree.Tp.atom s] ∧ A = Mathling.Lambek.ProductFree.Tp.atom s)) := by
  intro h
  have h_atoms :
      ∀ x ∈ ([Mathling.Lambek.ProductFree.Tp.atom "a"] :
        List Mathling.Lambek.ProductFree.Tp),
        Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    simp at hx
    rcases hx with rfl
    simp [Mathling.Lambek.ProductFree.is_atom]
  have ha :
      Mathling.Lambek.ProductFree.Sequent
        [Mathling.Lambek.ProductFree.Tp.atom "a"]
        (Mathling.Lambek.ProductFree.Tp.atom "a") :=
    Mathling.Lambek.ProductFree.Sequent.ax
  have hb :
      Mathling.Lambek.ProductFree.Sequent
        [Mathling.Lambek.ProductFree.Tp.atom "b"]
        (Mathling.Lambek.ProductFree.Tp.atom "b") :=
    Mathling.Lambek.ProductFree.Sequent.ax
  have h_rdiv :
      Mathling.Lambek.ProductFree.Sequent
        [ Mathling.Lambek.ProductFree.Tp.rdiv
            (Mathling.Lambek.ProductFree.Tp.atom "b")
            (Mathling.Lambek.ProductFree.Tp.atom "a"),
          Mathling.Lambek.ProductFree.Tp.atom "a" ]
        (Mathling.Lambek.ProductFree.Tp.atom "b") := by
    simpa using
      (Mathling.Lambek.ProductFree.Sequent.rdiv_l
        (Γ := [])
        (Δ := [Mathling.Lambek.ProductFree.Tp.atom "a"])
        (Λ := [])
        (A := Mathling.Lambek.ProductFree.Tp.atom "a")
        (B := Mathling.Lambek.ProductFree.Tp.atom "b")
        (C := Mathling.Lambek.ProductFree.Tp.atom "b")
        ha
        hb)
  have h_seq :
      Mathling.Lambek.ProductFree.Sequent
        [Mathling.Lambek.ProductFree.Tp.atom "a"]
        (Mathling.Lambek.ProductFree.Tp.ldiv
          (Mathling.Lambek.ProductFree.Tp.rdiv
            (Mathling.Lambek.ProductFree.Tp.atom "b")
            (Mathling.Lambek.ProductFree.Tp.atom "a"))
          (Mathling.Lambek.ProductFree.Tp.atom "b")) := by
    refine Mathling.Lambek.ProductFree.Sequent.ldiv_r
      (Γ := [Mathling.Lambek.ProductFree.Tp.atom "a"])
      (A := Mathling.Lambek.ProductFree.Tp.rdiv
        (Mathling.Lambek.ProductFree.Tp.atom "b")
        (Mathling.Lambek.ProductFree.Tp.atom "a"))
      (B := Mathling.Lambek.ProductFree.Tp.atom "b")
      ?_
      ?_
    · simp
    · simpa using h_rdiv
  have hs :
      ∃ s : String,
        ([Mathling.Lambek.ProductFree.Tp.atom "a"] :
          List Mathling.Lambek.ProductFree.Tp) =
          [Mathling.Lambek.ProductFree.Tp.atom s] ∧
        Mathling.Lambek.ProductFree.Tp.ldiv
            (Mathling.Lambek.ProductFree.Tp.rdiv
              (Mathling.Lambek.ProductFree.Tp.atom "b")
              (Mathling.Lambek.ProductFree.Tp.atom "a"))
            (Mathling.Lambek.ProductFree.Tp.atom "b") =
          Mathling.Lambek.ProductFree.Tp.atom s :=
    (h
      (Γ := [Mathling.Lambek.ProductFree.Tp.atom "a"])
      (A := Mathling.Lambek.ProductFree.Tp.ldiv
        (Mathling.Lambek.ProductFree.Tp.rdiv
          (Mathling.Lambek.ProductFree.Tp.atom "b")
          (Mathling.Lambek.ProductFree.Tp.atom "a"))
        (Mathling.Lambek.ProductFree.Tp.atom "b"))
      h_atoms).mp h_seq
  rcases hs with ⟨s, _, hA⟩
  cases hA

end AutomatedTheoryConstruction
