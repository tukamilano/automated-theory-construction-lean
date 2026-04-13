import Mathlib
import AutomatedTheoryConstruction.Theory

import AutomatedTheoryConstruction.Generated.Manifest

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


/-- A singleton sequent holds exactly when the two types are equal. -/
theorem thm_singleton_sequent_iff_eq_000001_is_false : ¬(∀ {A B : Tp}, [A] ⇒ B ↔ A = B) := by
  intro h
  let A : Tp := Tp.atom "p"
  let B : Tp := (Tp.atom "q" ⧸ Tp.atom "p") ⧹ Tp.atom "q"
  have hseq : [A] ⇒ B := by
    dsimp [A, B]
    apply Sequent.ldiv_r
    · simp
    · simpa using
        (Sequent.rdiv_l
          (Δ := [Tp.atom "p"])
          (A := Tp.atom "p")
          (Γ := [])
          (B := Tp.atom "q")
          (Λ := [])
          (C := Tp.atom "q")
          Sequent.ax
          Sequent.ax)
  have hEq : A = B := (h (A := A) (B := B)).mp hseq
  dsimp [A, B] at hEq
  cases hEq


/-- An all-atomic derivable context yields an atomic conclusion and a singleton context. -/
theorem thm_atomic_context_singleton_000002_is_false : ¬(∀ {Γ : List Tp} {A : Tp}, (∀ x ∈ Γ, is_atom x) → Γ ⇒ A → is_atom A ∧ Γ = [A]) := by
  intro h
  let p : Tp := #"p"
  let q : Tp := #"q"
  let A : Tp := ((q ⧸ p) ⧹ q)
  have hctx : ∀ x ∈ [p], is_atom x := by
    intro x hx
    simp at hx
    subst hx
    simp [p, is_atom]
  have hpq : [q ⧸ p, p] ⇒ q := by
    have hp : [p] ⇒ p := Sequent.ax
    have hq : [q] ⇒ q := Sequent.ax
    simpa using
      (Sequent.rdiv_l (Γ := []) (Δ := [p]) (Λ := []) (A := p) (B := q) (C := q) hp hq)
  have hder : [p] ⇒ A := by
    have hne : [p] ≠ [] := by simp
    simpa [A] using (Sequent.ldiv_r (Γ := [p]) (A := q ⧸ p) (B := q) hne hpq)
  have hatom : is_atom A := (h hctx hder).1
  simpa [A, is_atom] using hatom


/-- Decompose a derivation of an atomic succedent. -/
theorem thm_atom_sequent_decompose_000009 : ∀ {Γ : List Tp} {s : String}, Γ ⇒ Tp.atom s → Γ = [Tp.atom s] ∨ (∃ (L : List Tp) (B A : Tp) (Δ Λ : List Tp), Γ = L ++ [B ⧸ A] ++ Δ ++ Λ ∧ (Δ ⇒ A) ∧ (L ++ [B] ++ Λ ⇒ Tp.atom s)) ∨ (∃ (Γ₁ Δ : List Tp) (A B : Tp) (R : List Tp), Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R ∧ (Δ ⇒ A) ∧ (Γ₁ ++ [B] ++ R ⇒ Tp.atom s)) := by
  intro Γ s h
  cases h with
  | ax =>
      exact Or.inl rfl
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      exact Or.inr <| Or.inl ⟨Γ₁, B, A, Δ, Λ, rfl, d_arg, d_main⟩
  | ldiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      exact Or.inr <| Or.inr ⟨Γ₁, Δ, A, B, Λ, rfl, d_arg, d_main⟩


/-- A singleton derives an atom exactly when it is that atom. -/
theorem thm_singleton_atom_iff_eq_000008 : ∀ {A : Tp} {s : String}, ([A] ⇒ Tp.atom s) ↔ A = Tp.atom s := by
  intro A s
  constructor
  · intro h
    have hnil : ∀ X : Tp, prove1 [] X = false := by
      intro X
      unfold prove1
      cases X <;> simp [candidates, picks]
    have hp : prove1 [A] (Tp.atom s) := prove1_complete h
    cases A with
    | atom t =>
        unfold prove1 at hp
        simp [candidates, picks] at hp
        cases hp
        rfl
    | ldiv A B =>
        unfold prove1 at hp
        simp [candidates, picks, splits, hnil] at hp
    | rdiv B A =>
        unfold prove1 at hp
        simp [candidates, picks, splits, hnil] at hp
  · intro h
    simpa [h] using (Sequent.ax : [Tp.atom s] ⇒ Tp.atom s)


/-- Classifies derivable singleton sequents. -/
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


/-- Atomic derivations admit a finite focused decomposition tree. -/
theorem thm_atomic_focused_tree_exists_000016 : ∀ {Γ : List Tp} {s : String}, Γ ⇒ Tp.atom s → ∃ n : Nat, proveAux n Γ (Tp.atom s) = true := by
  intro Γ s h
  refine ⟨list_degree Γ + tp_degree (Tp.atom s) + 1, ?_⟩
  have h' : prove2 Γ (Tp.atom s) :=
    (prove2_iff_sequent (Γ := Γ) (A := Tp.atom s)).2 h
  simpa [prove2] using h'

end AutomatedTheoryConstruction
