import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

/-- A canonical singleton derivation of the bad right-division witness. -/
theorem thm_singleton_bad_rdiv_derivable :
    ([# "p"] ⇒ (# "p" ⧸ (# "p" ⧹ # "p"))) := by
  have hp : ([# "p"] : List Tp) ⇒ # "p" := Sequent.ax
  have hldiv : ([# "p", # "p" ⧹ # "p"] : List Tp) ⇒ # "p" := by
    simpa using
      (Sequent.ldiv_l
        (Δ := [# "p"])
        (A := # "p")
        (Γ := [])
        (B := # "p")
        (Λ := [])
        (C := # "p")
        hp hp)
  have hne : ([# "p"] : List Tp) ≠ [] := nonempty_premises hp
  simpa using
    (Sequent.rdiv_r
      (Γ := [# "p"])
      (A := (# "p" ⧹ # "p"))
      (B := # "p")
      hne hldiv)

/-- A derivable conclusion has degree bounded by its context degree. -/
theorem thm_sequent_degree_bound_000005_is_false : ¬(∀ {Γ : List Tp} {A : Tp}, (Γ ⇒ A) → tp_degree A ≤ list_degree Γ) := by
  intro h
  have hle : tp_degree (# "p" ⧸ (# "p" ⧹ # "p")) ≤ list_degree [# "p"] :=
    h thm_singleton_bad_rdiv_derivable
  simp [tp_degree, list_degree] at hle

/-- A singleton sequent holds exactly when the conclusion equals its premise. -/
theorem thm_singleton_sequent_eq_000002_is_false : ¬(∀ {A B : Tp}, ([A] ⇒ B) ↔ A = B) := by
  intro h
  have heq : (#"p" : Tp) = (#"p" ⧸ (#"p" ⧹ #"p")) :=
    (h (A := #"p") (B := (#"p" ⧸ (#"p" ⧹ #"p")))).mp thm_singleton_bad_rdiv_derivable
  cases heq

/-- Shape of conclusions derivable from a singleton atom premise. -/
theorem thm_singleton_atom_derivation_shape_000009_is_false : ¬(∀ {s : String} {A : Tp}, ([# s] ⇒ A) → ∃ Δ : List Tp, Δ ⇒ # s ∧ (A = (# s ⧸ List.foldl Tp.ldiv (# s) Δ) ∨ A = List.foldr Tp.rdiv (# s) Δ)) := by
  intro h
  have hax : ([# "x"] : List Tp) ⇒ # "x" := Sequent.ax
  have hcontra :
      ∀ {Δ : List Tp},
        Δ ⇒ # "x" →
          (# "x" = (# "x" ⧸ List.foldl Tp.ldiv (# "x") Δ) ∨
            # "x" = List.foldr Tp.rdiv (# "x") Δ) →
          False := by
    intro Δ hΔ hEq
    have hne : Δ ≠ [] := nonempty_premises hΔ
    cases Δ with
    | nil =>
        exact hne rfl
    | cons A Γ =>
        simp at hEq
  rcases h (s := "x") (A := # "x") hax with ⟨Δ, hΔ, hEq⟩
  exact hcontra hΔ hEq

def atom_count : Tp → Nat
  | Tp.atom _ => 1
  | Tp.ldiv A B => atom_count A + atom_count B
  | Tp.rdiv A B => atom_count A + atom_count B

def atom_count_list : List Tp → Nat
  | [] => 0
  | A :: Γ => atom_count A + atom_count_list Γ

/-- A derivable conclusion has atom count at most that of its context. -/
theorem thm_atom_count_bounded_by_context_000010_is_false : ¬(∀ {Γ : List Tp} {A : Tp}, (Γ ⇒ A) → atom_count A ≤ atom_count_list Γ) := by
  intro h
  have hle : atom_count (# "p" ⧸ (# "p" ⧹ # "p")) ≤ atom_count_list [# "p"] :=
    h thm_singleton_bad_rdiv_derivable
  norm_num [atom_count, atom_count_list] at hle

/-- A non-atomic singleton conclusion has an outer division decomposition. -/
theorem thm_singleton_nonatom_derivation_shape_000013 : ∀ {s : String} {A : Tp}, ([# s] ⇒ A) ∧ ¬ is_atom A → (∃ B C : Tp, A = (B ⧹ C) ∧ ([B, # s] ⇒ C)) ∨ (∃ B C : Tp, A = (C ⧸ B) ∧ ([# s, B] ⇒ C)) := by
  intro s A h
  rcases h with ⟨hA, hnot⟩
  cases A with
  | atom t =>
      exfalso
      exact hnot trivial
  | ldiv B C =>
      left
      refine ⟨B, C, rfl, ?_⟩
      simpa using ldiv_invertible hA
  | rdiv C B =>
      right
      refine ⟨B, C, rfl, ?_⟩
      simpa using rdiv_invertible hA

/-- A singleton context derives an atom iff it is that atom. -/
theorem thm_singleton_atomic_sequent_iff_000011 : ∀ {A : Tp} {s : String}, ([A] ⇒ # s) ↔ A = # s := by
  intro A s
  constructor
  · intro h
    have hp : prove1 [A] (# s) := (prove1_iff_sequent).2 h
    cases A with
    | atom name =>
        have hctx : ∀ x ∈ [Tp.atom name], is_atom x := by
          intro x hx
          simp at hx
          rcases hx with rfl
          simp [is_atom]
        have hsingle : [Tp.atom name] = [Tp.atom s] := atom_generation hctx h
        simpa using List.singleton_inj.mp hsingle
    | ldiv A B =>
        unfold prove1 at hp
        simp [candidates, picks, splits] at hp
        have hnil : ¬ prove1 [] A := by
          intro hA
          have hs : ([] : List Tp) ⇒ A := (prove1_iff_sequent).1 hA
          exact (nonempty_premises hs) rfl
        exact False.elim (hnil hp.1)
    | rdiv B A =>
        unfold prove1 at hp
        simp [candidates, picks, splits] at hp
        have hnil : ¬ prove1 [] A := by
          intro hA
          have hs : ([] : List Tp) ⇒ A := (prove1_iff_sequent).1 hA
          exact (nonempty_premises hs) rfl
        exact False.elim (hnil hp.1)
  · rintro rfl
    exact Sequent.ax

/-- Characterize sequents from a singleton atomic context. -/
theorem thm_singleton_atom_sequent_iff_000018 : ∀ {s : String} {A : Tp}, ([# s] ⇒ A) ↔ A = # s ∨ (∃ B C : Tp, A = (B ⧹ C) ∧ ([B, # s] ⇒ C)) ∨ (∃ B C : Tp, A = (C ⧸ B) ∧ ([# s, B] ⇒ C)) := by
  intro s A
  constructor
  · intro h
    cases A with
    | atom name =>
        left
        have hctx : ∀ x ∈ [Tp.atom s], is_atom x := by
          intro x hx
          simp at hx
          rcases hx with rfl
          simp [is_atom]
        have hsingle : [Tp.atom s] = [Tp.atom name] := atom_generation hctx h
        simpa using (List.singleton_inj.mp hsingle).symm
    | ldiv B C =>
        right
        left
        refine ⟨B, C, rfl, ?_⟩
        simpa using ldiv_invertible h
    | rdiv C B =>
        right
        right
        refine ⟨B, C, rfl, ?_⟩
        simpa using rdiv_invertible h
  · intro h
    rcases h with rfl | h | h
    · exact thm_singleton_atomic_sequent_iff_000011.mpr rfl
    · rcases h with ⟨B, C, rfl, hBC⟩
      have hne : ([# s] : List Tp) ≠ [] := by simp
      simpa using Sequent.ldiv_r hne hBC
    · rcases h with ⟨B, C, rfl, hCB⟩
      have hne : ([# s] : List Tp) ≠ [] := by simp
      simpa using Sequent.rdiv_r hne hCB

/-- Characterize derivations from a singleton context. -/
theorem thm_singleton_sequent_iff_cases_000022 : ∀ {A C : Tp}, ([A] ⇒ C) ↔ A = C ∨ (∃ B D : Tp, C = (B ⧹ D) ∧ ([B, A] ⇒ D)) ∨ (∃ B D : Tp, C = (D ⧸ B) ∧ ([A, B] ⇒ D)) := by
  intro A C
  constructor
  · intro h
    cases C with
    | atom s =>
        left
        exact thm_singleton_atomic_sequent_iff_000011.mp h
    | ldiv B D =>
        right
        left
        refine ⟨B, D, rfl, ?_⟩
        simpa using ldiv_invertible h
    | rdiv D B =>
        right
        right
        refine ⟨B, D, rfl, ?_⟩
        simpa using rdiv_invertible h
  · intro h
    rcases h with rfl | h | h
    · exact Sequent.ax
    · rcases h with ⟨B, D, rfl, hBD⟩
      have hne : ([A] : List Tp) ≠ [] := by simp
      simpa using Sequent.ldiv_r hne hBD
    · rcases h with ⟨B, D, rfl, hDB⟩
      have hne : ([A] : List Tp) ≠ [] := by simp
      simpa using Sequent.rdiv_r hne hDB

/-- Characterizes sequents derivable from atom-only contexts. -/
theorem thm_atom_context_sequent_cases_000023 : ∀ {Γ : List Tp} {A : Tp}, (∀ x ∈ Γ, is_atom x) → ((Γ ⇒ A) ↔ (∃ s : String, A = # s ∧ Γ = [# s]) ∨ (Γ ≠ [] ∧ ∃ B C : Tp, A = (B ⧹ C) ∧ ([B] ++ Γ ⇒ C)) ∨ (Γ ≠ [] ∧ ∃ B C : Tp, A = (C ⧸ B) ∧ (Γ ++ [B] ⇒ C))) := by
  intro Γ A hΓ
  constructor
  · intro h
    cases A with
    | atom s =>
        left
        exact ⟨s, rfl, atom_generation hΓ h⟩
    | ldiv B C =>
        right
        left
        refine ⟨nonempty_premises h, B, C, rfl, ?_⟩
        exact ldiv_invertible h
    | rdiv C B =>
        right
        right
        refine ⟨nonempty_premises h, B, C, rfl, ?_⟩
        exact rdiv_invertible h
  · intro h
    rcases h with ⟨s, rfl, rfl⟩ | ⟨hne, B, C, rfl, h⟩ | ⟨hne, B, C, rfl, h⟩
    · exact thm_singleton_atomic_sequent_iff_000011.mpr rfl
    · simpa using Sequent.ldiv_r hne h
    · simpa using Sequent.rdiv_r hne h

end AutomatedTheoryConstruction
