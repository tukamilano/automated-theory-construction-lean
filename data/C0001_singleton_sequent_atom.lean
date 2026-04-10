import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

/-- Any singleton context derives its self-residual. -/
theorem singleton_self_rdiv_derivable (A : Tp) : [A] ⇒ A ⧸ (A ⧹ A) := by
  have hax : [A] ⇒ A := Sequent.ax
  have hldiv : [A, A ⧹ A] ⇒ A := by
    simpa using
      (Sequent.ldiv_l (Δ := [A]) (A := A) (Γ := []) (B := A) (Λ := []) (C := A) hax hax)
  have hne : [A] ≠ [] := nonempty_premises hax
  simpa using
    (Sequent.rdiv_r (Γ := [A]) (A := A ⧹ A) (B := A) hne hldiv)


/-- A derivable conclusion has degree bounded by its context degree. -/
theorem thm_sequent_degree_bound_000005_is_false : ¬(∀ {Γ : List Tp} {A : Tp}, (Γ ⇒ A) → tp_degree A ≤ list_degree Γ) := by
  intro h
  let p : Tp := Tp.atom "p"
  let bad : Tp := Tp.rdiv p (Tp.ldiv p p)
  have hle : tp_degree bad ≤ list_degree [p] := h (Γ := [p]) (A := bad) (singleton_self_rdiv_derivable p)
  have hbad : 5 ≤ 1 := by
    have hbad' : tp_degree bad ≤ list_degree [p] := hle
    dsimp [bad, p, tp_degree, list_degree] at hbad'
    exact hbad'
  omega


/-- A singleton sequent holds exactly when the conclusion equals its premise. -/
theorem thm_singleton_sequent_eq_000002_is_false : ¬(∀ {A B : Tp}, ([A] ⇒ B) ↔ A = B) := by
  intro h
  have hseq : ([#"p"] ⇒ (#"p" ⧸ (#"p" ⧹ #"p"))) := by
    exact singleton_self_rdiv_derivable (#"p")
  have heq : (#"p" : Tp) = (#"p" ⧸ (#"p" ⧹ #"p")) :=
    (h (A := #"p") (B := (#"p" ⧸ (#"p" ⧹ #"p")))).mp hseq
  cases heq


/-- Shape of conclusions derivable from a singleton atom premise. -/
theorem thm_singleton_atom_derivation_shape_000009_is_false : ¬(∀ {s : String} {A : Tp}, ([# s] ⇒ A) → ∃ Δ : List Tp, Δ ⇒ # s ∧ (A = (# s ⧸ List.foldl Tp.ldiv (# s) Δ) ∨ A = List.foldr Tp.rdiv (# s) Δ)) := by
  intro h
  have hax : ([# "x"] : List Tp) ⇒ # "x" := Sequent.ax
  rcases h (s := "x") (A := # "x") hax with ⟨Δ, hΔ, hEq | hEq⟩
  all_goals
    have hne : Δ ≠ [] := nonempty_premises hΔ
    cases Δ with
    | nil =>
        cases hne rfl
    | cons A Γ =>
        simp at hEq


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
  let p : Tp := #"p"
  let bad : Tp := p ⧸ (p ⧹ p)
  have hle : atom_count bad ≤ atom_count_list [p] := by
    apply h
    exact singleton_self_rdiv_derivable p
  norm_num [bad, p, atom_count, atom_count_list] at hle


private lemma singleton_division_sequent_of_cases {A C : Tp} :
    ((∃ B D : Tp, C = (B ⧹ D) ∧ ([B, A] ⇒ D)) ∨
      (∃ B D : Tp, C = (D ⧸ B) ∧ ([A, B] ⇒ D))) →
    ([A] ⇒ C) := by
  intro h
  rcases h with h | h
  · rcases h with ⟨B, D, rfl, hBD⟩
    have hne : ([A] : List Tp) ≠ [] := List.cons_ne_nil A []
    simpa using Sequent.ldiv_r hne hBD
  · rcases h with ⟨B, D, rfl, hDB⟩
    have hne : ([A] : List Tp) ≠ [] := List.cons_ne_nil A []
    simpa using Sequent.rdiv_r hne hDB

/-- Forward singleton classification for non-atomic conclusions. -/
theorem singleton_nonatom_sequent_cases_forward : ∀ {A C : Tp},
    ([A] ⇒ C) → ¬ is_atom C →
      (∃ B D : Tp, C = (B ⧹ D) ∧ ([B, A] ⇒ D)) ∨
      (∃ B D : Tp, C = (D ⧸ B) ∧ ([A, B] ⇒ D)) := by
  intro A C h hnot
  cases C with
  | atom s =>
      exfalso
      exact hnot (by simp [is_atom])
  | ldiv B D =>
      left
      refine ⟨B, D, rfl, ?_⟩
      simpa using ldiv_invertible h
  | rdiv D B =>
      right
      refine ⟨B, D, rfl, ?_⟩
      simpa using rdiv_invertible h

/-- A non-atomic singleton conclusion has an outer division decomposition. -/
theorem thm_singleton_nonatom_derivation_shape_000013 : ∀ {s : String} {A : Tp}, ([# s] ⇒ A) ∧ ¬ is_atom A → (∃ B C : Tp, A = (B ⧹ C) ∧ ([B, # s] ⇒ C)) ∨ (∃ B C : Tp, A = (C ⧸ B) ∧ ([# s, B] ⇒ C)) := by
  intro s A h
  rcases h with ⟨hA, hnot⟩
  exact singleton_nonatom_sequent_cases_forward hA hnot


private lemma prove1_nil_false (A : Tp) : ¬ prove1 [] A := by
  intro hA
  have hs : ([] : List Tp) ⇒ A := (prove1_iff_sequent).1 hA
  exact (nonempty_premises hs) rfl

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
        exact List.head_eq_of_cons_eq hsingle
    | ldiv A B =>
        unfold prove1 at hp
        simp [candidates, picks, splits] at hp
        exact False.elim (prove1_nil_false A hp.1)
    | rdiv B A =>
        unfold prove1 at hp
        simp [candidates, picks, splits] at hp
        exact False.elim (prove1_nil_false A hp.1)
  · rintro rfl
    exact Sequent.ax


/-- Characterize sequents from a singleton atomic context. -/
theorem thm_singleton_atom_sequent_iff_000018 : ∀ {s : String} {A : Tp}, ([# s] ⇒ A) ↔ A = # s ∨ (∃ B C : Tp, A = (B ⧹ C) ∧ ([B, # s] ⇒ C)) ∨ (∃ B C : Tp, A = (C ⧸ B) ∧ ([# s, B] ⇒ C)) := by
  intro s A
  constructor
  · intro h
    by_cases hAtom : is_atom A
    · left
      cases A with
      | atom name =>
          simpa using
            ((thm_singleton_atomic_sequent_iff_000011 (A := # s) (s := name)).mp h).symm
      | ldiv B C =>
          simp [is_atom] at hAtom
      | rdiv C B =>
          simp [is_atom] at hAtom
    · right
      exact singleton_nonatom_sequent_cases_forward h hAtom
  · intro h
    rcases h with rfl | h
    · exact thm_singleton_atomic_sequent_iff_000011.mpr rfl
    · exact singleton_division_sequent_of_cases h


/-- Characterize derivations from a singleton context. -/
theorem thm_singleton_sequent_iff_cases_000022 : ∀ {A C : Tp}, ([A] ⇒ C) ↔ A = C ∨ (∃ B D : Tp, C = (B ⧹ D) ∧ ([B, A] ⇒ D)) ∨ (∃ B D : Tp, C = (D ⧸ B) ∧ ([A, B] ⇒ D)) := by
  intro A C
  constructor
  · intro h
    by_cases hAtom : is_atom C
    · left
      cases C with
      | atom s =>
          exact thm_singleton_atomic_sequent_iff_000011.mp h
      | ldiv B D =>
          simp [is_atom] at hAtom
      | rdiv D B =>
          simp [is_atom] at hAtom
    · right
      exact singleton_nonatom_sequent_cases_forward h hAtom
  · intro h
    rcases h with rfl | h
    · exact Sequent.ax
    · exact singleton_division_sequent_of_cases h


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
    · exact Sequent.ldiv_r hne h
    · exact Sequent.rdiv_r hne h

end AutomatedTheoryConstruction
