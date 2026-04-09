import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


/-- A derivable conclusion has degree bounded by its context degree. -/
theorem thm_sequent_degree_bound_000005_is_false : ¬(∀ {Γ : List Tp} {A : Tp}, (Γ ⇒ A) → tp_degree A ≤ list_degree Γ) := by
  intro h
  let p : Tp := Tp.atom "p"
  let bad : Tp := Tp.rdiv p (Tp.ldiv p p)
  have hp : [p] ⇒ p := Sequent.ax
  have hldiv : [p, Tp.ldiv p p] ⇒ p := by
    simpa [p] using
      (Sequent.ldiv_l (Δ := [p]) (A := p) (Γ := []) (B := p) (Λ := []) (C := p) hp hp)
  have hseq : [p] ⇒ bad := by
    have hne : [p] ≠ [] := by simp
    simpa [bad, p] using
      (Sequent.rdiv_r (Γ := [p]) (A := Tp.ldiv p p) (B := p) hne hldiv)
  have hle : tp_degree bad ≤ list_degree [p] := h hseq
  simpa [bad, p, tp_degree, list_degree] using hle


/-- A singleton sequent holds exactly when the conclusion equals its premise. -/
theorem thm_singleton_sequent_eq_000002_is_false : ¬(∀ {A B : Tp}, ([A] ⇒ B) ↔ A = B) := by
  intro h
  have hseq : ([#"p"] ⇒ (#"p" ⧸ (#"p" ⧹ #"p"))) := by
    decide
  have heq : (#"p" : Tp) = (#"p" ⧸ (#"p" ⧹ #"p")) :=
    (h (A := #"p") (B := (#"p" ⧸ (#"p" ⧹ #"p")))).mp hseq
  cases heq


/-- Shape of conclusions derivable from a singleton atom premise. -/
theorem thm_singleton_atom_derivation_shape_000009_is_false : ¬(∀ {s : String} {A : Tp}, ([# s] ⇒ A) → ∃ Δ : List Tp, Δ ⇒ # s ∧ (A = (# s ⧸ List.foldl Tp.ldiv (# s) Δ) ∨ A = List.foldr Tp.rdiv (# s) Δ)) := by
  intro h
  have hax : ([# "x"] : List Tp) ⇒ # "x" := Sequent.ax
  rcases h (s := "x") (A := # "x") hax with ⟨Δ, hΔ, hEq | hEq⟩
  · have hne : Δ ≠ [] := nonempty_premises hΔ
    cases Δ with
    | nil => exact hne rfl
    | cons A Γ =>
        simp at hEq
  · have hne : Δ ≠ [] := nonempty_premises hΔ
    cases Δ with
    | nil => exact hne rfl
    | cons A Γ =>
        simp at hEq


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

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
  have hp : [p] ⇒ p := Sequent.ax
  have hldiv : [p, p ⧹ p] ⇒ p := by
    simpa [p] using
      (Sequent.ldiv_l (Δ := [p]) (A := p) (Γ := []) (B := p) (Λ := []) (C := p) hp hp)
  have hseq : [p] ⇒ bad := by
    have hne : [p] ≠ [] := by simp
    simpa [bad, p] using
      (Sequent.rdiv_r (Γ := [p]) (A := p ⧹ p) (B := p) hne hldiv)
  have hle : atom_count bad ≤ atom_count_list [p] := h hseq
  norm_num [bad, p, atom_count, atom_count_list] at hle


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
    · exact Sequent.ax
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
        exact (thm_singleton_atomic_sequent_iff_000011 (A := A) (s := s)).mp h
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
        simpa using ldiv_invertible h
    | rdiv C B =>
        right
        right
        refine ⟨nonempty_premises h, B, C, rfl, ?_⟩
        simpa using rdiv_invertible h
  · intro h
    rcases h with ⟨s, rfl, rfl⟩ | ⟨hne, B, C, rfl, h⟩ | ⟨hne, B, C, rfl, h⟩
    · exact Sequent.ax
    · simpa using Sequent.ldiv_r hne h
    · simpa using Sequent.rdiv_r hne h


/-- Atomic sequents are singleton axioms or decompose through a candidate. -/
theorem thm_atom_goal_candidate_cases_000007 : ∀ (Γ : List Tp) (s : String), (Γ ⇒ # s) → Γ = [# s] ∨ ∃ c : Cand, c ∈ candidates Γ ∧ match c with | Cand.rdiv L B A Δ Λ => (Δ ⇒ A) ∧ (L ++ [B] ++ Λ ⇒ # s) | Cand.ldiv Gamma1 Δ A B R => (Δ ⇒ A) ∧ (Gamma1 ++ [B] ++ R ⇒ # s) := by
  intro Γ s h
  cases h with
  | ax =>
      left
      rfl
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      right
      refine ⟨Cand.rdiv Γ₁ B A Δ Λ, ?_, ?_⟩
      · exact candidates_rdiv_mem Γ₁ Δ Λ A B
      · exact ⟨d_arg, d_main⟩
  | ldiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      right
      refine ⟨Cand.ldiv Γ₁ Δ A B Λ, ?_, ?_⟩
      · exact candidates_ldiv_mem Γ₁ Δ Λ A B
      · exact ⟨d_arg, d_main⟩


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

def occurs_atom (t : String) : Tp → Prop
  | Tp.atom name => name = t
  | Tp.ldiv A B => occurs_atom t A ∨ occurs_atom t B
  | Tp.rdiv A B => occurs_atom t A ∨ occurs_atom t B

/-- Any atom occurring in a derived type already occurs in the context. -/
theorem thm_occurs_atom_from_context_000021_is_false : ¬(∀ {Γ : List Tp} {A : Tp} {t : String}, (Γ ⇒ A) → occurs_atom t A → ∃ B ∈ Γ, occurs_atom t B) := by
  intro h
  let p : Tp := #"p"
  let q : Tp := #"q"
  let bad : Tp := q ⧸ (p ⧹ q)
  have hp : [p] ⇒ p := Sequent.ax
  have hq : [q] ⇒ q := Sequent.ax
  have hldiv : [p, p ⧹ q] ⇒ q := by
    simpa [p, q] using
      (Sequent.ldiv_l (Δ := [p]) (A := p) (Γ := []) (B := q) (Λ := []) (C := q) hp hq)
  have hseq : [p] ⇒ bad := by
    have hne : [p] ≠ [] := by simp
    simpa [bad, p, q] using
      (Sequent.rdiv_r (Γ := [p]) (A := p ⧹ q) (B := q) hne hldiv)
  have hocc : occurs_atom "q" bad := by
    simp [occurs_atom, bad, p, q]
  rcases h (Γ := [p]) (A := bad) (t := "q") hseq hocc with ⟨B, hB, hBt⟩
  simp [p] at hB
  subst hB
  simp [occurs_atom] at hBt


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

def support_ok (Γ : List Tp) : Tp → Prop
  | Tp.atom s => ∃ B ∈ Γ, occurs_atom s B
  | Tp.ldiv B C => Γ ≠ [] ∧ support_ok ([B] ++ Γ) C
  | Tp.rdiv C B => Γ ≠ [] ∧ support_ok (Γ ++ [B]) C

lemma support_ok_replace
    {Γ L R Λ : List Tp} {B B' C : Tp}
    (hocc : ∀ s : String, occurs_atom s B → occurs_atom s B')
    (h : support_ok (Γ ++ [B] ++ Λ) C) :
    support_ok (Γ ++ L ++ [B'] ++ R ++ Λ) C := by
  induction C generalizing Γ L R Λ with
  | atom s =>
      rcases h with ⟨X, hX, hXocc⟩
      simp at hX
      rcases hX with hX | rfl | hX
      · refine ⟨X, ?_, hXocc⟩
        simp [hX]
      · refine ⟨B', ?_, hocc s hXocc⟩
        simp
      · refine ⟨X, ?_, hXocc⟩
        simp [hX]
  | ldiv D C ihD ihC =>
      rcases h with ⟨_, hC⟩
      constructor
      · simp
      · simpa [List.append_assoc] using
          ihC (Γ := [D] ++ Γ) (L := L) (R := R) (Λ := Λ) (by simpa [List.append_assoc] using hC)
  | rdiv C D ihC ihD =>
      rcases h with ⟨_, hC⟩
      constructor
      · simp
      · simpa [List.append_assoc] using
          ihC (Γ := Γ) (L := L) (R := R) (Λ := Λ ++ [D]) (by simpa [List.append_assoc] using hC)

lemma support_ok_self_singleton (A : Tp) : support_ok [A] A := by
  induction A with
  | atom s =>
      refine ⟨# s, by simp, by simp [occurs_atom]⟩
  | ldiv B C ihB ihC =>
      constructor
      · simp
      · simpa using
          (support_ok_replace
            (Γ := []) (L := [B]) (R := []) (Λ := [])
            (B := C) (B' := B ⧹ C) (C := C)
            (fun s hs => by simp [occurs_atom, hs]) ihC)
  | rdiv C B ihC ihB =>
      constructor
      · simp
      · simpa using
          (support_ok_replace
            (Γ := []) (L := []) (R := [B]) (Λ := [])
            (B := C) (B' := C ⧸ B) (C := C)
            (fun s hs => by simp [occurs_atom, hs]) ihC)

/-- Every derivable sequent satisfies the recursive support predicate. -/
theorem thm_derivable_support_ok_000032 : ∀ {Γ : List Tp} {A : Tp}, (Γ ⇒ A) → support_ok Γ A := by
  intro Γ A h
  induction h with
  | ax =>
      rename_i A
      simpa using support_ok_self_singleton A
  | rdiv_r hne hBA ih =>
      exact ⟨hne, by simpa using ih⟩
  | ldiv_r hne hAB ih =>
      exact ⟨hne, by simpa using ih⟩
  | rdiv_l d_arg d_main ih_arg ih_main =>
      rename_i Δ A' Γ' B Λ C
      simpa [List.append_assoc] using
        (support_ok_replace
          (Γ := Γ') (L := []) (R := Δ) (Λ := Λ)
          (B := B) (B' := B ⧸ A') (C := C)
          (fun s hs => by simp [occurs_atom, hs]) ih_main)
  | ldiv_l d_arg d_main ih_arg ih_main =>
      rename_i Δ A' Γ' B Λ C
      simpa [List.append_assoc] using
        (support_ok_replace
          (Γ := Γ') (L := Δ) (R := []) (Λ := Λ)
          (B := B) (B' := A' ⧹ B) (C := C)
          (fun s hs => by simp [occurs_atom, hs]) ih_main)


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

inductive AtomicCandidateTree : List Tp → String → Prop where
  | base (s : String) :
      AtomicCandidateTree [# s] s
  | step_rdiv (Γ L Δ Λ : List Tp) (A B : Tp) (s : String)
      (hc : Cand.rdiv L B A Δ Λ ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : AtomicCandidateTree (L ++ [B] ++ Λ) s) :
      AtomicCandidateTree Γ s
  | step_ldiv (Γ Γ₁ Δ R : List Tp) (A B : Tp) (s : String)
      (hc : Cand.ldiv Γ₁ Δ A B R ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : AtomicCandidateTree (Γ₁ ++ [B] ++ R) s) :
      AtomicCandidateTree Γ s

/-- Atomic candidate trees characterize atomic sequents. -/
theorem thm_atomic_candidate_tree_iff_sequent_000030 : ∀ (Γ : List Tp) (s : String), AtomicCandidateTree Γ s ↔ (Γ ⇒ # s) := by
  intro Γ s
  constructor
  · intro h
    induction h with
    | base s =>
        exact Sequent.ax
    | step_rdiv Γ L Δ Λ A B s hc harg hrec ih =>
        have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
        subst Γ
        simpa [List.append_assoc] using
          (Sequent.rdiv_l (Γ := L) (Δ := Δ) (A := A) (B := B) (Λ := Λ) (C := # s) harg ih)
    | step_ldiv Γ Γ₁ Δ R A B s hc harg hrec ih =>
        have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        subst Γ
        simpa [List.append_assoc] using
          (Sequent.ldiv_l (Γ := Γ₁) (Δ := Δ) (A := A) (B := B) (Λ := R) (C := # s) harg ih)
  · have hcomplete : ∀ (Γ : List Tp) (s : String), (Γ ⇒ # s) → AtomicCandidateTree Γ s := by
      intro Γ s
      let n := list_degree Γ
      have hmain : ∀ n (Γ : List Tp) (s : String), list_degree Γ = n → (Γ ⇒ # s) → AtomicCandidateTree Γ s := by
        intro n
        refine Nat.strong_induction_on n ?_
        intro n ih Γ s hdeg h
        rcases thm_atom_goal_candidate_cases_000007 Γ s h with rfl | ⟨c, hc, hcases⟩
        · simpa using AtomicCandidateTree.base s
        · cases c with
          | rdiv L B A Δ Λ =>
              rcases hcases with ⟨harg, hrec⟩
              have hlt : list_degree (L ++ [B] ++ Λ) < n := by
                have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
                  symm
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
                rw [hΓ] at hdeg
                rw [← hdeg]
                simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
                omega
              exact
                AtomicCandidateTree.step_rdiv Γ L Δ Λ A B s hc harg
                  (ih (list_degree (L ++ [B] ++ Λ)) hlt (L ++ [B] ++ Λ) s rfl hrec)
          | ldiv Γ₁ Δ A B R =>
              rcases hcases with ⟨harg, hrec⟩
              have hlt : list_degree (Γ₁ ++ [B] ++ R) < n := by
                have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
                  symm
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
                rw [hΓ] at hdeg
                rw [← hdeg]
                simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
                omega
              exact
                AtomicCandidateTree.step_ldiv Γ Γ₁ Δ R A B s hc harg
                  (ih (list_degree (Γ₁ ++ [B] ++ R)) hlt (Γ₁ ++ [B] ++ R) s rfl hrec)
      exact hmain n Γ s rfl
    exact hcomplete Γ s


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

inductive SupportClosure : List Tp → Tp → Prop where
  | self (A : Tp) :
      SupportClosure [A] A
  | ldiv_r (Γ : List Tp) (B C : Tp)
      (hΓ : Γ ≠ [])
      (h : SupportClosure ([B] ++ Γ) C) :
      SupportClosure Γ (B ⧹ C)
  | rdiv_r (Γ : List Tp) (C B : Tp)
      (hΓ : Γ ≠ [])
      (h : SupportClosure (Γ ++ [B]) C) :
      SupportClosure Γ (C ⧸ B)
  | replace (Γ L R Λ : List Tp) (B B' C : Tp)
      (hocc : ∀ s : String, occurs_atom s B → occurs_atom s B')
      (h : SupportClosure (Γ ++ [B] ++ Λ) C) :
      SupportClosure (Γ ++ L ++ [B'] ++ R ++ Λ) C

/-- The inductive support closure coincides with support_ok. -/
theorem thm_support_closure_matches_support_ok_000036 : ∀ (Γ : List Tp) (A : Tp), SupportClosure Γ A ↔ support_ok Γ A := by
  intro Γ A
  constructor
  · intro h
    induction h with
    | self A =>
        simpa using support_ok_self_singleton A
    | ldiv_r Γ B C hΓ h ih =>
        exact ⟨hΓ, by simpa using ih⟩
    | rdiv_r Γ C B hΓ h ih =>
        exact ⟨hΓ, by simpa using ih⟩
    | replace Γ L R Λ B B' C hocc h ih =>
        simpa [List.append_assoc] using support_ok_replace hocc ih
  · revert Γ
    induction A with
    | atom s =>
        intro Γ h
        rcases h with ⟨B, hB, hocc⟩
        have hsplit : ∃ L R, Γ = L ++ [B] ++ R := by
          induction Γ with
          | nil =>
              cases hB
          | cons X Γ ih =>
              simp at hB
              rcases hB with rfl | hB
              · exact ⟨[], Γ, by simp⟩
              · rcases ih hB with ⟨L, R, hLR⟩
                exact ⟨X :: L, R, by simp [hLR]⟩
        rcases hsplit with ⟨L, R, rfl⟩
        simpa [List.append_assoc] using
          (SupportClosure.replace
            (Γ := []) (L := L) (R := R) (Λ := [])
            (B := # s) (B' := B) (C := # s)
            (fun t ht => by
              simp [occurs_atom] at ht
              simpa [ht] using hocc)
            (SupportClosure.self (# s)))
    | ldiv B C ihB ihC =>
        intro Γ h
        rcases h with ⟨hΓ, hC⟩
        exact SupportClosure.ldiv_r Γ B C hΓ (ihC ([B] ++ Γ) hC)
    | rdiv C B ihC ihB =>
        intro Γ h
        rcases h with ⟨hΓ, hC⟩
        exact SupportClosure.rdiv_r Γ C B hΓ (ihC (Γ ++ [B]) hC)


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

inductive CandidateTree : List Tp → Tp → Prop where
  | base (s : String) :
      CandidateTree [# s] (# s)
  | step_rdiv (Γ L Δ Λ : List Tp) (A B : Tp) (s : String)
      (hc : Cand.rdiv L B A Δ Λ ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : CandidateTree (L ++ [B] ++ Λ) (# s)) :
      CandidateTree Γ (# s)
  | step_ldiv (Γ Γ₁ Δ R : List Tp) (A B : Tp) (s : String)
      (hc : Cand.ldiv Γ₁ Δ A B R ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : CandidateTree (Γ₁ ++ [B] ++ R) (# s)) :
      CandidateTree Γ (# s)
  | ldiv_r (Γ : List Tp) (A B : Tp)
      (hne : Γ ≠ [])
      (hrec : CandidateTree ([A] ++ Γ) B) :
      CandidateTree Γ (A ⧹ B)
  | rdiv_r (Γ : List Tp) (A B : Tp)
      (hne : Γ ≠ [])
      (hrec : CandidateTree (Γ ++ [A]) B) :
      CandidateTree Γ (B ⧸ A)

/-- Candidate trees characterize sequents. -/
theorem thm_candidate_tree_iff_sequent_000038 : ∀ (Γ : List Tp) (A : Tp), CandidateTree Γ A ↔ (Γ ⇒ A) := by
  intro Γ A
  constructor
  · intro h
    induction h with
    | base s =>
        exact Sequent.ax
    | step_rdiv Γ L Δ Λ A B s hc harg hrec ih =>
        have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
        subst Γ
        simpa [List.append_assoc] using
          (Sequent.rdiv_l (Γ := L) (Δ := Δ) (A := A) (B := B) (Λ := Λ) (C := # s) harg ih)
    | step_ldiv Γ Γ₁ Δ R A B s hc harg hrec ih =>
        have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        subst Γ
        simpa [List.append_assoc] using
          (Sequent.ldiv_l (Γ := Γ₁) (Δ := Δ) (A := A) (B := B) (Λ := R) (C := # s) harg ih)
    | ldiv_r Γ A B hne hrec ih =>
        exact Sequent.ldiv_r hne ih
    | rdiv_r Γ A B hne hrec ih =>
        exact Sequent.rdiv_r hne ih
  · have hatom : ∀ (Γ : List Tp) (s : String), AtomicCandidateTree Γ s → CandidateTree Γ (# s) := by
      intro Γ s h
      induction h with
      | base s =>
          simpa using CandidateTree.base s
      | step_rdiv Γ L Δ Λ A B s hc harg hrec ih =>
          exact CandidateTree.step_rdiv Γ L Δ Λ A B s hc harg ih
      | step_ldiv Γ Γ₁ Δ R A B s hc harg hrec ih =>
          exact CandidateTree.step_ldiv Γ Γ₁ Δ R A B s hc harg ih
    have hcomplete : ∀ (A : Tp) (Γ : List Tp), (Γ ⇒ A) → CandidateTree Γ A := by
      intro A
      induction A with
      | atom s =>
          intro Γ h
          exact hatom Γ s ((thm_atomic_candidate_tree_iff_sequent_000030 Γ s).2 h)
      | ldiv A B ihA ihB =>
          intro Γ h
          have hne : Γ ≠ [] := nonempty_premises h
          have hinner : [A] ++ Γ ⇒ B := ldiv_invertible h
          exact CandidateTree.ldiv_r Γ A B hne (ihB ([A] ++ Γ) hinner)
      | rdiv B A ihB ihA =>
          intro Γ h
          have hne : Γ ≠ [] := nonempty_premises h
          have hinner : Γ ++ [A] ⇒ B := rdiv_invertible h
          exact CandidateTree.rdiv_r Γ A B hne (ihB (Γ ++ [A]) hinner)
    exact hcomplete A Γ


/-- Support closure is exactly derivability. -/
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
