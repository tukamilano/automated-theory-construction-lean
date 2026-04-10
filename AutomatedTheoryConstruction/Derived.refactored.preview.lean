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


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

def HandedSupportClosure (Γ : List Tp) : Tp → Prop
  | Tp.atom s => AtomicCandidateTree Γ s
  | Tp.ldiv B C => Γ ≠ [] ∧ HandedSupportClosure ([B] ++ Γ) C
  | Tp.rdiv C B => Γ ≠ [] ∧ HandedSupportClosure (Γ ++ [B]) C

/-- Handed support closure exactly characterizes derivability. -/
theorem thm_handed_support_closure_iff_sequent_000048 : ∀ (Γ : List Tp) (A : Tp), HandedSupportClosure Γ A ↔ (Γ ⇒ A) := by
  intro Γ A
  induction A generalizing Γ with
  | atom s =>
      simpa [HandedSupportClosure] using
        (thm_atomic_candidate_tree_iff_sequent_000030 Γ s)
  | ldiv B C ihB ihC =>
      constructor
      · rintro ⟨hΓ, hC⟩
        exact Sequent.ldiv_r hΓ ((ihC (Γ := [B] ++ Γ)).1 hC)
      · intro h
        refine ⟨nonempty_premises h, ?_⟩
        exact (ihC (Γ := [B] ++ Γ)).2 (ldiv_invertible h)
  | rdiv C B ihC ihB =>
      constructor
      · rintro ⟨hΓ, hC⟩
        exact Sequent.rdiv_r hΓ ((ihC (Γ := Γ ++ [B])).1 hC)
      · intro h
        refine ⟨nonempty_premises h, ?_⟩
        exact (ihC (Γ := Γ ++ [B])).2 (rdiv_invertible h)


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

def isLeftOnly : Tp → Prop
  | Tp.atom _ => True
  | Tp.ldiv A B => isLeftOnly A ∧ isLeftOnly B
  | Tp.rdiv _ _ => False

def isRightOnly : Tp → Prop
  | Tp.atom _ => True
  | Tp.ldiv _ _ => False
  | Tp.rdiv B A => isRightOnly B ∧ isRightOnly A

def toLeftTp? : Tp → Option Left.Tp
  | Tp.atom s => some (Left.Tp.atom s)
  | Tp.ldiv A B => do
      let A' ← toLeftTp? A
      let B' ← toLeftTp? B
      pure (Left.Tp.ldiv A' B')
  | Tp.rdiv _ _ => none

def toRightTp? : Tp → Option Right.Tp
  | Tp.atom s => some (Right.Tp.atom s)
  | Tp.ldiv _ _ => none
  | Tp.rdiv B A => do
      let B' ← toRightTp? B
      let A' ← toRightTp? A
      pure (Right.Tp.rdiv B' A')

def toLeftCtx? (Γ : List Tp) : Option (List Left.Tp) :=
  List.mapM toLeftTp? Γ

def toRightCtx? (Γ : List Tp) : Option (List Right.Tp) :=
  List.mapM toRightTp? Γ

def leftTranslatedSequent (Γ : List Tp) (A : Tp) : Prop :=
  match (toLeftCtx? Γ, toLeftTp? A) with
  | (some ΓL, some AL) => Left.Sequent ΓL AL
  | _ => False

def rightTranslatedSequent (Γ : List Tp) (A : Tp) : Prop :=
  match (toRightCtx? Γ, toRightTp? A) with
  | (some ΓR, some AR) => Right.Sequent ΓR AR
  | _ => False

lemma exists_left_tp_of_isLeftOnly {A : Tp} (hA : isLeftOnly A) :
    ∃ AL, toLeftTp? A = some AL ∧ Left.Tp.toProductFree AL = A := by
  induction A with
  | atom s =>
      refine ⟨Left.Tp.atom s, ?_, ?_⟩ <;> rfl
  | ldiv A B ihA ihB =>
      rcases hA with ⟨hA, hB⟩
      rcases ihA hA with ⟨AL, hAL, hAL_pf⟩
      rcases ihB hB with ⟨BL, hBL, hBL_pf⟩
      refine ⟨Left.Tp.ldiv AL BL, ?_, ?_⟩
      · simp [toLeftTp?, hAL, hBL]
      · simp [Left.Tp.toProductFree, hAL_pf, hBL_pf]
  | rdiv B A =>
      cases hA

lemma exists_right_tp_of_isRightOnly {A : Tp} (hA : isRightOnly A) :
    ∃ AR, toRightTp? A = some AR ∧ Right.Tp.toProductFree AR = A := by
  induction A with
  | atom s =>
      refine ⟨Right.Tp.atom s, ?_, ?_⟩ <;> rfl
  | ldiv A B =>
      cases hA
  | rdiv B A ihB ihA =>
      rcases hA with ⟨hB, hA⟩
      rcases ihB hB with ⟨BR, hBR, hBR_pf⟩
      rcases ihA hA with ⟨AR, hAR, hAR_pf⟩
      refine ⟨Right.Tp.rdiv BR AR, ?_, ?_⟩
      · simp [toRightTp?, hBR, hAR]
      · simp [Right.Tp.toProductFree, hBR_pf, hAR_pf]

lemma exists_left_ctx_of_allLeftOnly {Γ : List Tp}
    (hΓ : ∀ x ∈ Γ, isLeftOnly x) :
    ∃ ΓL, toLeftCtx? Γ = some ΓL ∧ Left.ctxToProductFree ΓL = Γ := by
  induction Γ with
  | nil =>
      refine ⟨[], ?_, ?_⟩ <;> rfl
  | cons x xs ih =>
      have hx : isLeftOnly x := hΓ x (by simp)
      have hxs : ∀ y ∈ xs, isLeftOnly y := by
        intro y hy
        exact hΓ y (by simp [hy])
      rcases exists_left_tp_of_isLeftOnly hx with ⟨xL, hxL, hx_pf⟩
      rcases ih hxs with ⟨xsL, hxsL, hxs_pf⟩
      refine ⟨xL :: xsL, ?_, ?_⟩
      · simpa [toLeftCtx?, hxL] using
          congrArg (fun t => t.bind fun ys => some (xL :: ys)) hxsL
      · simpa [Left.ctxToProductFree, hx_pf, hxs_pf]

lemma exists_right_ctx_of_allRightOnly {Γ : List Tp}
    (hΓ : ∀ x ∈ Γ, isRightOnly x) :
    ∃ ΓR, toRightCtx? Γ = some ΓR ∧ Right.ctxToProductFree ΓR = Γ := by
  induction Γ with
  | nil =>
      refine ⟨[], ?_, ?_⟩ <;> rfl
  | cons x xs ih =>
      have hx : isRightOnly x := hΓ x (by simp)
      have hxs : ∀ y ∈ xs, isRightOnly y := by
        intro y hy
        exact hΓ y (by simp [hy])
      rcases exists_right_tp_of_isRightOnly hx with ⟨xR, hxR, hx_pf⟩
      rcases ih hxs with ⟨xsR, hxsR, hxs_pf⟩
      refine ⟨xR :: xsR, ?_, ?_⟩
      · simpa [toRightCtx?, hxR] using
          congrArg (fun t => t.bind fun ys => some (xR :: ys)) hxsR
      · simpa [Right.ctxToProductFree, hx_pf, hxs_pf]

/-- Full derivability matches the corresponding one-sided fragment derivability. -/
theorem thm_full_one_sided_conservativity_000042 : (∀ (Γ : List Tp) (A : Tp),
    (∀ x ∈ Γ, isLeftOnly x) →
    isLeftOnly A →
    (Γ ⇒ A ↔ leftTranslatedSequent Γ A))
  ∧
  (∀ (Γ : List Tp) (A : Tp),
    (∀ x ∈ Γ, isRightOnly x) →
    isRightOnly A →
    (Γ ⇒ A ↔ rightTranslatedSequent Γ A)) := by
  constructor
  · intro Γ A hΓ hA
    rcases exists_left_ctx_of_allLeftOnly hΓ with ⟨ΓL, hΓL, hΓ_pf⟩
    rcases exists_left_tp_of_isLeftOnly hA with ⟨AL, hAL, hA_pf⟩
    simp [leftTranslatedSequent, hΓL, hAL, Left.Sequent, hΓ_pf, hA_pf]
  · intro Γ A hΓ hA
    rcases exists_right_ctx_of_allRightOnly hΓ with ⟨ΓR, hΓR, hΓ_pf⟩
    rcases exists_right_tp_of_isRightOnly hA with ⟨AR, hAR, hA_pf⟩
    simp [rightTranslatedSequent, hΓR, hAR, Right.Sequent, hΓ_pf, hA_pf]


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

def residualAtomicState : List Tp → Tp → Option (List Tp × String)
  | Γ, Tp.atom s => some (Γ, s)
  | [], Tp.ldiv _ _ => none
  | Γ, Tp.ldiv B C => residualAtomicState ([B] ++ Γ) C
  | [], Tp.rdiv _ _ => none
  | Γ, Tp.rdiv C B => residualAtomicState (Γ ++ [B]) C

/-- Support closures reduce to a deterministic residual atomic state. -/
theorem thm_residual_support_normal_form_000050 : ∀ (Γ : List Tp) (A : Tp),
  (HandedSupportClosure Γ A ↔
    ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ AtomicCandidateTree Δ s) ∧
  (SupportClosure Γ A ↔
    ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ ∃ B ∈ Δ, occurs_atom s B) := by
  intro Γ A
  induction A generalizing Γ with
  | atom s =>
      constructor
      · simp [HandedSupportClosure, residualAtomicState]
      · simpa [support_ok, residualAtomicState] using
          (thm_support_closure_matches_support_ok_000036 Γ (# s))
  | ldiv B C ihB ihC =>
      cases Γ with
      | nil =>
          constructor
          · simp [HandedSupportClosure, residualAtomicState]
          · simpa [support_ok, residualAtomicState] using
              (thm_support_closure_matches_support_ok_000036 [] (B ⧹ C))
      | cons A Γ =>
          constructor
          · simpa [HandedSupportClosure, residualAtomicState] using
              (ihC (Γ := [B] ++ (A :: Γ))).1
          · rw [thm_support_closure_matches_support_ok_000036]
            simp [support_ok, residualAtomicState]
            rw [← thm_support_closure_matches_support_ok_000036 (B :: A :: Γ) C]
            exact (ihC (Γ := [B] ++ (A :: Γ))).2
  | rdiv C B ihC ihB =>
      cases Γ with
      | nil =>
          constructor
          · simp [HandedSupportClosure, residualAtomicState]
          · simpa [support_ok, residualAtomicState] using
              (thm_support_closure_matches_support_ok_000036 [] (C ⧸ B))
      | cons A Γ =>
          constructor
          · simpa [HandedSupportClosure, residualAtomicState] using
              (ihC (Γ := (A :: Γ) ++ [B])).1
          · rw [thm_support_closure_matches_support_ok_000036]
            simp [support_ok, residualAtomicState]
            rw [← thm_support_closure_matches_support_ok_000036 (A :: (Γ ++ [B])) C]
            exact (ihC (Γ := (A :: Γ) ++ [B])).2


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

def leftHandedSupportClosure (Γ : List Left.Tp) : Left.Tp → Prop
  | Left.Tp.atom s => AtomicCandidateTree (Left.ctxToProductFree Γ) s
  | Left.Tp.ldiv B C => Γ ≠ [] ∧ leftHandedSupportClosure ([B] ++ Γ) C

def rightHandedSupportClosure (Γ : List Right.Tp) : Right.Tp → Prop
  | Right.Tp.atom s => AtomicCandidateTree (Right.ctxToProductFree Γ) s
  | Right.Tp.rdiv C B => Γ ≠ [] ∧ rightHandedSupportClosure (Γ ++ [B]) C

def leftTranslatedHandedSupportClosure (Γ : List Tp) (A : Tp) : Prop :=
  match toLeftCtx? Γ, toLeftTp? A with
  | some ΓL, some AL => leftHandedSupportClosure ΓL AL
  | _, _ => False

def rightTranslatedHandedSupportClosure (Γ : List Tp) (A : Tp) : Prop :=
  match toRightCtx? Γ, toRightTp? A with
  | some ΓR, some AR => rightHandedSupportClosure ΓR AR
  | _, _ => False

lemma leftHandedSupportClosure_iff_sequent :
    ∀ (Γ : List Left.Tp) (A : Left.Tp),
      leftHandedSupportClosure Γ A ↔ Left.Sequent Γ A := by
  intro Γ A
  induction A generalizing Γ with
  | atom s =>
      simpa [leftHandedSupportClosure, Left.Sequent, Left.Tp.toProductFree] using
        (thm_atomic_candidate_tree_iff_sequent_000030 (Left.ctxToProductFree Γ) s)
  | ldiv B C ihB ihC =>
      constructor
      · rintro ⟨hΓ, hC⟩
        exact Left.Sequent.ldiv_r hΓ ((ihC (Γ := [B] ++ Γ)).1 hC)
      · intro h
        refine ⟨Left.nonempty_premises h, ?_⟩
        exact (ihC (Γ := [B] ++ Γ)).2 (Left.ldiv_invertible h)

lemma rightHandedSupportClosure_iff_sequent :
    ∀ (Γ : List Right.Tp) (A : Right.Tp),
      rightHandedSupportClosure Γ A ↔ Right.Sequent Γ A := by
  intro Γ A
  induction A generalizing Γ with
  | atom s =>
      simpa [rightHandedSupportClosure, Right.Sequent, Right.Tp.toProductFree] using
        (thm_atomic_candidate_tree_iff_sequent_000030 (Right.ctxToProductFree Γ) s)
  | rdiv C B ihC ihB =>
      constructor
      · rintro ⟨hΓ, hC⟩
        exact Right.Sequent.rdiv_r hΓ ((ihC (Γ := Γ ++ [B])).1 hC)
      · intro h
        refine ⟨Right.nonempty_premises h, ?_⟩
        exact (ihC (Γ := Γ ++ [B])).2 (Right.rdiv_invertible h)

/-- Handed support closure matches the one-sided translations. -/
theorem thm_one_sided_handed_conservativity_000051 : (∀ (Γ : List Tp) (A : Tp),
    (∀ x ∈ Γ, isLeftOnly x) →
    isLeftOnly A →
    (HandedSupportClosure Γ A ↔ leftTranslatedHandedSupportClosure Γ A))
  ∧
  (∀ (Γ : List Tp) (A : Tp),
    (∀ x ∈ Γ, isRightOnly x) →
    isRightOnly A →
    (HandedSupportClosure Γ A ↔ rightTranslatedHandedSupportClosure Γ A)) := by
  constructor
  · intro Γ A hΓ hA
    rcases exists_left_ctx_of_allLeftOnly hΓ with ⟨ΓL, hΓL, _⟩
    rcases exists_left_tp_of_isLeftOnly hA with ⟨AL, hAL, _⟩
    calc
      HandedSupportClosure Γ A ↔ Γ ⇒ A :=
        thm_handed_support_closure_iff_sequent_000048 Γ A
      _ ↔ leftTranslatedSequent Γ A :=
        (thm_full_one_sided_conservativity_000042.1 Γ A hΓ hA)
      _ ↔ leftTranslatedHandedSupportClosure Γ A := by
        simp [leftTranslatedSequent, leftTranslatedHandedSupportClosure, hΓL, hAL,
          leftHandedSupportClosure_iff_sequent]
  · intro Γ A hΓ hA
    rcases exists_right_ctx_of_allRightOnly hΓ with ⟨ΓR, hΓR, _⟩
    rcases exists_right_tp_of_isRightOnly hA with ⟨AR, hAR, _⟩
    calc
      HandedSupportClosure Γ A ↔ Γ ⇒ A :=
        thm_handed_support_closure_iff_sequent_000048 Γ A
      _ ↔ rightTranslatedSequent Γ A :=
        (thm_full_one_sided_conservativity_000042.2 Γ A hΓ hA)
      _ ↔ rightTranslatedHandedSupportClosure Γ A := by
        simp [rightTranslatedSequent, rightTranslatedHandedSupportClosure, hΓR, hAR,
          rightHandedSupportClosure_iff_sequent]


/-- Candidate trees are in bijection with residual atomic witnesses. -/
theorem thm_residual_candidate_tree_bijection_000055 : ∀ (Γ : List Tp) (A : Tp),
  ∃ reconstruct :
      { p : List Tp × String //
          residualAtomicState Γ A = some p ∧ AtomicCandidateTree p.1 p.2 } →
        CandidateTree Γ A,
    Function.Bijective reconstruct := by
  intro Γ A
  let S :=
    { p : List Tp × String //
        residualAtomicState Γ A = some p ∧ AtomicCandidateTree p.1 p.2 }
  have hS : Subsingleton S :=
    ⟨fun x y => Subtype.ext (Option.some.inj <| x.2.1.symm.trans y.2.1)⟩
  let reconstruct : S → CandidateTree Γ A := fun x =>
    (thm_candidate_tree_iff_sequent_000038 Γ A).mpr
      ((thm_handed_support_closure_iff_sequent_000048 Γ A).mp
        (((thm_residual_support_normal_form_000050 Γ A).1).mpr
          ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩))
  refine ⟨reconstruct, ?_⟩
  constructor
  · intro x y _
    exact hS.elim x y
  · intro htree
    have hseq : Γ ⇒ A :=
      (thm_candidate_tree_iff_sequent_000038 Γ A).mp htree
    have hhand : HandedSupportClosure Γ A :=
      (thm_handed_support_closure_iff_sequent_000048 Γ A).mpr hseq
    rcases ((thm_residual_support_normal_form_000050 Γ A).1).mp hhand with
      ⟨Δ, s, hres, hatom⟩
    let x : S := ⟨(Δ, s), ⟨hres, hatom⟩⟩
    refine ⟨x, ?_⟩
    exact Subsingleton.elim _ _


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

abbrev AtomicResidualState := List Tp × String

inductive AtomicResidualGraphStep : AtomicResidualState → AtomicResidualState → Prop where
  | rdiv (Γ L Δ Λ : List Tp) (A B : Tp) (s : String)
      (hc : Cand.rdiv L B A Δ Λ ∈ candidates Γ)
      (harg : Δ ⇒ A) :
      AtomicResidualGraphStep (Γ, s) (L ++ [B] ++ Λ, s)
  | ldiv (Γ Γ₁ Δ R : List Tp) (A B : Tp) (s : String)
      (hc : Cand.ldiv Γ₁ Δ A B R ∈ candidates Γ)
      (harg : Δ ⇒ A) :
      AtomicResidualGraphStep (Γ, s) (Γ₁ ++ [B] ++ R, s)

inductive AtomicResidualGraphAccepts : AtomicResidualState → Prop where
  | base (s : String) :
      AtomicResidualGraphAccepts ([# s], s)
  | step {p q : AtomicResidualState}
      (hstep : AtomicResidualGraphStep p q)
      (hacc : AtomicResidualGraphAccepts q) :
      AtomicResidualGraphAccepts p

/-- Residual atomic graph acceptance exactly recognizes derivability. -/
theorem thm_residual_graph_recognizes_sequent_000062 : ∀ (Γ : List Tp) (A : Tp),
  (Γ ⇒ A) ↔
    ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧
      AtomicResidualGraphAccepts (Δ, s) := by
  intro Γ A
  have hgraph_to_tree :
      ∀ p : AtomicResidualState,
        AtomicResidualGraphAccepts p → AtomicCandidateTree p.1 p.2
  · intro p hacc
    induction hacc with
    | base s =>
        exact AtomicCandidateTree.base s
    | step hstep hacc ih =>
        cases hstep with
        | rdiv Γ L Δ Λ A B s hc harg =>
            simpa using AtomicCandidateTree.step_rdiv Γ L Δ Λ A B s hc harg ih
        | ldiv Γ Γ₁ Δ R A B s hc harg =>
            simpa using AtomicCandidateTree.step_ldiv Γ Γ₁ Δ R A B s hc harg ih
  have htree_to_graph :
      ∀ {Δ : List Tp} {s : String},
        AtomicCandidateTree Δ s → AtomicResidualGraphAccepts (Δ, s)
  · intro Δ s htree
    induction htree with
    | base s =>
        simpa using AtomicResidualGraphAccepts.base s
    | step_rdiv Γ L Δ Λ A B s hc harg hrec ih =>
        exact AtomicResidualGraphAccepts.step
          (AtomicResidualGraphStep.rdiv Γ L Δ Λ A B s hc harg) ih
    | step_ldiv Γ Γ₁ Δ R A B s hc harg hrec ih =>
        exact AtomicResidualGraphAccepts.step
          (AtomicResidualGraphStep.ldiv Γ Γ₁ Δ R A B s hc harg) ih
  constructor
  · intro hseq
    have hhand : HandedSupportClosure Γ A :=
      (thm_handed_support_closure_iff_sequent_000048 Γ A).mpr hseq
    rcases ((thm_residual_support_normal_form_000050 Γ A).1).mp hhand with
      ⟨Δ, s, hres, htree⟩
    exact ⟨Δ, s, hres, htree_to_graph htree⟩
  · rintro ⟨Δ, s, hres, hacc⟩
    have hhand : HandedSupportClosure Γ A :=
      ((thm_residual_support_normal_form_000050 Γ A).1).mpr
        ⟨Δ, s, hres, hgraph_to_tree (Δ, s) hacc⟩
    exact (thm_handed_support_closure_iff_sequent_000048 Γ A).mp hhand


open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

inductive AtomicBranchLength : List Tp → String → Nat → Prop where
  | base (s : String) :
      AtomicBranchLength [# s] s 0
  | step_rdiv (Γ L Δ Λ : List Tp) (A B : Tp) (s : String) (n : Nat)
      (hc : Cand.rdiv L B A Δ Λ ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : AtomicBranchLength (L ++ [B] ++ Λ) s n) :
      AtomicBranchLength Γ s (n + 1)
  | step_ldiv (Γ Γ₁ Δ R : List Tp) (A B : Tp) (s : String) (n : Nat)
      (hc : Cand.ldiv Γ₁ Δ A B R ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : AtomicBranchLength (Γ₁ ++ [B] ++ R) s n) :
      AtomicBranchLength Γ s (n + 1)

/-- Residual atomic branches are bounded by the residual context degree. -/
theorem thm_residual_atomic_branch_bound_000057 : ∀ (Γ : List Tp) (A : Tp) (Δ : List Tp) (s : String),
  residualAtomicState Γ A = some (Δ, s) →
  AtomicCandidateTree Δ s →
  ∀ n : Nat, AtomicBranchLength Δ s n → n ≤ list_degree Δ := by
  intro Γ A Δ s _ _ n hlen
  have hmain :
      ∀ {Δ : List Tp} {s : String} {n : Nat},
        AtomicBranchLength Δ s n → n ≤ list_degree Δ := by
    intro Δ s n h
    induction h with
    | base s =>
        simp [list_degree, tp_degree]
    | step_rdiv Γ L Δ Λ A B s n hc harg hrec ih =>
        have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
        have hgap : list_degree (L ++ [B] ++ Λ) + 1 ≤ list_degree Γ := by
          rw [hΓ]
          simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
          omega
        exact le_trans (Nat.succ_le_succ ih) hgap
    | step_ldiv Γ Γ₁ Δ R A B s n hc harg hrec ih =>
        have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        have hgap : list_degree (Γ₁ ++ [B] ++ R) + 1 ≤ list_degree Γ := by
          rw [hΓ]
          simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
          omega
        exact le_trans (Nat.succ_le_succ ih) hgap
  exact hmain hlen


/-- Same-handed support closure agrees with handed support closure. -/
theorem thm_same_handed_support_exactness_000059_is_false : ¬((∀ (Γ : List Tp) (A : Tp),
    (∀ x ∈ Γ, isLeftOnly x) →
    isLeftOnly A →
    (SupportClosure Γ A ↔ HandedSupportClosure Γ A))
  ∧
  (∀ (Γ : List Tp) (A : Tp),
    (∀ x ∈ Γ, isRightOnly x) →
    isRightOnly A →
    (SupportClosure Γ A ↔ HandedSupportClosure Γ A))) := by
  intro h
  let bad : Tp := #"p" ⧹ #"p"
  have hleft : ∀ x ∈ [bad], isLeftOnly x := by
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    simp [bad, isLeftOnly]
  have hA : isLeftOnly (#"p" : Tp) := by
    simp [isLeftOnly]
  have hsc : SupportClosure [bad] (#"p") := by
    simpa [bad] using
      (SupportClosure.replace
        (Γ := []) (L := []) (R := []) (Λ := [])
        (B := #"p") (B' := bad) (C := #"p")
        (fun s hs => by
          simp [occurs_atom, bad] at hs ⊢
          exact hs)
        (SupportClosure.self (#"p")))
  have hhand : HandedSupportClosure [bad] (#"p") :=
    (h.1 [bad] (#"p") hleft hA).mp hsc
  have hseq : [bad] ⇒ #"p" :=
    (thm_handed_support_closure_iff_sequent_000048 [bad] (#"p")).mp hhand
  have heq : bad = #"p" :=
    (thm_singleton_atomic_sequent_iff_000011 (A := bad) (s := "p")).mp hseq
  simp [bad] at heq

end AutomatedTheoryConstruction
