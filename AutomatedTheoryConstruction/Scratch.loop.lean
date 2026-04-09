import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

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

end AutomatedTheoryConstruction
