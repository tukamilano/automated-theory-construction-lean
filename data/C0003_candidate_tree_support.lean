import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0002_support_ok_atom

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

/-- Candidate trees characterize sequents. -/
theorem thm_candidate_tree_iff_sequent_000038 : ∀ (Γ : List Tp) (A : Tp), CandidateTree Γ A ↔ (Γ ⇒ A) := by
  intro Γ A
  constructor
  · intro h
    induction h with
    | base s =>
        exact thm_singleton_atomic_sequent_iff_000011.mpr rfl
    | step_rdiv Γ L Δ Λ A B s hc harg hrec ih =>
        have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
        subst Γ
        exact Sequent.rdiv_l harg ih
    | step_ldiv Γ Γ₁ Δ R A B s hc harg hrec ih =>
        have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        subst Γ
        exact Sequent.ldiv_l harg ih
    | ldiv_r Γ A B hne hrec ih =>
        exact Sequent.ldiv_r hne ih
    | rdiv_r Γ A B hne hrec ih =>
        exact Sequent.rdiv_r hne ih
  · have hatom : ∀ (Γ : List Tp) (s : String), AtomicCandidateTree Γ s → CandidateTree Γ (# s) := by
      intro Γ s h
      induction h with
      | base s =>
          exact CandidateTree.base s
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
    exact fun a => (hcomplete A Γ ∘ fun a_1 => a) Γ

lemma candidateTree_atom_iff_atomicCandidateTree (Γ : List Tp) (s : String) :
    CandidateTree Γ (# s) ↔ AtomicCandidateTree Γ s := by
  calc
    CandidateTree Γ (# s) ↔ (Γ ⇒ # s) :=
      thm_candidate_tree_iff_sequent_000038 Γ (# s)
    _ ↔ AtomicCandidateTree Γ s :=
      (thm_atomic_candidate_tree_iff_sequent_000030 Γ s).symm

theorem supportClosure_ldiv_atom_counterexample :
    SupportClosure [#"p" ⧹ #"p"] (#"p") ∧
      ¬ ([#"p" ⧹ #"p"] ⇒ #"p") := by
  constructor
  · exact (supportClosure_atom_iff_occurs_in_context [#"p" ⧹ #"p"] "p").2
      ⟨#"p" ⧹ #"p", List.mem_singleton.mpr rfl, by simp [occurs_atom]⟩
  · intro hseq
    have heq : (#"p" ⧹ #"p" : Tp) = #"p" :=
      (thm_singleton_atomic_sequent_iff_000011 (A := #"p" ⧹ #"p") (s := "p")).mp hseq
    cases heq


/-- Support closure is exactly derivability. -/
theorem thm_support_closure_exact_complete_000041_is_false : ¬(∀ (Γ : List Tp) (A : Tp), SupportClosure Γ A ↔ (Γ ⇒ A)) := by
  intro h
  rcases supportClosure_ldiv_atom_counterexample with ⟨hsc, hnotSeq⟩
  exact hnotSeq ((h [#"p" ⧹ #"p"] (#"p")).mp hsc)


def HandedSupportClosure (Γ : List Tp) : Tp → Prop
  | Tp.atom s => AtomicCandidateTree Γ s
  | Tp.ldiv B C => Γ ≠ [] ∧ HandedSupportClosure ([B] ++ Γ) C
  | Tp.rdiv C B => Γ ≠ [] ∧ HandedSupportClosure (Γ ++ [B]) C

theorem handedSupportClosure_iff_candidateTree :
    ∀ (Γ : List Tp) (A : Tp), HandedSupportClosure Γ A ↔ CandidateTree Γ A := by
  intro Γ A
  induction A generalizing Γ with
  | atom s =>
      simpa [HandedSupportClosure] using
        (candidateTree_atom_iff_atomicCandidateTree Γ s).symm
  | ldiv B C ihB ihC =>
      constructor
      · rintro ⟨hΓ, hC⟩
        exact CandidateTree.ldiv_r Γ B C hΓ ((ihC (Γ := [B] ++ Γ)).1 hC)
      · intro h
        cases h with
        | ldiv_r _ _ _ hΓ hC =>
            exact ⟨hΓ, (ihC (Γ := [B] ++ Γ)).2 hC⟩
  | rdiv C B ihC ihB =>
      constructor
      · rintro ⟨hΓ, hC⟩
        exact CandidateTree.rdiv_r Γ B C hΓ ((ihC (Γ := Γ ++ [B])).1 hC)
      · intro h
        cases h with
        | rdiv_r _ _ _ hΓ hC =>
            exact ⟨hΓ, (ihC (Γ := Γ ++ [B])).2 hC⟩

/-- Handed support closure exactly characterizes derivability. -/
theorem thm_handed_support_closure_iff_sequent_000048 : ∀ (Γ : List Tp) (A : Tp), HandedSupportClosure Γ A ↔ (Γ ⇒ A) := by
  intro Γ A
  exact (handedSupportClosure_iff_candidateTree Γ A).trans
    (thm_candidate_tree_iff_sequent_000038 Γ A)

end AutomatedTheoryConstruction
