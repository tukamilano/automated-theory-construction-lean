import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0005_support_handed_closure

set_option autoImplicit false

namespace AutomatedTheoryConstruction

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

theorem atomicResidualGraphAccepts_iff_atomicCandidateTree :
    ∀ {Δ : List Tp} {s : String},
      AtomicResidualGraphAccepts (Δ, s) ↔ AtomicCandidateTree Δ s := by
  have hgraph_to_tree :
      ∀ p : AtomicResidualState,
        AtomicResidualGraphAccepts p → AtomicCandidateTree p.1 p.2 := by
    intro p hacc
    induction hacc with
    | base s =>
        exact AtomicCandidateTree.base s
    | step hstep hacc ih =>
        cases hstep with
        | rdiv Γ L Δ Λ A B s hc harg =>
            exact AtomicCandidateTree.step_rdiv (Γ, s).1 L Δ Λ A B (Γ, s).2 hc harg ih
        | ldiv Γ Γ₁ Δ R A B s hc harg =>
            exact AtomicCandidateTree.step_ldiv (Γ, s).1 Γ₁ Δ R A B (Γ, s).2 hc harg ih
  have htree_to_graph :
      ∀ {Δ : List Tp} {s : String},
        AtomicCandidateTree Δ s → AtomicResidualGraphAccepts (Δ, s) := by
    intro Δ s htree
    induction htree with
    | base s =>
        exact AtomicResidualGraphAccepts.base s
    | step_rdiv Γ L Δ Λ A B s hc harg hrec ih =>
        exact AtomicResidualGraphAccepts.step
          (AtomicResidualGraphStep.rdiv Γ L Δ Λ A B s hc harg) ih
    | step_ldiv Γ Γ₁ Δ R A B s hc harg hrec ih =>
        exact AtomicResidualGraphAccepts.step
          (AtomicResidualGraphStep.ldiv Γ Γ₁ Δ R A B s hc harg) ih
  exact fun {Δ} {s} => { mp := hgraph_to_tree (Δ, s), mpr := htree_to_graph }

/-- Residual atomic graph acceptance exactly recognizes derivability. -/
theorem thm_residual_graph_recognizes_sequent_000062 : ∀ (Γ : List Tp) (A : Tp),
  (Γ ⇒ A) ↔
    ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧
      AtomicResidualGraphAccepts (Δ, s) := by
  intro Γ A
  constructor
  · intro hseq
    rcases (thm_sequent_iff_residual_atomic_witness Γ A).mp hseq with
      ⟨Δ, s, hres, htree⟩
    exact ⟨Δ, s, hres,
      (atomicResidualGraphAccepts_iff_atomicCandidateTree (Δ := Δ) (s := s)).2 htree⟩
  · rintro ⟨Δ, s, hres, hacc⟩
    exact (thm_sequent_iff_residual_atomic_witness Γ A).mpr
      ⟨Δ, s, hres,
        (atomicResidualGraphAccepts_iff_atomicCandidateTree (Δ := Δ) (s := s)).1 hacc⟩


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
        exact Nat.zero_le (list_degree [#s])
    | step_rdiv Γ L Δ Λ A B s n hc harg hrec ih =>
        have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
        have hgap : list_degree (L ++ [B] ++ Λ) + 1 ≤ list_degree Γ := by
          rw [hΓ]
          simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
          omega
        exact add_le_of_add_le_right hgap ih
    | step_ldiv Γ Γ₁ Δ R A B s n hc harg hrec ih =>
        have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        have hgap : list_degree (Γ₁ ++ [B] ++ R) + 1 ≤ list_degree Γ := by
          rw [hΓ]
          simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
          omega
        exact add_le_of_add_le_right hgap ih
  exact le_of_eq_of_le rfl (hmain hlen)


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
  rcases supportClosure_ldiv_atom_counterexample with ⟨hsc, hnotSeq⟩
  have hleft : ∀ x ∈ [#"p" ⧹ #"p"], isLeftOnly x := by
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    simp [isLeftOnly]
  have hA : isLeftOnly (#"p" : Tp) := by
    simp [isLeftOnly]
  have hhand : HandedSupportClosure [#"p" ⧹ #"p"] (#"p") :=
    (h.1 [#"p" ⧹ #"p"] (#"p") hleft hA).mp hsc
  exact hnotSeq ((thm_handed_support_closure_iff_sequent_000048 [#"p" ⧹ #"p"] (#"p")).mp hhand)

end AutomatedTheoryConstruction
