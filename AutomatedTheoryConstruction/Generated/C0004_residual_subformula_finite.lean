import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0003_left_right_handed

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
            exact AtomicCandidateTree.step_rdiv Γ L Δ Λ A B s hc harg ih
        | ldiv Γ Γ₁ Δ R A B s hc harg =>
            exact AtomicCandidateTree.step_ldiv Γ Γ₁ Δ R A B s hc harg ih
  have htree_to_graph :
      ∀ {Δ : List Tp} {s : String},
        AtomicCandidateTree Δ s → AtomicResidualGraphAccepts (Δ, s)
  · intro Δ s htree
    induction htree with
    | base s =>
        exact AtomicResidualGraphAccepts.base s
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

inductive Subformula : Tp → Tp → Prop where
  | refl (A : Tp) : Subformula A A
  | ldiv_left {A B C : Tp} : Subformula A B → Subformula A (B ⧹ C)
  | ldiv_right {A B C : Tp} : Subformula A C → Subformula A (B ⧹ C)
  | rdiv_left {A B C : Tp} : Subformula A B → Subformula A (B ⧸ C)
  | rdiv_right {A B C : Tp} : Subformula A C → Subformula A (B ⧸ C)

/-- Residual atomic states only use source subformulas and source atoms. -/
theorem thm_residual_state_subformula_occurs_000061 : ∀ {Γ Δ : List Tp} {A : Tp} {s : String},
  residualAtomicState Γ A = some (Δ, s) →
    (∀ B ∈ Δ, ∃ C ∈ Γ ++ [A], Subformula B C) ∧
    (∃ C ∈ Γ ++ [A], occurs_atom s C) := by
  intro Γ Δ A s hres
  induction A generalizing Γ Δ s with
  | atom t =>
      simp [residualAtomicState] at hres
      rcases hres with ⟨rfl, rfl⟩
      constructor
      · intro B hB
        exact ⟨B, by simp [hB], Subformula.refl B⟩
      · exact ⟨# t, by simp, by simp [occurs_atom]⟩
  | ldiv B C ihB ihC =>
      cases Γ with
      | nil =>
          simp [residualAtomicState] at hres
      | cons A Γ =>
          have hih := ihC (Γ := B :: A :: Γ) (Δ := Δ) (s := s) hres
          rcases hih with ⟨hsub, hocc⟩
          constructor
          · intro X hX
            rcases hsub X hX with ⟨Y, hYmem, hXY⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYeq | hYmem | hYeq
            · subst Y
              exact ⟨B ⧹ C, by simp, Subformula.ldiv_left hXY⟩
            · subst Y
              exact ⟨A, by simp, hXY⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hXY⟩
            · subst Y
              exact ⟨B ⧹ C, by simp, Subformula.ldiv_right hXY⟩
          · rcases hocc with ⟨Y, hYmem, hYs⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYeq | hYmem | hYeq
            · subst Y
              exact ⟨B ⧹ C, by simp, by simp [occurs_atom, hYs]⟩
            · subst Y
              exact ⟨A, by simp, hYs⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hYs⟩
            · subst Y
              exact ⟨B ⧹ C, by simp, by simp [occurs_atom, hYs]⟩
  | rdiv C B ihC ihB =>
      cases Γ with
      | nil =>
          simp [residualAtomicState] at hres
      | cons A Γ =>
          have hih := ihC (Γ := (A :: Γ) ++ [B]) (Δ := Δ) (s := s) hres
          rcases hih with ⟨hsub, hocc⟩
          constructor
          · intro X hX
            rcases hsub X hX with ⟨Y, hYmem, hXY⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYmem | hYeq | hYeq
            · subst Y
              exact ⟨A, by simp, hXY⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hXY⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, Subformula.rdiv_right hXY⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, Subformula.rdiv_left hXY⟩
          · rcases hocc with ⟨Y, hYmem, hYs⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYmem | hYeq | hYeq
            · subst Y
              exact ⟨A, by simp, hYs⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hYs⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, by simp [occurs_atom, hYs]⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, by simp [occurs_atom, hYs]⟩

lemma subformula_trans {A B C : Tp} : Subformula A B → Subformula B C → Subformula A C := by
  intro hAB hBC
  induction hBC with
  | refl => exact hAB
  | ldiv_left h ih => exact Subformula.ldiv_left ih
  | ldiv_right h ih => exact Subformula.ldiv_right ih
  | rdiv_left h ih => exact Subformula.rdiv_left ih
  | rdiv_right h ih => exact Subformula.rdiv_right ih

/-- Reachable residual states keep the same atom and stay within source subformulas. -/
theorem thm_residual_reachable_subformula_invariant_000065 : ∀ (Γ Δ : List Tp) (A : Tp) (s : String) (q : AtomicResidualState),
  residualAtomicState Γ A = some (Δ, s) →
  Relation.ReflTransGen AtomicResidualGraphStep (Δ, s) q →
  q.2 = s ∧ ∀ B ∈ q.1, ∃ C ∈ Γ ++ [A], Subformula B C := by
  intro Γ Δ A s q hres hreach
  have hstart : ∀ B ∈ Δ, ∃ C ∈ Γ ++ [A], Subformula B C :=
    (thm_residual_state_subformula_occurs_000061 (Γ := Γ) (Δ := Δ) (A := A) (s := s) hres).1
  induction hreach with
  | refl =>
      constructor
      · rfl
      · simpa using hstart
  | tail hreach hstep ih =>
      rcases ih with ⟨hs, hsub⟩
      cases hstep with
      | rdiv Γ0 L Δ0 Λ A0 B0 s0 hc harg =>
          constructor
          · exact hs
          · intro X hX
            have hctx : Γ0 = L ++ [B0 ⧸ A0] ++ Δ0 ++ Λ :=
              cand_rdiv_context_eq (Γ := Γ0) (L := L) (Δ := Δ0) (Λ := Λ) (A := A0) (B := B0) hc
            have hcases : X ∈ L ∨ X = B0 ∨ X ∈ Λ := by
              simpa [List.mem_append, List.mem_singleton] using hX
            rcases hcases with hX | rfl | hX
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem
            · have hmem : Tp.rdiv X A0 ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append]
              rcases hsub (Tp.rdiv X A0) hmem with ⟨C, hC, hSC⟩
              exact ⟨C, hC, subformula_trans (Subformula.rdiv_left (Subformula.refl X)) hSC⟩
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem
      | ldiv Γ0 Γ1 Δ0 R A0 B0 s0 hc harg =>
          constructor
          · exact hs
          · intro X hX
            have hctx : Γ0 = Γ1 ++ Δ0 ++ [A0 ⧹ B0] ++ R := by
              symm
              simpa using (candidates_list_degree (Γ := Γ0) (c := Cand.ldiv Γ1 Δ0 A0 B0 R) hc)
            have hcases : X ∈ Γ1 ∨ X = B0 ∨ X ∈ R := by
              simpa [List.mem_append, List.mem_singleton] using hX
            rcases hcases with hX | rfl | hX
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem
            · have hmem : Tp.ldiv A0 X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append]
              rcases hsub (Tp.ldiv A0 X) hmem with ⟨C, hC, hSC⟩
              exact ⟨C, hC, subformula_trans (Subformula.ldiv_right (Subformula.refl X)) hSC⟩
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem

/-- Residual graph steps preserve a source-subformula bound. -/
theorem thm_residual_step_subformula_closed_000068 : ∀ (src : List Tp) (p q : AtomicResidualState),
  (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) →
  AtomicResidualGraphStep p q →
  q.2 = p.2 ∧ ∀ B ∈ q.1, ∃ C ∈ src, Subformula B C := by
  intro src p q hsrc hstep
  cases hstep with
  | rdiv Γ L Δ Λ A B s hc harg =>
      constructor
      · rfl
      · intro X hX
        have hctx : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ :=
          cand_rdiv_context_eq (Γ := Γ) (L := L) (Δ := Δ) (Λ := Λ) (A := A) (B := B) hc
        have hcases : X ∈ L ∨ X = B ∨ X ∈ Λ := by
          simpa [List.mem_append, List.mem_singleton] using hX
        rcases hcases with hX | rfl | hX
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem
        · have hmem : Tp.rdiv X A ∈ Γ := by
            rw [hctx]
            simp [List.mem_append]
          rcases hsrc (Tp.rdiv X A) hmem with ⟨C, hC, hSC⟩
          exact ⟨C, hC, subformula_trans (Subformula.rdiv_left (Subformula.refl X)) hSC⟩
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem
  | ldiv Γ Γ₁ Δ R A B s hc harg =>
      constructor
      · rfl
      · intro X hX
        have hctx : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        have hcases : X ∈ Γ₁ ∨ X = B ∨ X ∈ R := by
          simpa [List.mem_append, List.mem_singleton] using hX
        rcases hcases with hX | rfl | hX
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem
        · have hmem : Tp.ldiv A X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append]
          rcases hsrc (Tp.ldiv A X) hmem with ⟨C, hC, hSC⟩
          exact ⟨C, hC, subformula_trans (Subformula.ldiv_right (Subformula.refl X)) hSC⟩
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem

lemma subformula_set_finite (C : Tp) : Set.Finite {B : Tp | Subformula B C} := by
  induction C with
  | atom s =>
      refine (Set.finite_singleton (Tp.atom s)).subset ?_
      intro B hB
      cases hB
      simp
  | ldiv A B ihA ihB =>
      refine ((ihA.union ihB).union (Set.finite_singleton (Tp.ldiv A B))).subset ?_
      intro X hX
      cases hX with
      | refl =>
          simp
      | ldiv_left h =>
          simp [h]
      | ldiv_right h =>
          simp [h]
  | rdiv A B ihA ihB =>
      refine ((ihA.union ihB).union (Set.finite_singleton (Tp.rdiv A B))).subset ?_
      intro X hX
      cases hX with
      | refl =>
          simp
      | rdiv_left h =>
          simp [h]
      | rdiv_right h =>
          simp [h]

lemma subformula_support_finite (src : List Tp) :
    Set.Finite {B : Tp | ∃ C ∈ src, Subformula B C} := by
  induction src with
  | nil =>
      simpa using (Set.finite_empty : Set.Finite (∅ : Set Tp))
  | cons C src ih =>
      rw [show ({B : Tp | ∃ D ∈ C :: src, Subformula B D} : Set Tp) =
          {B : Tp | Subformula B C} ∪ {B : Tp | ∃ D ∈ src, Subformula B D} by
        ext B
        simp]
      exact (subformula_set_finite C).union ih

lemma finite_lists_bounded_of_finite {α : Type*} {S : Set α} (hS : S.Finite) :
    ∀ N : Nat,
      Set.Finite {l : List α | l.length ≤ N ∧ ∀ a ∈ l, a ∈ S} := by
  intro N
  induction N with
  | zero =>
      refine (Set.finite_singleton ([] : List α)).subset ?_
      intro l hl
      cases l with
      | nil =>
          simp
      | cons a tl =>
          simp at hl
  | succ N ih =>
      let T : Set (List α) := {l | l.length ≤ N ∧ ∀ a ∈ l, a ∈ S}
      have hT : T.Finite := ih
      refine ((Set.finite_singleton ([] : List α)).union
        (Set.Finite.image (fun p : α × List α => p.1 :: p.2) (hS.prod hT))).subset ?_
      intro l hl
      cases l with
      | nil =>
          simp
      | cons a tl =>
          right
          refine ⟨(a, tl), ?_, rfl⟩
          constructor
          · exact hl.2 a (by simp)
          · change tl.length ≤ N ∧ ∀ b ∈ tl, b ∈ S
            constructor
            · simpa using hl.1
            · intro b hb
              exact hl.2 b (by simp [hb])

lemma list_length_le_list_degree : ∀ Γ : List Tp, Γ.length ≤ list_degree Γ
  | [] => by
      simp [list_degree]
  | A :: Γ => by
      have hA : 1 ≤ tp_degree A := by
        cases A <;> simp [tp_degree]
      have hΓ : Γ.length ≤ list_degree Γ := list_length_le_list_degree Γ
      calc
        (A :: Γ).length = Γ.length + 1 := by simp
        _ = 1 + Γ.length := by omega
        _ ≤ tp_degree A + list_degree Γ := Nat.add_le_add hA hΓ
        _ = list_degree (A :: Γ) := by simp [list_degree]

lemma atomicResidualGraphStep_degree_lt {p q : AtomicResidualState}
    (h : AtomicResidualGraphStep p q) :
    list_degree q.1 < list_degree p.1 := by
  cases h with
  | rdiv Γ L Δ Λ A B s hc harg =>
      have hΓ : Γ = L ++ [Tp.rdiv B A] ++ Δ ++ Λ := by
        symm
        simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
      rw [hΓ]
      simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
      omega
  | ldiv Γ Γ₁ Δ R A B s hc harg =>
      have hΓ : Γ = Γ₁ ++ Δ ++ [Tp.ldiv A B] ++ R := by
        symm
        simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
      rw [hΓ]
      simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
      omega

lemma residual_reachable_degree_le {p q : AtomicResidualState}
    (h : Relation.ReflTransGen AtomicResidualGraphStep p q) :
    list_degree q.1 ≤ list_degree p.1 := by
  induction h with
  | refl =>
      exact le_rfl
  | tail hreach hstep ih =>
      exact le_trans (atomicResidualGraphStep_degree_lt hstep).le ih

/-- Reachable residual states form a finite set. -/
theorem thm_residual_reachable_finite_000071 : ∀ (Γ Δ : List Tp) (A : Tp) (s : String), residualAtomicState Γ A = some (Δ, s) → Set.Finite { q : AtomicResidualState | Relation.ReflTransGen AtomicResidualGraphStep (Δ, s) q } := by
  intro Γ Δ A s hres
  have hsubsrc : Set.Finite {B : Tp | ∃ C ∈ Γ ++ [A], Subformula B C} :=
    subformula_support_finite (Γ ++ [A])
  have hctxfin :
      Set.Finite {ctx : List Tp |
        ctx.length ≤ list_degree Δ ∧
        ∀ B ∈ ctx, ∃ C ∈ Γ ++ [A], Subformula B C} :=
    finite_lists_bounded_of_finite
      (S := {B : Tp | ∃ C ∈ Γ ++ [A], Subformula B C})
      hsubsrc (list_degree Δ)
  refine (Set.Finite.image (fun ctx : List Tp => (ctx, s)) hctxfin).subset ?_
  intro q hq
  rcases thm_residual_reachable_subformula_invariant_000065 Γ Δ A s q hres hq with
    ⟨hs, hsub⟩
  have hdeg : list_degree q.1 ≤ list_degree Δ :=
    residual_reachable_degree_le hq
  refine ⟨q.1, ?_, ?_⟩
  · exact ⟨le_trans (list_length_le_list_degree q.1) hdeg, hsub⟩
  · cases q
    simpa using hs.symm

end AutomatedTheoryConstruction
