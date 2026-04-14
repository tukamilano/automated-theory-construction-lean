import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0001_singleton_focused_tree

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

abbrev AtomicCtx (Γ : List Tp) : Prop := ∀ x ∈ Γ, is_atom x

abbrev LeftRep (Γ : List Tp) (A : Tp) : Prop :=
  ∃ Γ' : List Left.Tp, ∃ A' : Left.Tp,
    Left.ctxToProductFree Γ' = Γ ∧ A'.toProductFree = A ∧ Left.Sequent Γ' A'

abbrev RightRep (Γ : List Tp) (A : Tp) : Prop :=
  ∃ Γ' : List Right.Tp, ∃ A' : Right.Tp,
    Right.ctxToProductFree Γ' = Γ ∧ A'.toProductFree = A ∧ Right.Sequent Γ' A'

/-- An atomic-context full sequent is absent from both one-sided fragments. -/
theorem thm_atomic_context_fragment_gap_000025 : ∃ Γ A, AtomicCtx Γ ∧ Γ ⇒ A ∧ ¬ LeftRep Γ A ∧ ¬ RightRep Γ A := by
  refine ⟨[Tp.atom "r", Tp.atom "p"], Tp.rdiv (Tp.atom "q") (Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q"))), ?_⟩
  constructor
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> simp [is_atom]
  constructor
  · have h_rq : [Tp.atom "r", Tp.ldiv (Tp.atom "r") (Tp.atom "q")] ⇒ Tp.atom "q" := by
      simpa using
        (Sequent.ldiv_l
          (Δ := [Tp.atom "r"]) (A := Tp.atom "r")
          (Γ := []) (B := Tp.atom "q") (Λ := []) (C := Tp.atom "q")
          Sequent.ax Sequent.ax)
    have h_rpq :
        [Tp.atom "r", Tp.atom "p", Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q"))] ⇒
          Tp.atom "q" := by
      simpa [List.append_assoc] using
        (Sequent.ldiv_l
          (Δ := [Tp.atom "p"]) (A := Tp.atom "p")
          (Γ := [Tp.atom "r"]) (B := Tp.ldiv (Tp.atom "r") (Tp.atom "q")) (Λ := []) (C := Tp.atom "q")
          Sequent.ax h_rq)
    apply Sequent.rdiv_r
    · exact List.cons_ne_nil (#"r") [#"p"]
    · simpa using h_rpq
  constructor
  · intro hLeft
    rcases hLeft with ⟨Γ', A', hΓ, hA, hseq⟩
    cases A' <;> cases hA
  · intro hRight
    rcases hRight with ⟨Γ', A', hΓ, hA, hseq⟩
    cases A' with
    | atom s =>
        cases hA
    | rdiv B C =>
        cases C with
        | atom s =>
            have hC : (Right.Tp.atom s).toProductFree = Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q")) := by
              injection hA with _ hC
            cases hC
        | rdiv C1 C2 =>
            have hC :
                (Right.Tp.rdiv C1 C2).toProductFree =
                  Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q")) := by
              injection hA with _ hC
            cases hC

/-- Atomic derivability is exactly the axiom case or a derivable candidate. -/
theorem thm_atomic_candidate_exactness_000020 : ∀ {Γ : List Tp} {s : String}, Γ ⇒ # s ↔ Γ = [# s] ∨ ∃ c ∈ candidates Γ, match c with | Cand.rdiv L B A Δ Λ => Δ ⇒ A ∧ L ++ [B] ++ Λ ⇒ # s | Cand.ldiv Γ₁ Δ A B R => Δ ⇒ A ∧ Γ₁ ++ [B] ++ R ⇒ # s := by
  intro Γ s
  rw [← prove1_iff_sequent]
  unfold prove1
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    rcases h with hEq | ⟨⟨c, hc⟩, -, hcProof⟩
    · exact Or.symm (Or.inr hEq)
    · refine Or.inr ⟨c, hc, ?_⟩
      cases c <;> simpa [Bool.and_eq_true, prove1_iff_sequent] using hcProof
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
    rcases h with hEq | ⟨c, hc, hcProof⟩
    · exact Or.symm (Or.inr hEq)
    · refine Or.inr ?_
      refine ⟨⟨c, hc⟩, by exact List.mem_attach (candidates Γ) ⟨c, hc⟩, ?_⟩
      cases c <;> simpa [Bool.and_eq_true, prove1_iff_sequent] using hcProof

/-- Sharp focused degree witnesses exist for every realizable total degree. -/
theorem thm_sharp_focused_degree_from_two_000033_is_false : ¬(∀ N : Nat, 2 ≤ N → ∃ Γ : List Tp, ∃ A : Tp, list_degree Γ + tp_degree A = N ∧ Γ ⇒ A ∧ FocusedTree (N + 1) Γ A ∧ ∀ m < N + 1, ¬ FocusedTree m Γ A) := by
  intro hforall
  rcases hforall 2 (by exact Nat.AtLeastTwo.prop) with ⟨Γ, A, hdeg, hder, _, hmin⟩
  have hApos : 0 < tp_degree A := by
    cases A <;> simp [tp_degree]
  have hΓpos : 0 < list_degree Γ := by
    rcases List.exists_cons_of_ne_nil (nonempty_premises hder) with ⟨B, Δ, rfl⟩
    have hBpos : 0 < tp_degree B := by
      cases B <;> simp [tp_degree]
    simpa [list_degree] using add_pos_of_pos_of_nonneg hBpos (Nat.zero_le (list_degree Δ))
  have hAone : tp_degree A = 1 := by
    omega
  have hΓone : list_degree Γ = 1 := by
    omega
  cases A with
  | atom s =>
      rcases List.exists_cons_of_ne_nil (nonempty_premises hder) with ⟨B, Δ, hΓcons⟩
      subst Γ
      have hΔnil : Δ = [] := by
        cases Δ with
        | nil => exact Array.toList_empty
        | cons C Θ =>
            exfalso
            have hBpos : 0 < tp_degree B := by
              cases B <;> simp [tp_degree]
            have hTailPos : 0 < list_degree (C :: Θ) := by
              have hCpos : 0 < tp_degree C := by
                cases C <;> simp [tp_degree]
              simpa [list_degree] using add_pos_of_pos_of_nonneg hCpos (Nat.zero_le (list_degree Θ))
            have : tp_degree B + list_degree (C :: Θ) = 1 := by
              simpa [list_degree] using hΓone
            omega
      rw [hΔnil] at hΓone hder hmin
      have hBone : tp_degree B = 1 := by
        simpa [list_degree] using hΓone
      cases B with
      | atom t =>
          have hBt : Tp.atom t = Tp.atom s := by
            exact thm_singleton_atom_iff_eq_000008.mp hder
          have hft1 : FocusedTree 1 [Tp.atom s] (Tp.atom s) := by
            simp [FocusedTree]
          exact (hmin 1 (by exact Nat.one_lt_succ_succ 1)) (by simpa [hBt] using hft1)
      | ldiv B1 B2 =>
          exfalso
          have hBcontra := hBone
          simp [tp_degree] at hBcontra
          have hB1pos : 0 < tp_degree B1 := by
            cases B1 <;> simp [tp_degree]
          omega
      | rdiv B1 B2 =>
          exfalso
          have hBcontra := hBone
          simp [tp_degree] at hBcontra
          have hB1pos : 0 < tp_degree B1 := by
            cases B1 <;> simp [tp_degree]
          omega
  | ldiv A1 A2 =>
      exfalso
      have hAcontra := hAone
      simp [tp_degree] at hAcontra
      have hA1pos : 0 < tp_degree A1 := by
        cases A1 <;> simp [tp_degree]
      omega
  | rdiv A1 A2 =>
      exfalso
      have hAcontra := hAone
      simp [tp_degree] at hAcontra
      have hA1pos : 0 < tp_degree A1 := by
        cases A1 <;> simp [tp_degree]
      omega

def LeftDivisionOnly : Tp → Prop
  | Tp.atom _ => True
  | Tp.ldiv A B => LeftDivisionOnly A ∧ LeftDivisionOnly B
  | Tp.rdiv _ _ => False

def RightDivisionOnly : Tp → Prop
  | Tp.atom _ => True
  | Tp.ldiv _ _ => False
  | Tp.rdiv A B => RightDivisionOnly A ∧ RightDivisionOnly B

abbrev SameDivisionOrientation (A : Tp) : Prop :=
  LeftDivisionOnly A ∨ RightDivisionOnly A

lemma left_only_of_left_tp (A : Left.Tp) : LeftDivisionOnly A.toProductFree := by
  induction A with
  | atom s =>
      trivial
  | ldiv A B ihA ihB =>
      exact ⟨ihA, ihB⟩

lemma right_only_of_right_tp (A : Right.Tp) : RightDivisionOnly A.toProductFree := by
  induction A with
  | atom s =>
      trivial
  | rdiv B A ihB ihA =>
      exact ⟨ihB, ihA⟩

lemma exists_left_tp_of_left_only {A : Tp} (hA : LeftDivisionOnly A) :
    ∃ A' : Left.Tp, A'.toProductFree = A := by
  induction A with
  | atom s => exact ⟨Left.Tp.atom s, rfl⟩
  | ldiv A B ihA ihB =>
      rcases hA with ⟨hA, hB⟩
      rcases ihA hA with ⟨A', rfl⟩
      rcases ihB hB with ⟨B', rfl⟩
      exact ⟨Left.Tp.ldiv A' B', rfl⟩
  | rdiv A B =>
      cases hA

lemma exists_right_tp_of_right_only {A : Tp} (hA : RightDivisionOnly A) :
    ∃ A' : Right.Tp, A'.toProductFree = A := by
  induction A with
  | atom s => exact ⟨Right.Tp.atom s, rfl⟩
  | ldiv A B =>
      cases hA
  | rdiv B A ihB ihA =>
      rcases hA with ⟨hB, hA⟩
      rcases ihB hB with ⟨B', rfl⟩
      rcases ihA hA with ⟨A', rfl⟩
      exact ⟨Right.Tp.rdiv B' A', rfl⟩

lemma exists_left_ctx_of_atomic (Γ : List Tp) (hΓ : AtomicCtx Γ) :
    ∃ Γ' : List Left.Tp, Left.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : is_atom A := hΓ A (by exact List.mem_cons_self)
      have htail : AtomicCtx Γ := by
        intro x hx
        exact List.forall_mem_of_forall_mem_cons hΓ x hx
      rcases ih htail with ⟨Γ', hΓ'⟩
      cases A with
      | atom s =>
          refine ⟨Left.Tp.atom s :: Γ', ?_⟩
          simp [Left.ctxToProductFree]
          exact ⟨rfl, hΓ'⟩
      | ldiv A B =>
          cases hA
      | rdiv A B =>
          cases hA

lemma exists_right_ctx_of_atomic (Γ : List Tp) (hΓ : AtomicCtx Γ) :
    ∃ Γ' : List Right.Tp, Right.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : is_atom A := hΓ A (by exact List.mem_cons_self)
      have htail : AtomicCtx Γ := by
        intro x hx
        exact List.forall_mem_of_forall_mem_cons hΓ x hx
      rcases ih htail with ⟨Γ', hΓ'⟩
      cases A with
      | atom s =>
          refine ⟨Right.Tp.atom s :: Γ', ?_⟩
          simp [Right.ctxToProductFree]
          exact ⟨rfl, hΓ'⟩
      | ldiv A B =>
          cases hA
      | rdiv A B =>
          cases hA

/-- Atomic contexts are one-sided representable exactly for derivable one-sided succedents. -/
theorem thm_atomic_context_one_sided_iff_000035 : ∀ (Γ : List Tp) (A : Tp), AtomicCtx Γ → ((LeftRep Γ A ∨ RightRep Γ A) ↔ (Γ ⇒ A ∧ SameDivisionOrientation A)) := by
  intro Γ A hΓ
  constructor
  · intro hRep
    rcases hRep with hLeft | hRight
    · rcases hLeft with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inl ?_⟩
      · simpa [Left.Sequent, hΓ', hA'] using hseq'
      · simpa [hA'] using left_only_of_left_tp A'
    · rcases hRight with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inr ?_⟩
      · simpa [Right.Sequent, hΓ', hA'] using hseq'
      · simpa [hA'] using right_only_of_right_tp A'
  · rintro ⟨hseq, hOrient⟩
    rcases hOrient with hLeftOnly | hRightOnly
    · left
      rcases exists_left_ctx_of_atomic Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_left_tp_of_left_only hLeftOnly with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Left.Sequent, hΓ', hA'] using hseq
    · right
      rcases exists_right_ctx_of_atomic Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_right_tp_of_right_only hRightOnly with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Right.Sequent, hΓ', hA'] using hseq

lemma exists_left_ctx_of_left_only (Γ : List Tp) (hΓ : ∀ x ∈ Γ, LeftDivisionOnly x) :
    ∃ Γ' : List Left.Tp, Left.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : LeftDivisionOnly A := hΓ A (by exact List.mem_cons_self)
      have htail : ∀ x ∈ Γ, LeftDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hΓ x a
      rcases exists_left_tp_of_left_only hA with ⟨A', hA'⟩
      rcases ih htail with ⟨Γ', hΓ'⟩
      refine ⟨A' :: Γ', ?_⟩
      simpa [Left.ctxToProductFree, hA'] using congrArg (List.cons A'.toProductFree) hΓ'

lemma exists_right_ctx_of_right_only (Γ : List Tp) (hΓ : ∀ x ∈ Γ, RightDivisionOnly x) :
    ∃ Γ' : List Right.Tp, Right.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : RightDivisionOnly A := hΓ A (by exact List.mem_cons_self)
      have htail : ∀ x ∈ Γ, RightDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hΓ x a
      rcases exists_right_tp_of_right_only hA with ⟨A', hA'⟩
      rcases ih htail with ⟨Γ', hΓ'⟩
      refine ⟨A' :: Γ', ?_⟩
      simpa [Right.ctxToProductFree, hA'] using congrArg (List.cons A'.toProductFree) hΓ'

/-- One-sided representability is exactly derivability with a uniform division orientation. -/
theorem thm_uniform_orientation_fragment_iff_000041 : ∀ (Γ : List Tp) (A : Tp), (LeftRep Γ A ∨ RightRep Γ A) ↔ (Γ ⇒ A ∧ ((∀ x ∈ A :: Γ, LeftDivisionOnly x) ∨ (∀ x ∈ A :: Γ, RightDivisionOnly x))) := by
  intro Γ A
  constructor
  · intro hRep
    rcases hRep with hLeft | hRight
    · rcases hLeft with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inl ?_⟩
      · simpa [Left.Sequent, hΓ', hA'] using hseq'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa [hA'] using left_only_of_left_tp A'
        · rw [← hΓ'] at hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact left_only_of_left_tp y
    · rcases hRight with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inr ?_⟩
      · simpa [Right.Sequent, hΓ', hA'] using hseq'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa [hA'] using right_only_of_right_tp A'
        · rw [← hΓ'] at hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact right_only_of_right_tp y
  · rintro ⟨hseq, hOrient⟩
    rcases hOrient with hLeftOnly | hRightOnly
    · left
      have hA : LeftDivisionOnly A := hLeftOnly A (by exact List.mem_cons_self)
      have hΓ : ∀ x ∈ Γ, LeftDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hLeftOnly x a
      rcases exists_left_ctx_of_left_only Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_left_tp_of_left_only hA with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Left.Sequent, hΓ', hA'] using hseq
    · right
      have hA : RightDivisionOnly A := hRightOnly A (by exact List.mem_cons_self)
      have hΓ : ∀ x ∈ Γ, RightDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hRightOnly x a
      rcases exists_right_ctx_of_right_only Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_right_tp_of_right_only hA with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Right.Sequent, hΓ', hA'] using hseq

end AutomatedTheoryConstruction
