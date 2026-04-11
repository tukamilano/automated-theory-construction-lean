import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0002_support_ok_atom

set_option autoImplicit false

namespace AutomatedTheoryConstruction

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
      have hx : isLeftOnly x := hΓ x List.mem_cons_self
      have hxs : ∀ y ∈ xs, isLeftOnly y := by
        intro y hy
        exact List.forall_mem_of_forall_mem_cons hΓ y hy
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
      have hx : isRightOnly x := hΓ x List.mem_cons_self
      have hxs : ∀ y ∈ xs, isRightOnly y := by
        intro y hy
        exact List.forall_mem_of_forall_mem_cons hΓ y hy
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
  · exact Function.injective_of_subsingleton reconstruct
  · intro htree
    have hseq : Γ ⇒ A :=
      (thm_candidate_tree_iff_sequent_000038 Γ A).mp htree
    have hhand : HandedSupportClosure Γ A :=
      (thm_handed_support_closure_iff_sequent_000048 Γ A).mpr hseq
    rcases ((thm_residual_support_normal_form_000050 Γ A).1).mp hhand with
      ⟨Δ, s, hres, hatom⟩
    let x : S := ⟨(Δ, s), ⟨hres, hatom⟩⟩
    exact exists_apply_eq_apply reconstruct x

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
            exact AtomicCandidateTree.step_rdiv (Γ, s).1 L Δ Λ A B (Γ, s).2 hc harg ih
        | ldiv Γ Γ₁ Δ R A B s hc harg =>
            exact AtomicCandidateTree.step_ldiv (Γ, s).1 Γ₁ Δ R A B (Γ, s).2 hc harg ih
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
          exact (String.append_left_inj s).mp (congrFun (congrArg HAppend.hAppend hs) s))
        (SupportClosure.self (#"p")))
  have hhand : HandedSupportClosure [bad] (#"p") :=
    (h.1 [bad] (#"p") hleft hA).mp hsc
  have hseq : [bad] ⇒ #"p" :=
    (thm_handed_support_closure_iff_sequent_000048 [bad] (#"p")).mp hhand
  have heq : bad = #"p" :=
    (thm_singleton_atomic_sequent_iff_000011 (A := bad) (s := "p")).mp hseq
  simp [bad] at heq

end AutomatedTheoryConstruction
