import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0004_left_right_only

set_option autoImplicit false

namespace AutomatedTheoryConstruction

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
      · simpa [residualAtomicState] using
          (supportClosure_atom_iff_occurs_in_context Γ s)
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

lemma left_handed_support_closure_iff_handed_support_closure :
    ∀ (Γ : List Left.Tp) (A : Left.Tp),
      leftHandedSupportClosure Γ A ↔
        HandedSupportClosure (Left.ctxToProductFree Γ) (Left.Tp.toProductFree A) := by
  intro Γ A
  induction A generalizing Γ with
  | atom s =>
      simp [leftHandedSupportClosure, HandedSupportClosure, Left.Tp.toProductFree]
  | ldiv B C ihB ihC =>
      constructor
      · rintro ⟨hΓ, hC⟩
        refine ⟨?_, ?_⟩
        · cases Γ <;> simp at hΓ ⊢
        · simpa [leftHandedSupportClosure, HandedSupportClosure, Left.ctxToProductFree,
            Left.Tp.toProductFree] using (ihC (Γ := [B] ++ Γ)).1 hC
      · rintro ⟨hΓ, hC⟩
        refine ⟨?_, ?_⟩
        · cases Γ <;> simp at hΓ ⊢
        · have hC' :
            HandedSupportClosure (Left.ctxToProductFree ([B] ++ Γ)) (Left.Tp.toProductFree C) := by
            simpa [Left.ctxToProductFree] using hC
          exact Iff.elim (fun a a_1 => a_1 hC') (ihC ([B] ++ Γ))

lemma right_handed_support_closure_iff_handed_support_closure :
    ∀ (Γ : List Right.Tp) (A : Right.Tp),
      rightHandedSupportClosure Γ A ↔
        HandedSupportClosure (Right.ctxToProductFree Γ) (Right.Tp.toProductFree A) := by
  intro Γ A
  induction A generalizing Γ with
  | atom s =>
      simp [rightHandedSupportClosure, HandedSupportClosure, Right.Tp.toProductFree]
  | rdiv C B ihC ihB =>
      constructor
      · rintro ⟨hΓ, hC⟩
        refine ⟨?_, ?_⟩
        · cases Γ <;> simp at hΓ ⊢
        · simpa [rightHandedSupportClosure, HandedSupportClosure, Right.ctxToProductFree,
            Right.Tp.toProductFree] using (ihC (Γ := Γ ++ [B])).1 hC
      · rintro ⟨hΓ, hC⟩
        refine ⟨?_, ?_⟩
        · cases Γ <;> simp at hΓ ⊢
        · have hC' :
            HandedSupportClosure (Right.ctxToProductFree (Γ ++ [B])) (Right.Tp.toProductFree C) := by
            simpa [Right.ctxToProductFree] using hC
          exact Iff.elim (fun a a_1 => a_1 hC') (ihC (Γ ++ [B]))

lemma leftHandedSupportClosure_iff_sequent :
    ∀ (Γ : List Left.Tp) (A : Left.Tp),
      leftHandedSupportClosure Γ A ↔ Left.Sequent Γ A := by
  intro Γ A
  calc
    leftHandedSupportClosure Γ A ↔
        HandedSupportClosure (Left.ctxToProductFree Γ) (Left.Tp.toProductFree A) :=
      left_handed_support_closure_iff_handed_support_closure Γ A
    _ ↔ Left.ctxToProductFree Γ ⇒ Left.Tp.toProductFree A :=
      thm_handed_support_closure_iff_sequent_000048 (Left.ctxToProductFree Γ) (Left.Tp.toProductFree A)
    _ ↔ Left.Sequent Γ A := by
      simp [Left.Sequent]

lemma rightHandedSupportClosure_iff_sequent :
    ∀ (Γ : List Right.Tp) (A : Right.Tp),
      rightHandedSupportClosure Γ A ↔ Right.Sequent Γ A := by
  intro Γ A
  calc
    rightHandedSupportClosure Γ A ↔
        HandedSupportClosure (Right.ctxToProductFree Γ) (Right.Tp.toProductFree A) :=
      right_handed_support_closure_iff_handed_support_closure Γ A
    _ ↔ Right.ctxToProductFree Γ ⇒ Right.Tp.toProductFree A :=
      thm_handed_support_closure_iff_sequent_000048 (Right.ctxToProductFree Γ) (Right.Tp.toProductFree A)
    _ ↔ Right.Sequent Γ A := by
      simp [Right.Sequent]

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
      HandedSupportClosure Γ A ↔ (Γ ⇒ A) :=
        thm_handed_support_closure_iff_sequent_000048 Γ A
      _ ↔ leftTranslatedSequent Γ A :=
        thm_full_one_sided_conservativity_000042.1 Γ A hΓ hA
      _ ↔ Left.Sequent ΓL AL := by
        simp [leftTranslatedSequent, hΓL, hAL]
      _ ↔ leftHandedSupportClosure ΓL AL :=
        (leftHandedSupportClosure_iff_sequent ΓL AL).symm
      _ ↔ leftTranslatedHandedSupportClosure Γ A := by
        simp [leftTranslatedHandedSupportClosure, hΓL, hAL]
  · intro Γ A hΓ hA
    rcases exists_right_ctx_of_allRightOnly hΓ with ⟨ΓR, hΓR, _⟩
    rcases exists_right_tp_of_isRightOnly hA with ⟨AR, hAR, _⟩
    calc
      HandedSupportClosure Γ A ↔ (Γ ⇒ A) :=
        thm_handed_support_closure_iff_sequent_000048 Γ A
      _ ↔ rightTranslatedSequent Γ A :=
        thm_full_one_sided_conservativity_000042.2 Γ A hΓ hA
      _ ↔ Right.Sequent ΓR AR := by
        simp [rightTranslatedSequent, hΓR, hAR]
      _ ↔ rightHandedSupportClosure ΓR AR :=
        (rightHandedSupportClosure_iff_sequent ΓR AR).symm
      _ ↔ rightTranslatedHandedSupportClosure Γ A := by
        simp [rightTranslatedHandedSupportClosure, hΓR, hAR]


/-- Sequents are exactly residual atomic witnesses. -/
theorem thm_sequent_iff_residual_atomic_witness :
    ∀ (Γ : List Tp) (A : Tp), (Γ ⇒ A) ↔
      ∃ Δ s, residualAtomicState Γ A = some (Δ, s) ∧ AtomicCandidateTree Δ s := by
  intro Γ A
  exact (thm_handed_support_closure_iff_sequent_000048 Γ A).symm.trans
    ((thm_residual_support_normal_form_000050 Γ A).1)


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
      ((thm_sequent_iff_residual_atomic_witness Γ A).mpr
        ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩)
  refine ⟨reconstruct, ?_⟩
  constructor
  · exact Function.injective_of_subsingleton reconstruct
  · intro htree
    have hseq : Γ ⇒ A :=
      (thm_candidate_tree_iff_sequent_000038 Γ A).mp htree
    rcases (thm_sequent_iff_residual_atomic_witness Γ A).mp hseq with
      ⟨Δ, s, hres, hatom⟩
    let x : S := ⟨(Δ, s), ⟨hres, hatom⟩⟩
    exact exists_apply_eq_apply reconstruct x

end AutomatedTheoryConstruction
