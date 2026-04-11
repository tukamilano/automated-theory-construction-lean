import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

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

end AutomatedTheoryConstruction
