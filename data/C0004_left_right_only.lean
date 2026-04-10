import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0003_candidate_tree_support

set_option autoImplicit false

namespace AutomatedTheoryConstruction

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
      have hx : isLeftOnly x := hΓ x (by
        simp)
      have hxs : ∀ y ∈ xs, isLeftOnly y := by
        exact fun y a => List.forall_mem_of_forall_mem_cons hΓ y a
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
      have hx : isRightOnly x := hΓ x (by
        simp)
      have hxs : ∀ y ∈ xs, isRightOnly y := by
        exact fun y a => List.forall_mem_of_forall_mem_cons hΓ y a
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

end AutomatedTheoryConstruction
