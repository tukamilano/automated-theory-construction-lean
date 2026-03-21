import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


theorem thm_op_000002_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * y = y * x) := by
  intro h
  let T : Type u := ULift Bool
  let s : SemigroupLike01 T :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  letI : SemigroupLike01 T := s
  have hc := h (α := T) (x := ULift.up true) (y := ULift.up false)
  change (ULift.up true : T) = ULift.up false at hc
  have htf : true = false := congrArg ULift.down hc
  cases htf


theorem thm_op_000003_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, e * x = x ∧ x * e = x) := by
  intro h
  let T : Type u := ULift Bool
  let s : SemigroupLike01 T :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  letI : SemigroupLike01 T := s
  obtain ⟨e, he⟩ := h (α := T)
  have htrue : e = ULift.up true := by
    have h := (he (ULift.up true)).1
    change e = ULift.up true at h
    exact h
  have hfalse : e = ULift.up false := by
    have h := (he (ULift.up false)).1
    change e = ULift.up false at h
    exact h
  have htf' : (ULift.up true : T) = ULift.up false := htrue.symm.trans hfalse
  have htf : true = false := congrArg ULift.down htf'
  cases htf


theorem thm_op_000004_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e) := by
  intro h
  let T : Type u := ULift Bool
  let s : SemigroupLike01 T :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  letI : SemigroupLike01 T := s
  obtain ⟨e, he⟩ := h (α := T)
  have htrue : (ULift.up true : T) = e := by
    obtain ⟨y, hy⟩ := he (ULift.up true)
    have hye := hy.1
    change (ULift.up true : T) = e at hye
    exact hye
  have hfalse : (ULift.up false : T) = e := by
    obtain ⟨y, hy⟩ := he (ULift.up false)
    have hye := hy.1
    change (ULift.up false : T) = e at hye
    exact hye
  have htf' : (ULift.up true : T) = ULift.up false := htrue.trans hfalse.symm
  have htf : true = false := congrArg ULift.down htf'
  cases htf


theorem thm_op_000005_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ join : α → α → α, ∀ x y z : α, x * (join y z) = join (x * y) (x * z)) := by
  intro h
  let T : Type u := ULift Bool
  let join : T → T → T := fun _ _ => ULift.up false
  let s : SemigroupLike01 T :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  letI : SemigroupLike01 T := s
  have hc := h (α := T) join (ULift.up true) (ULift.up false) (ULift.up false)
  change (ULift.up true : T) = ULift.up false at hc
  have htf : true = false := congrArg ULift.down hc
  cases htf

end AutomatedTheoryConstruction
