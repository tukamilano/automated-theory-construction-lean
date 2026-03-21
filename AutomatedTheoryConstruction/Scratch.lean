import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000006_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, x * y = x * z → y = z) := by
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
  have hc := h (α := T) (x := ULift.up true) (y := ULift.up false) (z := ULift.up true) rfl
  change (ULift.up false : T) = ULift.up true at hc
  have htf : false = true := congrArg ULift.down hc
  cases htf

end AutomatedTheoryConstruction
