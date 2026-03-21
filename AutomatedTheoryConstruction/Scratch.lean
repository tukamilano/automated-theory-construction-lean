import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000063_is_false : ¬(∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α] (e : α), (∀ y : α, e * y = e) → ∀ x : α, x * e = e) := by
  intro h
  letI : AutomatedTheoryConstruction.SemigroupLike01 Bool where
    mul := fun x _ => x
    ax_left_idempotent := by
      intro x
      rfl
    ax_right_absorb_duplicate := by
      intro x y
      rfl
    ax_middle_swap := by
      intro x y z
      rfl
  have hfalse : (true : Bool) = false := by
    simpa using h (α := Bool) (e := false) (by
      intro y
      rfl) true
  cases hfalse

end AutomatedTheoryConstruction
