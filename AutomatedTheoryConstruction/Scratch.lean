import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000068 : ∀ (α : Type u), ∃ s : AutomatedTheoryConstruction.SemigroupLike01 α, ∀ x y : α, s.mul x y = x := by
  intro α
  refine ⟨{
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
  }, ?_⟩
  intro x y
  rfl

end AutomatedTheoryConstruction
