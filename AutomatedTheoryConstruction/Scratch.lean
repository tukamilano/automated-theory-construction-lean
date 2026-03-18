import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000006_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, x * y = x * z → y = z) := by
  intro h
  letI : SemigroupLike01 (ULift Bool) :=
    { mul := fun x y => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  have hbad : ((⟨true⟩ : ULift Bool) = ⟨false⟩) := by
    apply h (α := ULift Bool) ⟨true⟩ ⟨true⟩ ⟨false⟩
    rfl
  cases hbad

end AutomatedTheoryConstruction
