import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000021 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * (x * z) = (x * y) * z := by
  intro α _ x y z
  calc
    (x * y) * (x * z) = (x * (x * z)) * y := by
      simpa [AutomatedTheoryConstruction.op] using
        (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (α := α) x y (x * z))
    _ = (x * z) * y := by
      simpa [AutomatedTheoryConstruction.op] using
        congrArg (fun t => t * y)
          (AutomatedTheoryConstruction.SemigroupLike01.ax_right_absorb_duplicate (α := α) x z)
    _ = (x * y) * z := by
      simpa [AutomatedTheoryConstruction.op] using
        (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (α := α) x z y)

end AutomatedTheoryConstruction
