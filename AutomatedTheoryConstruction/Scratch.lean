import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000043 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (((x * y) * z) * x) = (x * y) * z := by
  intro α _ x y z
  simpa using (thm_op_000037 (x := x) (y := y) (z := z))

end AutomatedTheoryConstruction
