import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000056 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α] (x y z : α), ((x * y) * z) * (x * y) = (x * y) * z := by
  intro α _ x y z
  simpa using (thm_op_000010 (x * y) z)

end AutomatedTheoryConstruction
