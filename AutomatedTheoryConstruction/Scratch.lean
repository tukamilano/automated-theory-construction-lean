import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000070 : ∀ {α : Type _} [Fintype α] [AutomatedTheoryConstruction.SemigroupLike01 α] (e : α), (∀ y : α, e * y = e) → (¬ ∀ x : α, x * e = e) → Nontrivial α := by
  intro α _ _ e he hne
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  apply hne
  intro x
  have hx : x = e := hsub.elim x e
  rw [hx]
  exact he e

end AutomatedTheoryConstruction
