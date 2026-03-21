import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000064_is_false : ¬((∃ (_ : AutomatedTheoryConstruction.SemigroupLike01 Bool), (∀ x y : Bool, x * y = x) ∧ ∃ e : Bool, (∀ y : Bool, e * y = e) ∧ ¬ ∀ x : Bool, x * e = e) ∧ ∀ (α : Type _) (_ : Fintype α) (_ : AutomatedTheoryConstruction.SemigroupLike01 α), (∃ e : α, (∀ y : α, e * y = e) ∧ ¬ ∀ x : α, x * e = e) → 2 ≤ Fintype.card α) := by
  intro h
  rcases h with ⟨hBool, _⟩
  rcases hBool with ⟨_, hproj, _⟩
  have htf : true * false = true := hproj true false
  change false = true at htf
  cases htf

end AutomatedTheoryConstruction
