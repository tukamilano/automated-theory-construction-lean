import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000017 : ∀ {α : Type u} [Mul α] (join : α → α → α), (∀ x y : α, x * y = x) → ((∀ x y z : α, x * (join y z) = join (x * y) (x * z)) ↔ ∀ x : α, join x x = x) := by
  intro α _ join hmul
  constructor
  · intro h x
    specialize h x x x
    rw [hmul x (join x x), hmul x x] at h
    exact h.symm
  · intro h x y z
    rw [hmul x (join y z), hmul x y, hmul x z, h x]

end AutomatedTheoryConstruction
