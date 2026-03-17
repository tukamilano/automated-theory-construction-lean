namespace AutomatedTheoryConstruction

universe u

class HasOp (α : Type u) where
  op : α -> α -> α

def op {α : Type u} [HasOp α] (x y : α) : α :=
  HasOp.op x y

class SemigroupLike01 (α : Type u) extends HasOp α where
  ax_left_idempotent : ∀ x : α, op x x = x
  ax_right_absorb_duplicate : ∀ x y : α, op x (op x y) = op x y
  ax_middle_swap : ∀ x y z : α, op (op x y) z = op (op x z) y

end AutomatedTheoryConstruction
