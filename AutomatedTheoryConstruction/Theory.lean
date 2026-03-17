namespace AutomatedTheoryConstruction

universe u

class HasOp (α : Type u) where
  op : α -> α -> α

def op {α : Type u} [HasOp α] (x y : α) : α :=
  HasOp.op x y

end AutomatedTheoryConstruction
