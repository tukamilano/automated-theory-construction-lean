import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000001_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * z = x * (y * z)) := by
  intro h
  let mul : Fin 3 → Fin 3 → Fin 3 := fun a b =>
    if a = 0 then 0
    else if a = 1 then
      if b = 1 then 1 else 0
    else
      if b = 0 then 0 else 2
  let _ : SemigroupLike01 (Fin 3) :=
    { mul := mul
      ax_left_idempotent := by native_decide
      ax_right_absorb_duplicate := by native_decide
      ax_middle_swap := by native_decide }
  have h' := h (α := Fin 3) (x := (2 : Fin 3)) (y := (1 : Fin 3)) (z := (2 : Fin 3))
  have hfalse : ¬ ((2 : Fin 3) * 1) * 2 = (2 : Fin 3) * (1 * 2) := by
    native_decide
  exact hfalse h'

end AutomatedTheoryConstruction
