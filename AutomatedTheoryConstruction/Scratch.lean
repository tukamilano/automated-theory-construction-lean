import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000001_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * z = x * (y * z)) := by
  intro h
  let op3 : Fin 3 → Fin 3 → Fin 3 := fun x y => if y = 1 then x else if x = y then x else 0
  letI : SemigroupLike01 (Fin 3) :=
    { mul := op3
      ax_left_idempotent := by
        intro x
        change op3 x x = x
        simp [op3]
      ax_right_absorb_duplicate := by
        intro x y
        change op3 x (op3 x y) = op3 x y
        decide
      ax_middle_swap := by
        intro x y z
        change op3 (op3 x y) z = op3 (op3 x z) y
        decide }
  have hbad : ¬ (((2 : Fin 3) * 1) * 2 = (2 : Fin 3) * (1 * 2)) := by
    change ¬ (op3 (op3 2 1) 2 = op3 2 (op3 1 2))
    decide
  exact hbad (h (α := Fin 3) 2 1 2)

end AutomatedTheoryConstruction
