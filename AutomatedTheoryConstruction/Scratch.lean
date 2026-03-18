import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000005_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ join : α → α → α, ∀ x y z : α, x * (join y z) = join (x * y) (x * z)) := by
  intro h
  let α : Type u := ULift.{u} (Fin 3)
  let zero : α := ⟨(0 : Fin 3)⟩
  let one : α := ⟨(1 : Fin 3)⟩
  let top : α := ⟨(2 : Fin 3)⟩
  let op3 : α → α → α := fun x y => if x = y then x else top
  let join0 : α → α → α := fun _ _ => zero
  letI : Mul α := ⟨op3⟩
  letI : SemigroupLike01 α :=
    { mul := op3
      ax_left_idempotent := by
        intro x
        change op3 x x = x
        simp [op3]
      ax_right_absorb_duplicate := by
        native_decide
      ax_middle_swap := by
        native_decide }
  have hEq : one * join0 zero one = join0 (one * zero) (one * one) := h (α := α) join0 one zero one
  change op3 one (join0 zero one) = join0 (op3 one zero) (op3 one one) at hEq
  simp [join0, op3, zero, one] at hEq
  have hne : top ≠ zero := by
    decide
  exact hne hEq

end AutomatedTheoryConstruction
