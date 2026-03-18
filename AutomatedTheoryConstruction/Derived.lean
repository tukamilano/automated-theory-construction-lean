import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.


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


theorem thm_op_000006_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, x * y = x * z → y = z) := by
  intro h
  let α : Type u := ULift.{u} (Fin 3)
  let zero : α := ⟨(0 : Fin 3)⟩
  let one : α := ⟨(1 : Fin 3)⟩
  let top : α := ⟨(2 : Fin 3)⟩
  let op3 : α → α → α := fun x y => if x = y then x else top
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
  have hEq : top * zero = top * one := by
    change op3 top zero = op3 top one
    simp [op3, top, zero, one]
  have hContra : zero = one := h (α := α) top zero one hEq
  have hne : zero ≠ one := by
    decide
  exact hne hContra


theorem thm_op_000007 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x : α, x * x = x := by
  intro α _ x
  simpa [op] using SemigroupLike01.ax_left_idempotent (α := α) x


theorem thm_op_000009 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, (x * y) * x = x * y := by
  intro α _ x y
  have hswap : (x * y) * x = (x * x) * y := by
    simpa [op] using SemigroupLike01.ax_middle_swap (α := α) x y x
  have hxx : x * x = x := by
    simpa [op] using SemigroupLike01.ax_left_idempotent (α := α) x
  simpa [hxx] using hswap


theorem thm_op_000011 : ∃ α : Type u, ∃ _ : SemigroupLike01 α, ¬ Subsingleton α := by
  let α : Type u := ULift.{u} Bool
  letI : SemigroupLike01 α :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  refine ⟨α, inferInstance, ?_⟩
  intro h
  have hEq : (ULift.up true : α) = (ULift.up false : α) := Subsingleton.elim _ _
  have htf : (true : Bool) ≠ false := by
    decide
  exact htf (congrArg ULift.down hEq)


theorem thm_op_000012 : ∃ α : Type u, ∃ _ : SemigroupLike01 α, ∃ x y z : α, x * y = x * z ∧ y ≠ z := by
  let α : Type u := ULift.{u} Bool
  letI : SemigroupLike01 α :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  refine ⟨α, inferInstance, ULift.up true, ULift.up true, ULift.up false, ?_⟩
  constructor
  · rfl
  · intro h
    have htf : (true : Bool) ≠ false := by
      decide
    exact htf (congrArg ULift.down h)


theorem thm_op_000013 : ∃ α : Type u, ∃ _ : SemigroupLike01 α, ∃ x y : α, x * y = x ∧ x ≠ y := by
  let α : Type u := ULift.{u} Bool
  letI : SemigroupLike01 α :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  refine ⟨α, inferInstance, ULift.up true, ULift.up false, ?_⟩
  constructor
  · rfl
  · intro h
    have htf : (true : Bool) ≠ false := by
      decide
    exact htf (congrArg ULift.down h)


theorem thm_op_000014 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * (x * z) = (x * y) * z := by
  intro α _ x y z
  have h1 : (x * y) * (x * z) = (x * (x * z)) * y := by
    simpa [op] using SemigroupLike01.ax_middle_swap (α := α) x y (x * z)
  have h2 : x * (x * z) = x * z := by
    simpa [op] using SemigroupLike01.ax_right_absorb_duplicate (α := α) x z
  have h3 : (x * z) * y = (x * y) * z := by
    simpa [op] using SemigroupLike01.ax_middle_swap (α := α) x z y
  calc
    (x * y) * (x * z) = (x * (x * z)) * y := h1
    _ = (x * z) * y := by rw [h2]
    _ = (x * y) * z := h3


theorem thm_op_000015 : ∀ {α : Type u} [Nontrivial α], ∃ _ : SemigroupLike01 α, ¬ Subsingleton α := by
  intro α _
  letI : SemigroupLike01 α :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  refine ⟨inferInstance, ?_⟩
  exact not_subsingleton α


theorem thm_op_000016 : ∀ α : Type u, ∃ _ : SemigroupLike01 α, ∀ x y : α, x * y = x := by
  intro α
  letI : SemigroupLike01 α :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  refine ⟨inferInstance, ?_⟩
  intro x y
  rfl

end AutomatedTheoryConstruction
