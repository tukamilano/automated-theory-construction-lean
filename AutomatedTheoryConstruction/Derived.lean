import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


theorem thm_op_000002_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * y = y * x) := by
  intro h
  let T : Type u := ULift Bool
  let s : SemigroupLike01 T :=
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
  letI : SemigroupLike01 T := s
  have hc := h (α := T) (x := ULift.up true) (y := ULift.up false)
  change (ULift.up true : T) = ULift.up false at hc
  have htf : true = false := congrArg ULift.down hc
  cases htf


theorem thm_op_000003_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, e * x = x ∧ x * e = x) := by
  intro h
  let T : Type u := ULift Bool
  let s : SemigroupLike01 T :=
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
  letI : SemigroupLike01 T := s
  obtain ⟨e, he⟩ := h (α := T)
  have htrue : e = ULift.up true := by
    have h := (he (ULift.up true)).1
    change e = ULift.up true at h
    exact h
  have hfalse : e = ULift.up false := by
    have h := (he (ULift.up false)).1
    change e = ULift.up false at h
    exact h
  have htf' : (ULift.up true : T) = ULift.up false := htrue.symm.trans hfalse
  have htf : true = false := congrArg ULift.down htf'
  cases htf


theorem thm_op_000004_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e) := by
  intro h
  let T : Type u := ULift Bool
  let s : SemigroupLike01 T :=
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
  letI : SemigroupLike01 T := s
  obtain ⟨e, he⟩ := h (α := T)
  have htrue : (ULift.up true : T) = e := by
    obtain ⟨y, hy⟩ := he (ULift.up true)
    have hye := hy.1
    change (ULift.up true : T) = e at hye
    exact hye
  have hfalse : (ULift.up false : T) = e := by
    obtain ⟨y, hy⟩ := he (ULift.up false)
    have hye := hy.1
    change (ULift.up false : T) = e at hye
    exact hye
  have htf' : (ULift.up true : T) = ULift.up false := htrue.trans hfalse.symm
  have htf : true = false := congrArg ULift.down htf'
  cases htf


theorem thm_op_000005_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ join : α → α → α, ∀ x y z : α, x * (join y z) = join (x * y) (x * z)) := by
  intro h
  let T : Type u := ULift Bool
  let join : T → T → T := fun _ _ => ULift.up false
  let s : SemigroupLike01 T :=
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
  letI : SemigroupLike01 T := s
  have hc := h (α := T) join (ULift.up true) (ULift.up false) (ULift.up false)
  change (ULift.up true : T) = ULift.up false at hc
  have htf : true = false := congrArg ULift.down hc
  cases htf


theorem thm_op_000006_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, x * y = x * z → y = z) := by
  intro h
  let T : Type u := ULift Bool
  let s : SemigroupLike01 T :=
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
  letI : SemigroupLike01 T := s
  have hc := h (α := T) (x := ULift.up true) (y := ULift.up false) (z := ULift.up true) rfl
  change (ULift.up false : T) = ULift.up true at hc
  have htf : false = true := congrArg ULift.down hc
  cases htf


theorem thm_op_000007 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x : α, x * x = x := by
  intro α _ x
  simpa [AutomatedTheoryConstruction.op] using (SemigroupLike01.ax_left_idempotent (α := α) x)


theorem thm_op_000009 : let mul : Fin 3 → Fin 3 → Fin 3 := fun x y => if x = 0 then 0 else if x = 1 then if y = 1 then 1 else 0 else if y = 0 then 0 else 2; (∀ x : Fin 3, mul x x = x) ∧ (∀ x y : Fin 3, mul x (mul x y) = mul x y) ∧ ∀ x y z : Fin 3, mul (mul x y) z = mul (mul x z) y := by
  native_decide


theorem thm_op_000001_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * z = x * (y * z)) := by
  intro h
  let T := ULift.{u, 0} (Fin 3)
  let mulT : T → T → T := fun x y => ⟨if x.down = 0 then 0 else if x.down = 1 then if y.down = 1 then 1 else 0 else if y.down = 0 then 0 else 2⟩
  letI : Mul T := ⟨mulT⟩
  have h_left : ∀ x : T, op x x = x := by
    decide
  have h_absorb : ∀ x y : T, op x (op x y) = op x y := by
    decide
  have h_swap : ∀ x y z : T, op (op x y) z = op (op x z) y := by
    decide
  let semigroupLikeT : SemigroupLike01 T :=
    { mul := mulT
      ax_left_idempotent := h_left
      ax_right_absorb_duplicate := h_absorb
      ax_middle_swap := h_swap }
  letI : SemigroupLike01 T := semigroupLikeT
  have hAssoc := h (α := T) ⟨2⟩ ⟨1⟩ ⟨2⟩
  have hNotAssoc : ¬ (((⟨2⟩ : T) * ⟨1⟩) * ⟨2⟩ = (⟨2⟩ : T) * (⟨1⟩ * ⟨2⟩)) := by
    decide
  exact hNotAssoc hAssoc


theorem thm_op_000011 : ∀ α : Type u, ∃ s : AutomatedTheoryConstruction.SemigroupLike01 α, letI := s.toMul; ∀ x y : α, x * y = x := by
  intro α
  refine ⟨{
    mul := fun x _ => x
    ax_left_idempotent := ?_
    ax_right_absorb_duplicate := ?_
    ax_middle_swap := ?_
  }, ?_⟩
  · intro x
    rfl
  · intro x y
    rfl
  · intro x y z
    rfl
  · intro x y
    rfl


theorem thm_op_000012 : ∀ α : Type u, (∃ a b : α, a ≠ b) → ∃ s : AutomatedTheoryConstruction.SemigroupLike01 α, letI := s.toMul; ∃ x y : α, x * y ≠ y * x := by
  intro α hne
  rcases hne with ⟨a, b, hab⟩
  let s : SemigroupLike01 α :=
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
  refine ⟨s, ?_⟩
  letI : Mul α := s.toMul
  refine ⟨a, b, ?_⟩
  change a ≠ b
  exact hab


theorem thm_op_000013 : ∃ (α : Type) (_ : SemigroupLike01 α), ¬ ∃ e : α, ∀ x : α, e * x = x ∧ x * e = x := by
  let T : Type := ULift Bool
  let s : SemigroupLike01 T :=
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
  refine ⟨T, s, ?_⟩
  letI : SemigroupLike01 T := s
  intro h
  rcases h with ⟨e, he⟩
  have htrue : e = ULift.up true := by
    have h := (he (ULift.up true)).1
    change e = ULift.up true at h
    exact h
  have hfalse : e = ULift.up false := by
    have h := (he (ULift.up false)).1
    change e = ULift.up false at h
    exact h
  have htf : true = false := congrArg ULift.down (htrue.symm.trans hfalse)
  cases htf


theorem thm_op_000015 : ∃ α : Type u, ∃ _ : AutomatedTheoryConstruction.SemigroupLike01 α, ∃ a b : α, a ≠ b ∧ ∀ x y : α, x * y = x := by
  let α : Type u := ULift.{u} Bool
  let a : α := ULift.up true
  let b : α := ULift.up false
  let s : AutomatedTheoryConstruction.SemigroupLike01 α := {
    mul := fun x _ => x
    ax_left_idempotent := by
      intro x
      rfl
    ax_right_absorb_duplicate := by
      intro x y
      rfl
    ax_middle_swap := by
      intro x y z
      rfl
  }
  letI : AutomatedTheoryConstruction.SemigroupLike01 α := s
  refine ⟨α, s, a, b, ?_⟩
  constructor
  · show (ULift.up true : α) ≠ ULift.up false
    decide
  · intro x y
    rfl


theorem thm_op_000016 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, (x * y) * x = x * y := by
  intro α _ x y
  calc
    (x * y) * x = (x * x) * y := by
      simpa [AutomatedTheoryConstruction.op] using (SemigroupLike01.ax_middle_swap (α := α) x y x)
    _ = x * y := by
      rw [show x * x = x by
        simpa [AutomatedTheoryConstruction.op] using (SemigroupLike01.ax_left_idempotent (α := α) x)]


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
