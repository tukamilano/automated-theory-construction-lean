import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


theorem thm_op_000001_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * z = x * (y * z)) := by
  intro h
  let α := ULift (Bool ⊕ Unit)
  let zero : α := ⟨Sum.inl false⟩
  let one : α := ⟨Sum.inl true⟩
  let two : α := ⟨Sum.inr ()⟩
  let mulBase : Bool ⊕ Unit → Bool ⊕ Unit → Bool ⊕ Unit
    | Sum.inl false, _ => Sum.inl false
    | Sum.inl true, Sum.inl false => Sum.inl false
    | Sum.inl true, Sum.inl true => Sum.inl true
    | Sum.inl true, Sum.inr () => Sum.inl false
    | Sum.inr (), Sum.inl false => Sum.inl false
    | Sum.inr (), Sum.inl true => Sum.inr ()
    | Sum.inr (), Sum.inr () => Sum.inr ()
  let mul : α → α → α := fun a b => ⟨mulBase a.down b.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x with
          | inl b => cases b <;> rfl
          | inr u => cases u; rfl
    · intro x y
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases x with
              | inl b =>
                  cases b <;> cases y with
                  | inl b => cases b <;> rfl
                  | inr u => cases u; rfl
              | inr u =>
                  cases u
                  cases y with
                  | inl b => cases b <;> rfl
                  | inr u => cases u; rfl
    · intro x y z
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases z with
              | up z =>
                  cases x with
                  | inl b =>
                      cases b <;> cases y with
                      | inl b =>
                          cases b <;> cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                      | inr u =>
                          cases u
                          cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                  | inr u =>
                      cases u
                      cases y with
                      | inl b =>
                          cases b <;> cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                      | inr u =>
                          cases u
                          cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
  have h' := h (α := α) (x := two) (y := one) (z := two)
  change two = zero at h'
  injection h' with hbase
  cases hbase

theorem thm_op_000002_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * y = y * x) := by
  intro h
  let α := ULift Bool
  let mul : α → α → α := fun x _ => ⟨x.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y z
      cases x with
      | up x =>
          cases x <;> rfl
  let zero : α := ⟨false⟩
  let one : α := ⟨true⟩
  have h' := h (α := α) (x := zero) (y := one)
  change zero = one at h'
  injection h' with hbase
  cases hbase

theorem thm_op_000003_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, e * x = x ∧ x * e = x) := by
  intro h
  let α := ULift Bool
  let mul : α → α → α := fun x _ => ⟨x.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y z
      cases x with
      | up x =>
          cases x <;> rfl
  obtain ⟨e, he⟩ := h (α := α)
  let zero : α := ⟨false⟩
  let one : α := ⟨true⟩
  have hzero := (he zero).1
  have hone := (he one).1
  change e = zero at hzero
  change e = one at hone
  have h01 : zero = one := by
    exact hzero.symm.trans hone
  injection h01 with hbase
  cases hbase

theorem thm_op_000004_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e) := by
  intro h
  let α := ULift Bool
  let mul : α → α → α := fun x _ => ⟨x.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y z
      cases x with
      | up x =>
          cases x <;> rfl
  obtain ⟨e, he⟩ := h (α := α)
  let zero : α := ⟨false⟩
  let one : α := ⟨true⟩
  have hzero : zero = e := by
    obtain ⟨y, hxy, hyx⟩ := he zero
    change zero = e at hxy
    exact hxy
  have hone : one = e := by
    obtain ⟨y, hxy, hyx⟩ := he one
    change one = e at hxy
    exact hxy
  have h01 : zero = one := by
    exact hzero.trans hone.symm
  injection h01 with hbase
  cases hbase

theorem thm_op_000005_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ join : α → α → α, ∀ x y z : α, x * (join y z) = join (x * y) (x * z)) := by
  intro h
  let α := ULift Bool
  let mul : α → α → α := fun x _ => ⟨x.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y z
      cases x with
      | up x =>
          cases x <;> rfl
  let zero : α := ⟨false⟩
  let one : α := ⟨true⟩
  have h' := h (α := α) (join := fun _ _ => zero) (x := one) (y := zero) (z := zero)
  change one = zero at h'
  injection h' with hbase
  cases hbase

theorem thm_op_000006_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, x * y = x * z → y = z) := by
  intro h
  let α := ULift Bool
  let mul : α → α → α := fun x _ => ⟨x.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y z
      cases x with
      | up x =>
          cases x <;> rfl
  let zero : α := ⟨false⟩
  let one : α := ⟨true⟩
  have hEq : zero * zero = zero * one := by
    rfl
  have h' := h (α := α) (x := zero) (y := zero) (z := one) hEq
  change zero = one at h'
  injection h' with hbase
  cases hbase

theorem thm_op_000007 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x : α, x * x = x := by
  intro α _ x
  simpa [op] using (SemigroupLike01.ax_left_idempotent (α := α) x)

theorem thm_op_000008_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ meet : α → α → α, ∀ x y : α, x * (meet x y) = x) := by
  intro h
  let α := ULift Bool
  let mul : α → α → α := fun x y => ⟨x.down && y.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases x <;> cases y <;> rfl
    · intro x y z
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases z with
              | up z =>
                  cases x <;> cases y <;> cases z <;> rfl
  let zero : α := ⟨false⟩
  let one : α := ⟨true⟩
  have h' := h (α := α) (meet := fun _ _ => zero) (x := one) (y := zero)
  change zero = one at h'
  have hbase : false = true := by
    simpa [zero, one] using congrArg ULift.down h'
  cases hbase

theorem thm_op_000009 : ∃ (α : Type) (_ : SemigroupLike01 α), ∃ x y z : α, (x * y) * z ≠ x * (y * z) := by
  let α := ULift (Bool ⊕ Unit)
  let zero : α := ⟨Sum.inl false⟩
  let one : α := ⟨Sum.inl true⟩
  let two : α := ⟨Sum.inr ()⟩
  let mulBase : Bool ⊕ Unit → Bool ⊕ Unit → Bool ⊕ Unit
    | Sum.inl false, _ => Sum.inl false
    | Sum.inl true, Sum.inl false => Sum.inl false
    | Sum.inl true, Sum.inl true => Sum.inl true
    | Sum.inl true, Sum.inr () => Sum.inl false
    | Sum.inr (), Sum.inl false => Sum.inl false
    | Sum.inr (), Sum.inl true => Sum.inr ()
    | Sum.inr (), Sum.inr () => Sum.inr ()
  let mul : α → α → α := fun a b => ⟨mulBase a.down b.down⟩
  letI : Mul α := ⟨mul⟩
  letI : SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x with
          | inl b => cases b <;> rfl
          | inr u => cases u; rfl
    · intro x y
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases x with
              | inl b =>
                  cases b <;> cases y with
                  | inl b => cases b <;> rfl
                  | inr u => cases u; rfl
              | inr u =>
                  cases u
                  cases y with
                  | inl b => cases b <;> rfl
                  | inr u => cases u; rfl
    · intro x y z
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases z with
              | up z =>
                  cases x with
                  | inl b =>
                      cases b <;> cases y with
                      | inl b =>
                          cases b <;> cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                      | inr u =>
                          cases u
                          cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                  | inr u =>
                      cases u
                      cases y with
                      | inl b =>
                          cases b <;> cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                      | inr u =>
                          cases u
                          cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
  refine ⟨α, (show SemigroupLike01 α from inferInstance), two, one, two, ?_⟩
  intro h
  change two = zero at h
  injection h with hbase
  cases hbase

theorem thm_op_000010 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, (x * y) * x = x * y := by
  intro α _ x y
  have hxyx : (x * y) * x = (x * x) * y := by
    simpa [op] using (SemigroupLike01.ax_middle_swap (α := α) x x y).symm
  have hxx : (x * x) * y = x * y := by
    simpa [op] using congrArg (fun t => t * y) (SemigroupLike01.ax_left_idempotent (α := α) x)
  exact hxyx.trans hxx

theorem thm_op_000011 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, (x * y) * y = x * y := by
  intro α _ x y
  have hswap : ((x * y) * (x * y)) = ((x * (x * y)) * y) := by
    simpa [op] using (SemigroupLike01.ax_middle_swap (α := α) x y (x * y))
  have hdup : ((x * (x * y)) * y) = ((x * y) * y) := by
    simpa [op] using congrArg (fun t => t * y) (SemigroupLike01.ax_right_absorb_duplicate (α := α) x y)
  have hidem : ((x * y) * (x * y)) = x * y := by
    simpa [op] using (SemigroupLike01.ax_left_idempotent (α := α) (x * y))
  exact (hswap.trans hdup).symm.trans hidem

theorem thm_op_000013 : ∃ (α : Type) (_ : SemigroupLike01 α), ¬ ∃ e : α, ∀ x : α, e * x = x := by
  refine ⟨Bool, ?_, ?_⟩
  · refine
      { mul := fun x y => x
        ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      rfl
    · intro x y
      rfl
    · intro x y z
      rfl
  · intro h
    rcases h with ⟨e, he⟩
    have hfalse : e = false := by
      simpa using he false
    have htrue : e = true := by
      simpa using he true
    have : false = true := by
      calc
        false = e := hfalse.symm
        _ = true := htrue
    exact Bool.false_ne_true this

theorem thm_op_000021 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * (x * y) = x * y := by
  intro α _ x y
  simpa [AutomatedTheoryConstruction.op] using
    (AutomatedTheoryConstruction.SemigroupLike01.ax_right_absorb_duplicate (α := α) x y)

theorem thm_op_000026 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, ((x * y) * z) * y = (x * y) * z := by
  intro α _ x y z
  have hswap : ((x * y) * z) * y = ((x * y) * y) * z := by
    simpa [op] using
      (SemigroupLike01.ax_middle_swap (α := α) (x := x * y) (y := z) (z := y))
  rw [hswap, thm_op_000011]

theorem thm_op_000036 : ∀ {α : Type u} [SemigroupLike01 α], ∀ e f : α, (∀ x : α, x * e = e ∧ e * x = e) → (∀ x : α, x * f = f ∧ f * x = f) → e = f := by
  intro α _ e f he hf
  have hfe : f * e = e := (he f).1
  have hff : f * e = f := (hf e).2
  exact hfe.symm.trans hff

theorem thm_op_000037 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, ((x * y) * z) * x = (x * y) * z := by
  intro α _ x y z
  have hswap : ((x * y) * z) * x = ((x * y) * x) * z := by
    simpa [op] using
      (SemigroupLike01.ax_middle_swap (α := α) (x := x * y) (y := z) (z := x))
  rw [hswap, thm_op_000010]

theorem thm_op_000038 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z t : α, (((x * y) * z) * t) = (((x * y) * t) * z) := by
  intro α _ x y z t
  simpa [AutomatedTheoryConstruction.op] using (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (x := x * y) (y := z) (z := t))

theorem thm_op_000039 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (((x * y) * z) * (x * y)) = (x * y) * z := by
  intro α _ x y z
  simpa using (thm_op_000010 (x := x * y) (y := z))

theorem thm_op_000040 : ∀ {α : Type u} [Mul α], ∀ e f : α, (∀ x : α, x * e = e) → (∀ x : α, f * x = f) → e = f := by
  intro α _ e f he hf
  have h1 : f * e = e := he f
  have h2 : f * e = f := hf e
  exact h1.symm.trans h2

theorem thm_op_000041 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ e : α, (∀ x : α, x * e = e) → ∀ x : α, e * x = e := by
  intro α _ e h x
  have hee : e * e = e := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_left_idempotent e)
  have hswap : (e * e) * x = (e * x) * e := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap e e x)
  rw [hee] at hswap
  exact hswap.trans (h (e * x))

theorem thm_op_000042 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * (x * z) = (x * y) * z := by
  intro α _ x y z
  have hswap : (x * y) * (x * z) = (x * (x * z)) * y := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (α := α) (x := x) (y := y) (z := x * z))
  have habsorb : x * (x * z) = x * z := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_right_absorb_duplicate (α := α) x z)
  rw [hswap, habsorb]
  simpa [AutomatedTheoryConstruction.op] using
    (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (α := α) (x := x) (y := z) (z := y))

theorem thm_op_000043 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (((x * y) * z) * x) = (x * y) * z := by
  intro α _ x y z
  have hswap : ((x * y) * z) * x = ((x * y) * x) * z := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (α := α) (x := x * y) (y := z) (z := x))
  calc
    (((x * y) * z) * x) = (((x * y) * x) * z) := hswap
    _ = (x * y) * z := by
      rw [AutomatedTheoryConstruction.thm_op_000010 (x := x) (y := y)]

theorem thm_op_000044_is_false : ¬(∀ {α : Type u} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ x y z : α, ((x * y) * (z * x)) = (x * y) * z) := by
  intro h
  let α := ULift (Bool ⊕ Unit)
  let zero : α := ⟨Sum.inl false⟩
  let one : α := ⟨Sum.inl true⟩
  let two : α := ⟨Sum.inr ()⟩
  let mulBase : Bool ⊕ Unit → Bool ⊕ Unit → Bool ⊕ Unit
    | Sum.inl false, _ => Sum.inl false
    | Sum.inl true, Sum.inl false => Sum.inl false
    | Sum.inl true, Sum.inl true => Sum.inl true
    | Sum.inl true, Sum.inr () => Sum.inl false
    | Sum.inr (), Sum.inl false => Sum.inl false
    | Sum.inr (), Sum.inl true => Sum.inr ()
    | Sum.inr (), Sum.inr () => Sum.inr ()
  let mul : α → α → α := fun a b => ⟨mulBase a.down b.down⟩
  letI : Mul α := ⟨mul⟩
  letI : AutomatedTheoryConstruction.SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x with
          | inl b => cases b <;> rfl
          | inr u => cases u; rfl
    · intro x y
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases x with
              | inl b =>
                  cases b <;> cases y with
                  | inl b => cases b <;> rfl
                  | inr u => cases u; rfl
              | inr u =>
                  cases u
                  cases y with
                  | inl b => cases b <;> rfl
                  | inr u => cases u; rfl
    · intro x y z
      cases x with
      | up x =>
          cases y with
          | up y =>
              cases z with
              | up z =>
                  cases x with
                  | inl b =>
                      cases b <;> cases y with
                      | inl b =>
                          cases b <;> cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                      | inr u =>
                          cases u
                          cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                  | inr u =>
                      cases u
                      cases y with
                      | inl b =>
                          cases b <;> cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
                      | inr u =>
                          cases u
                          cases z with
                          | inl b => cases b <;> rfl
                          | inr u => cases u; rfl
  have h' := h (α := α) (x := two) (y := one) (z := one)
  change zero = two at h'
  injection h' with hbase
  cases hbase

theorem thm_op_000045 : ∀ {α : Type u} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ x y z : α, (((x * y) * z) * z) = (x * y) * z := by
  intro α _ x y z
  simpa using (thm_op_000011 (x * y) z)

theorem thm_op_000046 : ∀ {α : Type u} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ x y z : α, (x * y) * ((x * y) * z) = (x * y) * z := by
  intro α _ x y z
  simpa [AutomatedTheoryConstruction.op] using
    (AutomatedTheoryConstruction.SemigroupLike01.ax_right_absorb_duplicate (x := x * y) (y := z))

theorem thm_op_000047_is_false : ¬(∀ {α : Type u} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ e : α, (∀ x : α, e * x = e) → ∀ x : α, x * e = e) := by
  intro h
  let α := ULift Bool
  let mul : α → α → α := fun x _ => ⟨x.down⟩
  letI : Mul α := ⟨mul⟩
  letI : AutomatedTheoryConstruction.SemigroupLike01 α := by
    refine
      { ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y
      cases x with
      | up x =>
          cases x <;> rfl
    · intro x y z
      cases x with
      | up x =>
          cases x <;> rfl
  let zero : α := ⟨false⟩
  let one : α := ⟨true⟩
  have h' := h (α := α) (e := zero)
  have hzero : ∀ x : α, zero * x = zero := by
    intro x
    cases x with
    | up x =>
        cases x <;> rfl
  have hone := h' hzero one
  change one = zero at hone
  injection hone with hbase
  cases hbase

theorem thm_op_000056 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α] (x y z : α), ((x * y) * z) * (x * y) = (x * y) * z := by
  intro α _ x y z
  simpa using (thm_op_000010 (x * y) z)

theorem thm_op_000057 : ∀ {α : Type u} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ x y z : α, ((x * y) * z) * (x * y) = (x * y) * z := by
  intro α _ x y z
  simpa using (thm_op_000010 (x := x * y) (y := z))

theorem thm_op_000058 : ∃ (α : Type _) (_ : AutomatedTheoryConstruction.SemigroupLike01 α) (e x : α), (∀ y : α, e * y = e) ∧ x * e ≠ e := by
  letI : SemigroupLike01 (ULift Bool) :=
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
  refine ⟨ULift Bool, inferInstance, ULift.up false, ULift.up true, ?_⟩
  constructor
  · intro y
    rfl
  · decide

theorem thm_op_000060 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α] (a b c : α), ((a * b) * c) * a = (a * b) * c := by
  intro α _ a b c
  have hswap : ((a * b) * c) * a = ((a * b) * a) * c := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (α := α) (x := a * b) (y := c) (z := a))
  calc
    (((a * b) * c) * a) = (((a * b) * a) * c) := hswap
    _ = (a * b) * c := by
      rw [AutomatedTheoryConstruction.thm_op_000010 (x := a) (y := b)]

theorem thm_op_000062 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ a b c t : α, t = a * b → ((a * b) * c) * t = (a * b) * c := by
  intro α _ a b c t ht
  rw [ht]
  simpa using (thm_op_000010 (x := a * b) (y := c))

theorem thm_op_000065 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α] (a b c d : α), (((a * b) * c) * d) * a = ((a * b) * c) * d := by
  intro α _ a b c d
  have hswap : ((((a * b) * c) * d) * a) = ((((a * b) * c) * a) * d) := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap
        (α := α) (x := (a * b) * c) (y := d) (z := a))
  have hfix : (((a * b) * c) * a) = ((a * b) * c) := by
    simpa using (AutomatedTheoryConstruction.thm_op_000060 (α := α) (a := a) (b := b) (c := c))
  calc
    ((((a * b) * c) * d) * a) = ((((a * b) * c) * a) * d) := hswap
    _ = (((a * b) * c) * d) := by
      rw [hfix]

theorem thm_op_000066 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ x y z : α, ((x * y) * z) * (x * y) = (x * y) * z := by
  intro α _ x y z
  simpa using (thm_op_000010 (x := x * y) (y := z))

theorem thm_op_000067 : ∀ {α : Type _} [AutomatedTheoryConstruction.SemigroupLike01 α], ∀ a b c d : α, ((((a * b) * c) * d) * (a * b)) = (((a * b) * c) * d) := by
  intro α _ a b c d
  have hswap : ((((a * b) * c) * d) * (a * b)) = ((((a * b) * c) * (a * b)) * d) := by
    simpa [AutomatedTheoryConstruction.op] using
      (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap
        (α := α) (x := (a * b) * c) (y := d) (z := a * b))
  rw [hswap, AutomatedTheoryConstruction.thm_op_000010 (x := a * b) (y := c)]

theorem thm_op_000068 : ∀ (α : Type u), ∃ s : AutomatedTheoryConstruction.SemigroupLike01 α, ∀ x y : α, s.mul x y = x := by
  intro α
  refine ⟨{
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
  }, ?_⟩
  intro x y
  rfl

end AutomatedTheoryConstruction
