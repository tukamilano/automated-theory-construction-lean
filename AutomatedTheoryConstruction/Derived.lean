import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems and AI-friendly aliases are appended here by scripts/append_derived.py.


theorem thm_op_000002_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * y = y * x) := by
  intro h
  letI : SemigroupLike01 (ULift Bool) :=
    { mul := fun x y => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  have hcomm : ((⟨true⟩ : ULift Bool) = ⟨false⟩) := h (α := ULift Bool) ⟨true⟩ ⟨false⟩
  cases hcomm

theorem not_mul_comm_op_000002 : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * y = y * x) := thm_op_000002_is_false


theorem thm_op_000003_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, e * x = x ∧ x * e = x) := by
  intro h
  letI : SemigroupLike01 (ULift Bool) :=
    { mul := fun x y => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  obtain ⟨e, he⟩ := h (α := ULift Bool)
  have htrue := (he ⟨true⟩).1
  change e = (⟨true⟩ : ULift Bool) at htrue
  have hfalse := (he ⟨false⟩).1
  change e = (⟨false⟩ : ULift Bool) at hfalse
  have htf : ((⟨true⟩ : ULift Bool) = ⟨false⟩) := by
    calc
      (⟨true⟩ : ULift Bool) = e := htrue.symm
      _ = ⟨false⟩ := hfalse
  cases htf

theorem not_exists_two_sided_identity_op_000003 : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, e * x = x ∧ x * e = x) := thm_op_000003_is_false


theorem thm_op_000004_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e) := by
  intro h
  letI : SemigroupLike01 (ULift Bool) :=
    { mul := fun x y => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  obtain ⟨e, he⟩ := h (α := ULift Bool)
  obtain ⟨_, htrue, _⟩ := he ⟨true⟩
  change ((⟨true⟩ : ULift Bool) = e) at htrue
  obtain ⟨_, hfalse, _⟩ := he ⟨false⟩
  change ((⟨false⟩ : ULift Bool) = e) at hfalse
  have htf : ((⟨true⟩ : ULift Bool) = ⟨false⟩) := by
    calc
      (⟨true⟩ : ULift Bool) = e := htrue
      _ = ⟨false⟩ := hfalse.symm
  cases htf

theorem not_exists_two_sided_sink_op_000004 : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e) := thm_op_000004_is_false

end AutomatedTheoryConstruction
