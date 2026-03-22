import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000015_is_false : ¬(For every finite type α, every SemigroupLike01 structure on α satisfies ∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e.) := by
  intro h
  let T : Type u := ULift.{u} Bool
  let t : T := ULift.up true
  let f : T := ULift.up false
  let semigroupLikeT : SemigroupLike01 T :=
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
  letI : SemigroupLike01 T := semigroupLikeT
  letI : Fintype T := inferInstance
  obtain ⟨e, he⟩ := h (α := T)
  obtain ⟨yt, ht, _⟩ := he t
  obtain ⟨yf, hf, _⟩ := he f
  have hte : t = e := by
    simpa [t] using ht
  have hfe : f = e := by
    simpa [f] using hf
  have htf : t = f := hte.trans hfe.symm
  have hbool : true = false := by
    simpa [t, f] using congrArg ULift.down htf
  cases hbool

end AutomatedTheoryConstruction
