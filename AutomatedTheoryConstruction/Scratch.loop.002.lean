import Mathlib
import AutomatedTheoryConstruction.Derived


set_option autoImplicit false

namespace AutomatedTheoryConstruction

inductive CounterBool where
  | ff
  | tt
  deriving DecidableEq, Repr

instance : ACR CounterBool where
  top := CounterBool.tt
  bot := CounterBool.ff
  le x y := x = CounterBool.ff ∨ y = CounterBool.tt
  refl := by
    intro x
    cases x <;> simp
  trans := by
    intro a b c hab hbc
    rcases hab with ha | hb
    · exact Or.inl ha
    · rcases hbc with hb' | hc
      · cases hb.trans hb'
      · exact Or.inr hc

instance : ACR.Prov CounterBool where
  prov _ := CounterBool.tt

instance : ACR.Reft CounterBool where
  reft
    | CounterBool.ff => CounterBool.tt
    | CounterBool.tt => CounterBool.ff

instance : ACR.APS CounterBool where
  prov_mono := by
    intro x y h
    simp [ACR.Prov.prov]
  reft_anti_mono := by
    intro x y h
    cases x <;> cases y <;> simp [ACR.Reft.reft] at h ⊢
  top_le_reft_bot := by
    simp [ACR.Reft.reft]
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hx hy
    cases x <;> cases y <;> simp [ACR.Prov.prov, ACR.Reft.reft] at hx hy ⊢
  reft_le_prov_reft := by
    intro x
    cases x <;> simp [ACR.Prov.prov, ACR.Reft.reft]

theorem thm_odd_reft_fixedpoint_godel_000008_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (d : Delta), Odd (Delta.countReft d) → (Nonempty {x : α // x ≐ Delta.act d x} ↔ Nonempty (ACR.GödelFixpoint α))) := by
  by
    intro h
    let d : Delta := [Delta.reft, Delta.box]
    have hodd : Odd (Delta.countReft d) := by
      native_decide
    have hiff := h (α := CounterBool) d hodd
    have hleft : Nonempty {x : CounterBool // x ≐ Delta.act d x} := by
      refine ⟨⟨CounterBool.tt, ?_⟩⟩
      constructor <;> simp [d, Delta.act, Delta.actSymbol, ACR.Equivalent, ACR.Prov.prov, ACR.Reft.reft]
    have hright : ¬ Nonempty (ACR.GödelFixpoint CounterBool) := by
      rintro ⟨⟨g, hg⟩⟩
      cases g <;> simp [ACR.GödelFixpoint, ACR.Equivalent, ACR.Reft.reft] at hg
    exact hright (hiff.mp hleft)

end AutomatedTheoryConstruction
