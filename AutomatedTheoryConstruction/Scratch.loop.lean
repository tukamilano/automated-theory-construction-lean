import Mathlib
import AutomatedTheoryConstruction.Derived


set_option autoImplicit false

namespace AutomatedTheoryConstruction

instance op000017ACR : ACR Nat where
  toPreorder := inferInstance
  top := 0
  bot := 0

instance op000017Prov : ACR.Prov Nat where
  prov n := n + 1

instance op000017Reft : ACR.Reft Nat where
  reft _ := 0

instance op000017APS : ACR.APS Nat where
  prov_mono := by
    intro x y h
    exact Nat.succ_le_succ h
  reft_anti_mono := by
    intro x y h
    exact le_rfl
  top_le_reft_bot := by
    exact le_rfl
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hprov hreft
    simpa using hreft
  reft_le_prov_reft := by
    intro x
    exact Nat.zero_le _

theorem thm_even_delta_fixpoint_no_henkin_000017 : ∃ (α : Type*) (a : ACR α) (p : @ACR.Prov α a) (r : @ACR.Reft α a) (aps : @ACR.APS α a p r) (d : Delta), d ≠ [] ∧ Even (Delta.countReft d) ∧ Nonempty {x : α // @ACR.Equivalent α a x (@Delta.act α a p r d x)} ∧ ¬ Nonempty (@ACR.HenkinFixpoint α a p) := by
  refine ⟨_, op000017ACR, op000017Prov, op000017Reft, op000017APS, [Delta.reft, Delta.reft], ?_, ?_, ?_, ?_⟩
  · simp
  · native_decide
  · refine ⟨⟨0, ?_⟩⟩
    change ((0 : Nat) ≤ 0) ∧ ((0 : Nat) ≤ 0)
    constructor <;> exact le_rfl
  · rintro ⟨⟨n, hn⟩⟩
    have hs := hn.2
    change n + 1 ≤ n at hs
    exact Nat.not_succ_le_self n hs

end AutomatedTheoryConstruction
