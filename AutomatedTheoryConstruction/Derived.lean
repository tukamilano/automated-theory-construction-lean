import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Product

set_option autoImplicit false

namespace AutomatedTheoryConstruction

-- Newly verified staging theorems are appended here by scripts/append_derived.py.
-- Promote reviewed results into Product.lean and then reset this file.


instance instACRULiftNat : ACR (ULift Nat) where
  toPreorder := inferInstance
  top := ⟨0⟩
  bot := ⟨0⟩

instance instProvULiftNat : ACR.Prov (ULift Nat) where
  prov n := ⟨n.1 + 1⟩

instance instReftULiftNat : ACR.Reft (ULift Nat) where
  reft _ := ⟨0⟩

instance instAPSULiftNat : ACR.APS (ULift Nat) where
  prov_mono := by
    intro x y h
    change x.1 + 1 ≤ y.1 + 1
    exact Nat.succ_le_succ h
  reft_anti_mono := by
    intro x y h
    change (0 : Nat) ≤ 0
    exact le_rfl
  top_le_reft_bot := by
    change (0 : Nat) ≤ 0
    exact le_rfl
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hprov hreft
    change x.1 ≤ (0 : Nat) at hreft ⊢
    exact hreft
  reft_le_prov_reft := by
    intro x
    change (0 : Nat) ≤ 0 + 1
    exact Nat.zero_le _

/-- Even reft parity gives Henkin fixed points. -/
theorem thm_even_reft_henkin_fixpoint_000009_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (d : Delta), Even (Delta.countReft d) → (Nonempty {x : α // x ≐ Delta.act d x} ↔ Nonempty (ACR.HenkinFixpoint α))) := by
  intro h
  letI : ACR (ULift Nat) := instACRULiftNat
  letI : ACR.Prov (ULift Nat) := instProvULiftNat
  letI : ACR.Reft (ULift Nat) := instReftULiftNat
  letI : ACR.APS (ULift Nat) := instAPSULiftNat
  let d : Delta := []
  have hEven : Even (Delta.countReft d) := by
    decide
  have hiff : Nonempty {x : ULift Nat // x ≐ Delta.act d x} ↔ Nonempty (ACR.HenkinFixpoint (ULift Nat)) := by
    simpa using (h (α := ULift Nat) d hEven)
  have hfixed : Nonempty {x : ULift Nat // x ≐ Delta.act d x} := by
    refine ⟨⟨⟨0⟩, ?_⟩⟩
    simp [d, Delta.act, ACR.Equivalent]
  have hhenkin : Nonempty (ACR.HenkinFixpoint (ULift Nat)) := hiff.mp hfixed
  rcases hhenkin with ⟨⟨n, hn⟩⟩
  have hs := hn.2
  change n.1 + 1 ≤ n.1 at hs
  exact Nat.not_succ_le_self n.1 hs

end AutomatedTheoryConstruction
