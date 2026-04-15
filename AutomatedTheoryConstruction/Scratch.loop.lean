import Mathlib
import Mathlib
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

inductive Op000071α where
  | t | c | a | b
  deriving DecidableEq

open Op000071α

def Op000071Le : Op000071α → Op000071α → Prop
  | t, t => True
  | t, c => True
  | c, c => True
  | a, a => True
  | a, c => True
  | b, b => True
  | _, _ => False

instance decOp000071Le : DecidableRel Op000071Le := by
  intro x y
  cases x <;> cases y <;> unfold Op000071Le <;> infer_instance

instance : Top Op000071α where
  top := t

instance : Bot Op000071α where
  bot := b

instance : LE Op000071α where
  le := Op000071Le

instance : DecidableRel ((· ≤ ·) : Op000071α → Op000071α → Prop) := decOp000071Le

instance : Preorder Op000071α where
  le := Op000071Le
  le_refl x := by
    cases x <;> decide
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;> cases hxy <;> cases hyz <;> decide

instance op000071ACR : ACR (ULift Op000071α) where
  toTop := ULift.instTop
  toBot := ULift.instBot
  toPreorder := ULift.instPreorder

instance op000071Prov : ACR.Prov (ULift Op000071α) where
  prov _ := ⟨c⟩

instance op000071Reft : ACR.Reft (ULift Op000071α) where
  reft x :=
    match x.down with
    | t => ⟨c⟩
    | c => ⟨a⟩
    | a => ⟨a⟩
    | b => ⟨c⟩

instance op000071APS : ACR.APS (ULift Op000071α) where
  prov_mono := by
    intro x y h
    trivial
  reft_anti_mono := by
    intro x y h
    cases x using ULift.casesOn with
    | _ x =>
      cases y using ULift.casesOn with
      | _ y =>
        cases x <;> cases y <;> trivial
  top_le_reft_bot := by
    trivial
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hprov hreft
    cases x using ULift.casesOn with
    | _ x =>
      cases y using ULift.casesOn with
      | _ y =>
        cases x <;> cases y <;> cases hprov <;> cases hreft <;> trivial
  reft_le_prov_reft := by
    intro x
    cases x using ULift.casesOn with
    | _ x =>
      cases x <;> trivial

theorem thm_consistent_godel_non_equiv_000071 : ∃ (α : Type*) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α), ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) ∧ ¬ (⊠⊠(⊤ : α) ≐ ⊠⊤) := by
  refine ⟨ULift Op000071α, op000071ACR, op000071Prov, op000071Reft, op000071APS, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    change False at h
    exact h
  · refine ⟨⟨⟨a⟩, ?_⟩⟩
    constructor <;> trivial
  · intro h
    have hca : ((⟨c⟩ : ULift Op000071α) ≤ ⟨a⟩) := by
      simpa using h.2
    change False at hca
    exact hca

end AutomatedTheoryConstruction
