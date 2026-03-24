import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_consistent_reft_top_not_box_equiv_000028 : ∃ (α : Type _), ∃ (_ : ACR α), ∃ (_ : ACR.Prov α), ∃ (_ : ACR.Reft α), ∃ (_ : ACR.APS α), ∃ (_ : ACR.C5 α), ACR.Consistent α ∧ (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ∧ ¬ (⊠(⊤ : α) ≐ □(⊠(⊤ : α))) := by
  let α : Type := Fin 3
  letI : Top α := ⟨2⟩
  letI : Bot α := ⟨0⟩
  letI : Preorder α := {
    le := fun x y => x.1 ≤ y.1
    le_refl := by
      intro x
      exact Nat.le_refl x.1
    le_trans := by
      intro a b c hab hbc
      exact Nat.le_trans hab hbc
  }
  let acr : ACR α := {
    toTop := inferInstance
    toBot := inferInstance
    toPreorder := inferInstance
  }
  letI : ACR α := acr
  let prov : ACR.Prov α := ⟨fun x => if x = 0 then 1 else 2⟩
  let reft : ACR.Reft α := ⟨fun x => if x = 0 then 2 else 1⟩
  letI : ACR.Prov α := prov
  letI : ACR.Reft α := reft
  let aps : ACR.APS α := {
    prov_mono := by decide
    reft_anti_mono := by decide
    top_le_reft_bot := by decide
    le_reft_top_of_le_prov_of_le_reft := by decide
    reft_le_prov_reft := by decide
  }
  letI : ACR.APS α := aps
  let c5 : ACR.C5 α := {
    le_top := by decide
  }
  refine ⟨α, acr, prov, reft, aps, c5, ?_⟩
  constructor
  · decide
  constructor
  · constructor <;> decide
  · decide

end AutomatedTheoryConstruction
