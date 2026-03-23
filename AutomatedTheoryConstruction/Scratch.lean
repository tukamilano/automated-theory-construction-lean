import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000080_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → □(⊠(⊤ : α)) ≤ ⊠(⊤ : α)) := by
  intro h
  let prov : Fin 3 → Fin 3 := fun x => if x = 0 then 0 else 2
  let reft : Fin 3 → Fin 3 := fun x => if x = 0 then 2 else 1
  let acrInst : ACR (Fin 3) :=
    { toTop := inferInstance
      toBot := inferInstance
      toLE := inferInstance
      toLT := inferInstance
      le_refl := by
        intro a
        exact Preorder.le_refl a
      le_trans := by
        intro a b c hab hbc
        exact Preorder.le_trans _ _ _ hab hbc
      lt_iff_le_not_ge := by
        intro a b
        exact Preorder.lt_iff_le_not_ge _ _ }
  letI : ACR (Fin 3) := acrInst
  let provInst : ACR.Prov (Fin 3) := ⟨prov⟩
  letI : ACR.Prov (Fin 3) := provInst
  let reftInst : ACR.Reft (Fin 3) := ⟨reft⟩
  letI : ACR.Reft (Fin 3) := reftInst
  let apsInst : ACR.APS (Fin 3) :=
    { prov_mono := by
        native_decide
      reft_anti_mono := by
        native_decide
      top_le_reft_bot := by
        native_decide
      le_reft_top_of_le_prov_of_le_reft := by
        native_decide
      reft_le_prov_reft := by
        native_decide }
  letI : ACR.APS (Fin 3) := apsInst
  let c5Inst : ACR.C5 (Fin 3) :=
    { le_top := by
        native_decide }
  letI : ACR.C5 (Fin 3) := c5Inst
  have hg : Nonempty (ACR.GödelFixpoint (Fin 3)) := by
    refine ⟨⟨1, ?_⟩⟩
    native_decide
  have hle : □(⊠(⊤ : Fin 3)) ≤ ⊠(⊤ : Fin 3) := h (α := Fin 3) hg
  have hfalse : ¬ (□(⊠(⊤ : Fin 3)) ≤ ⊠(⊤ : Fin 3)) := by
    native_decide
  exact hfalse hle

end AutomatedTheoryConstruction
