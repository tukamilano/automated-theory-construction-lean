import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_reft_fixpoint_iff_reft_top_000005_is_false : ¬(∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {x : α}, x ≐ ⊠x ↔ x ≐ ⊠(⊤ : α)) := by
  intro h
  let T : Type := Bool
  let rel : T → T → Prop := fun a b => a = false ∨ b = true
  let rf : T → T := Bool.not
  let acrT : ACR T :=
    { top := true
      bot := false
      le := rel
      le_refl := by
        intro a
        cases a <;> simp [rel]
      le_trans := by
        intro a b c hab hbc
        cases a <;> cases b <;> cases c <;> simp [rel] at hab hbc ⊢ }
  letI : ACR T := acrT
  let provT : ACR.Prov T :=
    { prov := id }
  letI : ACR.Prov T := provT
  let reftT : ACR.Reft T :=
    { reft := rf }
  letI : ACR.Reft T := reftT
  let apsT : ACR.APS T :=
    { prov_mono := by
        intro x y hxy
        simpa [rel] using hxy
      reft_anti_mono := by
        intro x y hxy
        cases x <;> cases y <;> simp [rel, rf] at hxy ⊢
      top_le_reft_bot := by
        simp [rel, rf]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxry
        cases x <;> cases y <;> simp [rel, rf] at hxy hxry ⊢
      reft_le_prov_reft := by
        intro x
        cases x <;> simp [rel, rf] }
  letI : ACR.APS T := apsT
  let c5T : ACR.C5 T :=
    { le_top := by
        intro x
        cases x <;> simp [rel] }
  letI : ACR.C5 T := c5T
  have h0 : ((false : T) ≐ ⊠(false : T)) ↔ ((false : T) ≐ ⊠(⊤ : T)) := h (α := T) (x := false)
  have hRight : (false : T) ≐ ⊠(⊤ : T) := by
    constructor <;> simp [rel, rf]
  have hLeft : (false : T) ≐ ⊠(false : T) := h0.2 hRight
  have htf : (true : T) ≤ (false : T) := hLeft.2
  simpa [rel] using htf

end AutomatedTheoryConstruction
