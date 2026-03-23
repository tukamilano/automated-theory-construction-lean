import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_equiv_reft_top_iff_reft_fixpoint_000009 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)] {x : α}, x ≡ ⊠(⊤ : α) ↔ x ≡ ⊠x := by
  intro α _ _ _ _ _ _ x
  constructor
  · intro hx
    constructor
    · exact le_trans hx.1 (ACR.reft_anti_mono (ACR.le_top (x := x)))
    · have h1 : ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono hx.2
      exact le_trans h1 (le_trans (ACR.reft_reft_top_le_reft_top (α := α)) hx.2)
  · intro hx
    constructor
    · have hxbox : x ≤ □x := by
        calc
          x ≤ ⊠x := hx.1
          _ ≤ □⊠x := ACR.reft_le_prov_reft
          _ ≤ □x := ACR.prov_mono hx.2
      exact ACR.le_reft_top_of_le_prov_of_le_reft hxbox hx.1
    · exact le_trans (ACR.reft_anti_mono (ACR.le_top (x := x))) hx.2

end AutomatedTheoryConstruction
