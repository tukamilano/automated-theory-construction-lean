import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_double_reft_below_reft_000031 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ x : α, ⊠⊠x ≤ ⊠x := by
  intro α _ _ _ _ _ hG x
  letI : Nonempty (ACR.GödelFixpoint α) := hG
  have hx_top : x ≤ (⊤ : α) := ACR.le_top
  have htop : ⊠(⊤ : α) ≤ ⊠x := ACR.reft_anti_mono hx_top
  have hxx : ⊠⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono htop
  exact le_trans hxx (le_trans (ACR.reft_reft_top_le_reft_top (α := α)) htop)

end AutomatedTheoryConstruction
