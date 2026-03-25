import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_double_reft_top_iff_godel_fixpoint_000001 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ↔ Nonempty (ACR.GödelFixpoint α) := by
  intro α _ _ _ _ _
  constructor
  · intro h
    refine ⟨⟨⊠(⊤ : α), ?_⟩⟩
    exact ⟨h.2, h.1⟩
  · intro hg
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    constructor
    · simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    · simpa using (ACR.reft_anti_mono (ACR.le_top (x := ⊠(⊤ : α))))

end AutomatedTheoryConstruction
