import Mathlib
import Mathlib
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_universal_reft_fixed_inconsistent_000132 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∀ x : α, x ≐ ⊠x) → ACR.Inconsistent α := by
  intro α _ _ _ _ h
  exact le_trans ACR.top_le_reft_bot (h ⊥).2

end AutomatedTheoryConstruction
