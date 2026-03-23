import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_op_000087 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g : ACR.GödelFixpoint α, (g.1 ≤ (⊥ : α)) ↔ (□g.1 ≤ (⊥ : α)) := by
  intro α _ _ _ _ _ g
  by_cases hinc : ((⊤ : α) ≤ (⊥ : α))
  · constructor
    · intro _
      exact le_trans (ACR.le_top (x := □g.1)) hinc
    · intro _
      exact le_trans (ACR.le_top (x := g.1)) hinc
  · have hC : ACR.Consistent α := hinc
    constructor
    · intro hg
      exact False.elim ((thm_op_000005 (g := g) hC) hg)
    · intro hbox
      exact False.elim (((thm_op_000042 (g := g)).1 hC) hbox)

end AutomatedTheoryConstruction
