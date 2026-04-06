import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_indep_three_union_iff_000003 : ∀ (α : Type*) (G : SemiGraphoid α) (X Y W V Z : Set α), G.Indep X ((Y ∪ W) ∪ V) Z ↔ (G.Indep X Y Z ∧ G.Indep X W (Y ∪ Z) ∧ G.Indep X V ((Y ∪ W) ∪ Z)) := by
  intro α G X Y W V Z
  rw [G.indep_union_iff X (Y ∪ W) V Z, G.indep_union_iff X Y W Z]
  constructor
  · rintro ⟨⟨hY, hW⟩, hV⟩
    exact ⟨hY, hW, hV⟩
  · rintro ⟨hY, hW, hV⟩
    exact ⟨⟨hY, hW⟩, hV⟩

end AutomatedTheoryConstruction
