import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_indep_of_subset_of_subset_000001 : ∀ (α : Type*) (G : SemiGraphoid α) (X X' Y Y' Z : Set α), X ⊆ X' → Y ⊆ Y' → G.Indep X' Y' Z → G.Indep X Y Z := by
  intro α G X X' Y Y' Z hXX' hYY' h
  rw [← Set.union_diff_cancel hYY'] at h
  have hXY : G.Indep X' Y Z := G.decomposition _ _ _ _ h
  have hYX' : G.Indep Y X' Z := G.symmetry _ _ _ hXY
  rw [← Set.union_diff_cancel hXX'] at hYX'
  have hYX : G.Indep Y X Z := G.decomposition _ _ _ _ hYX'
  exact G.symmetry _ _ _ hYX

end AutomatedTheoryConstruction
