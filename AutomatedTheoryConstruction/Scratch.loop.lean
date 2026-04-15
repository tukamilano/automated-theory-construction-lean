import Mathlib
import Mathlib
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

noncomputable abbrev chosen_canonical_acr (α : Type*) [LinearOrder α] [BoundedOrder α] [Nontrivial α] : ACR α :=
  Classical.choose (thm_bounded_linear_canonical_realization_000122 (α := α))

noncomputable abbrev chosen_canonical_reft (α : Type*) [LinearOrder α] [BoundedOrder α] [Nontrivial α] :
    @ACR.Reft α (chosen_canonical_acr α) :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec (thm_bounded_linear_canonical_realization_000122 (α := α))))

theorem thm_canonical_godel_fixpoint_top_000129 : ∀ (α : Type*) [LinearOrder α] [BoundedOrder α] [Nontrivial α],
  ∀ g : @ACR.GödelFixpoint α (chosen_canonical_acr α) (chosen_canonical_reft α),
    @ACR.Equivalent α (chosen_canonical_acr α) g.1 (@Top.top α (chosen_canonical_acr α).toTop) := by
  intro α _ _ _ g
  have hreft :
      ∀ x : α,
        @ACR.Reft.reft α (chosen_canonical_acr α) (chosen_canonical_reft α) x =
          @Top.top α (chosen_canonical_acr α).toTop :=
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Classical.choose_spec
              (thm_bounded_linear_canonical_realization_000122 (α := α))))))).2.1
  simpa [ACR.Equivalent, hreft g.1] using g.2

end AutomatedTheoryConstruction
