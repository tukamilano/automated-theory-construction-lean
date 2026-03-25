import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_exists_godel_not_henkin_fixpoint_000016 : ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ∃ g : ACR.GödelFixpoint α, ¬ (g.1 ≐ □g.1) := by
  let hA : ACR (ULift Nat) :=
    { top := ⟨0⟩
      bot := ⟨2⟩
      le := fun x y => x.down ≤ y.down
      lt := fun x y => x.down ≤ y.down ∧ ¬ y.down ≤ x.down
      le_refl := by
        intro x
        exact Nat.le_refl x.down
      le_trans := by
        intro x y z hxy hyz
        exact Nat.le_trans hxy hyz }
  let hP : @ACR.Prov (ULift Nat) hA :=
    { prov := fun _ => ⟨2⟩ }
  let hR : @ACR.Reft (ULift Nat) hA :=
    { reft := fun x => ⟨2 - x.down⟩ }
  letI : ACR (ULift Nat) := hA
  letI : ACR.Prov (ULift Nat) := hP
  letI : ACR.Reft (ULift Nat) := hR
  let hAPS : ACR.APS (ULift Nat) :=
    { prov_mono := by
        intro x y hxy
        exact Nat.le_refl 2
      reft_anti_mono := by
        intro x y hxy
        show 2 - y.down ≤ 2 - x.down
        exact Nat.sub_le_sub_left hxy 2
      top_le_reft_bot := by
        show 0 ≤ (2 - 2)
        decide
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxry
        show x.down ≤ 2
        simpa using hxy
      reft_le_prov_reft := by
        intro x
        show 2 - x.down ≤ 2
        exact Nat.sub_le _ _ }
  letI : ACR.APS (ULift Nat) := hAPS
  refine ⟨ULift Nat, hA, hP, hR, hAPS, ?_⟩
  refine ⟨⟨⟨1⟩, ?_⟩, ?_⟩
  · constructor
    · show 1 ≤ 1
      exact Nat.le_refl 1
    · show 1 ≤ 1
      exact Nat.le_refl 1
  · intro h
    have h21 : 2 ≤ 1 := by
      change ((⟨2⟩ : ULift Nat) ≤ ⟨1⟩)
      exact h.2
    have h' : ¬ 2 ≤ 1 := by
      decide
    exact h' h21

end AutomatedTheoryConstruction
