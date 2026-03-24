import Mathlib.Logic.Function.Iterate
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_iterate_box_reft_irrefutable_000025 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → ∀ x : α, ∀ n : Nat, ¬ (⊬ (Nat.iterate (fun y : α => □ y) n (⊠ x))) := by
  intro α _ _ _ _ _ hCons hg x n hRef
  have htop : ⊠(⊤ : α) ≤ ⊠x := by
    exact ACR.reft_anti_mono (ACR.le_top (x := x))
  have hiter_mono :
      ∀ m : Nat, ∀ {a b : α}, a ≤ b →
        Nat.iterate (fun y : α => □ y) m a ≤ Nat.iterate (fun y : α => □ y) m b := by
    intro m
    induction m with
    | zero =>
        intro a b hab
        simpa [Nat.iterate] using hab
    | succ m ih =>
        intro a b hab
        simpa [Nat.iterate] using ih (a := □a) (b := □b) (ACR.prov_mono hab)
  have hiter :
      Nat.iterate (fun y : α => □ y) n (⊠(⊤ : α)) ≤
        Nat.iterate (fun y : α => □ y) n (⊠x) :=
    hiter_mono n htop
  exact
    (AutomatedTheoryConstruction.thm_iterate_box_reft_top_irrefutable_000020
      (α := α) hCons hg n)
      (le_trans hiter hRef)

end AutomatedTheoryConstruction
