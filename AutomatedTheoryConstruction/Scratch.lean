import Mathlib.Logic.Function.Iterate
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_reft_iterate_top_equiv_000026 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ⊠⊠(⊤ : α) ≐ ⊠(⊤ : α) → ∀ n : Nat, (Nat.iterate (fun y : α => ⊠ y) (n + 1) (⊤ : α)) ≐ ⊠(⊤ : α) := by
  intro α _ _ _ _ _ h n
  let f : α → α := fun y => ⊠ y
  have hmap : ∀ {x y : α}, x ≐ y → f x ≐ f y := by
    intro x y hxy
    exact ⟨ACR.reft_anti_mono hxy.2, ACR.reft_anti_mono hxy.1⟩
  have hiter_map : ∀ m : Nat, ∀ {x y : α}, x ≐ y → Nat.iterate f m x ≐ Nat.iterate f m y := by
    intro m
    induction m with
    | zero =>
        intro x y hxy
        simpa [Nat.iterate] using hxy
    | succ m ihm =>
        intro x y hxy
        simpa [f, Nat.iterate] using ihm (x := f x) (y := f y) (hmap hxy)
  have hstable : ∀ m : Nat, Nat.iterate f m (⊠(⊤ : α)) ≐ ⊠(⊤ : α) := by
    intro m
    induction m with
    | zero =>
        exact ⟨le_rfl, le_rfl⟩
    | succ m ihm =>
        have hstep : Nat.iterate f m (⊠⊠(⊤ : α)) ≐ Nat.iterate f m (⊠(⊤ : α)) :=
          hiter_map m (x := ⊠⊠(⊤ : α)) (y := ⊠(⊤ : α)) h
        constructor
        · exact le_trans hstep.1 ihm.1
        · exact le_trans ihm.2 hstep.2
  simpa [f, Nat.iterate] using hstable n

end AutomatedTheoryConstruction
