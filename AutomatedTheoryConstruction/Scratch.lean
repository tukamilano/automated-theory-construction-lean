import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

namespace AutomatedTheoryConstruction

theorem thm_exists_consistent_fixpoint_not_reft_top_000018 : ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) ∧ ∃ x : α, x ≐ ⊠x ∧ ¬ (x ≐ ⊠(⊤ : α)) := by
  let rel : Fin 4 → Fin 4 → Prop := fun x y => x = 0 ∨ x = y ∨ y = 3
  let provFn : Fin 4 → Fin 4 := fun _ => 3
  let reftFn : Fin 4 → Fin 4 := fun x => if x = 1 ∨ x = 3 then 1 else 3
  let hA : ACR (Fin 4) :=
    { top := 2
      bot := 0
      le := rel
      le_refl := by
        intro x
        exact Or.inr <| Or.inl rfl
      le_trans := by
        intro x y z hxy hyz
        rcases hxy with h0 | hxy | hy3
        · subst h0
          exact Or.inl rfl
        · subst hxy
          exact hyz
        · subst hy3
          have hz : z = 3 := by
            simpa [rel] using hyz
          subst hz
          exact Or.inr <| Or.inr rfl }
  let hP : @ACR.Prov (Fin 4) hA :=
    { prov := provFn }
  let hR : @ACR.Reft (Fin 4) hA :=
    { reft := reftFn }
  letI : ACR (Fin 4) := hA
  letI : ACR.Prov (Fin 4) := hP
  letI : ACR.Reft (Fin 4) := hR
  let hAPS : @ACR.APS (Fin 4) hA hP hR :=
    { prov_mono := by
        intro x y hxy
        change rel (provFn x) (provFn y)
        simp [rel, provFn]
      reft_anti_mono := by
        intro x y hxy
        rcases hxy with h0 | hxy | hy3
        · subst h0
          change rel (reftFn y) (reftFn 0)
          simp [rel, reftFn]
        · subst hxy
          change rel (reftFn y) (reftFn y)
          simp [rel]
        · subst hy3
          change rel (reftFn 3) (reftFn x)
          by_cases hx : x = 1 ∨ x = 3
          · simp [rel, reftFn, hx]
          · simp [rel, reftFn, hx]
      top_le_reft_bot := by
        change rel 2 (reftFn 0)
        simp [rel, reftFn]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxry
        change rel x (reftFn 2)
        simpa [rel, provFn, reftFn] using hxy
      reft_le_prov_reft := by
        intro x
        change rel (reftFn x) (provFn (reftFn x))
        simp [rel, provFn] }
  letI : ACR.APS (Fin 4) := hAPS
  refine ⟨Fin 4, hA, hP, hR, hAPS, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change ¬ rel 2 0
    simp [rel]
  · refine ⟨⟨1, ?_⟩⟩
    constructor
    · change rel 1 (reftFn 1)
      simp [rel, reftFn]
    · change rel (reftFn 1) 1
      simp [rel, reftFn]
  · refine ⟨1, ?_⟩
    constructor
    · constructor
      · change rel 1 (reftFn 1)
        simp [rel, reftFn]
      · change rel (reftFn 1) 1
        simp [rel, reftFn]
    · intro h
      have h' : False := by
        simpa [rel, reftFn] using h.2
      exact h'

end AutomatedTheoryConstruction
