import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


/-- `⊠⊠⊤ ≐ ⊠⊤` holds exactly when the theory has a Gödel fixpoint. -/
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


/-- Assuming a Gödel fixpoint exists, `x` is reft-fixed exactly when `x ≐ ⊠⊤`. -/
theorem thm_reft_fixedpoint_iff_reft_top_000005 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ {x : α}, (x ≐ ⊠x) ↔ x ≐ ⊠(⊤ : α) := by
  intro α _ _ _ _ _ hg x
  constructor
  · intro hx
    simpa using (ACR.gf_equiv_reft_top (g := ⟨x, hx⟩))
  · intro hx
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    have htop : ⊠⊠(⊤ : α) ≐ ⊠(⊤ : α) := by
      constructor
      · simpa using (ACR.reft_reft_top_le_reft_top (α := α))
      · simpa using (ACR.reft_anti_mono (ACR.le_top (x := ⊠(⊤ : α))))
    constructor
    · calc
        x ≤ ⊠(⊤ : α) := hx.1
        _ ≤ ⊠⊠(⊤ : α) := htop.2
        _ ≤ ⊠x := ACR.reft_anti_mono hx.1
    · calc
        ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono hx.2
        _ ≤ ⊠(⊤ : α) := htop.1
        _ ≤ x := hx.2


/-- In a consistent theory, the box of any Gödel fixpoint is irrefutable. -/
theorem thm_consistent_godel_box_irrefutable_000003 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ∀ g : ACR.GödelFixpoint α, ¬ (⊬ □g.1) := by
  intro α _ _ _ _ hcons g hbox
  have h1 : g.1 ≤ (⊥ : α) :=
    le_trans (le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))) hbox
  have h2 : ⊠(⊥ : α) ≤ ⊠g.1 := ACR.reft_anti_mono h1
  have h3 : ⊠(⊥ : α) ≤ g.1 := le_trans h2 g.2.2
  exact hcons <|
    calc
      (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
      _ ≤ g.1 := h3
      _ ≤ ⊥ := h1


/-- Any two reft-fixed points are equivalent. -/
theorem thm_reft_fixpoints_equivalent_000007 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {x y : α}, x ≐ ⊠x → y ≐ ⊠y → x ≐ y := by
  intro α _ _ _ _ _ x y hx hy
  have hx' : x ≐ ⊠(⊤ : α) := by
    simpa using (ACR.gf_equiv_reft_top (g := ⟨x, hx⟩))
  have hy' : y ≐ ⊠(⊤ : α) := by
    simpa using (ACR.gf_equiv_reft_top (g := ⟨y, hy⟩))
  constructor
  · exact le_trans hx'.1 hy'.2
  · exact le_trans hy'.1 hx'.2


/-- There exists an ACR model with a reft-fixed point that is not equivalent to `⊠⊤`. -/
theorem thm_exists_reft_fixpoint_not_reft_top_000008 : ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ∃ x : α, Nonempty (ACR.GödelFixpoint α) ∧ x ≐ ⊠x ∧ ¬ (x ≐ ⊠(⊤ : α)) := by
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
  refine ⟨⟨1⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨⟨1⟩, ?_⟩⟩
    constructor
    · show 1 ≤ 1
      exact Nat.le_refl 1
    · show 1 ≤ 1
      exact Nat.le_refl 1
  · constructor
    · show 1 ≤ 1
      exact Nat.le_refl 1
    · show 1 ≤ 1
      exact Nat.le_refl 1
  · intro hx
    have h21 : 2 ≤ 1 := by
      change ((⟨2⟩ : ULift Nat) ≤ ⟨1⟩)
      exact hx.2
    have h : ¬ 2 ≤ 1 := by decide
    exact h h21


/-- In a consistent theory, every Gödel fixpoint is irrefutable. -/
theorem thm_consistent_godel_irrefutable_000009 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ∀ g : ACR.GödelFixpoint α, ¬ (⊬ g.1) := by
  intro α _ _ _ _ hC g hg
  have h1 : g.1 ≤ (⊥ : α) := hg
  have h2 : ⊠(⊥ : α) ≤ ⊠g.1 := ACR.reft_anti_mono h1
  have h3 : ⊠(⊥ : α) ≤ g.1 := le_trans h2 g.2.2
  exact hC <|
    calc
      (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
      _ ≤ g.1 := h3
      _ ≤ ⊥ := h1


/-- ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x : α}, x ≐ ⊠x → x ≤ □x (auto-generated from op_000022) -/
theorem thm_reft_fixedpoint_le_box_000022 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x : α}, x ≐ ⊠x → x ≤ □x := by
  intro α _ _ _ _ x h
  calc
    x ≤ ⊠x := h.1
    _ ≤ □⊠x := ACR.reft_le_prov_reft
    _ ≤ □x := ACR.prov_mono h.2

end AutomatedTheoryConstruction
