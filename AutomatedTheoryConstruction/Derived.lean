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


/-- ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ACR.Consistent α ∧ Nonempty... -/
theorem thm_exists_consistent_fixpoint_not_reft_top_000018 : ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) ∧ ∃ x : α, x ≐ ⊠x ∧ ¬ (x ≐ ⊠(⊤ : α)) := by
  let rel : ULift Nat → ULift Nat → Prop := fun x y => x.down = 0 ∨ x = y ∨ y.down = 3
  let provFn : ULift Nat → ULift Nat := fun _ => ⟨3⟩
  let reftFn : ULift Nat → ULift Nat := fun x => if x.down = 1 ∨ x.down = 3 then ⟨1⟩ else ⟨3⟩
  let hA : ACR (ULift Nat) :=
    { top := ⟨2⟩
      bot := ⟨0⟩
      le := rel
      lt := fun a b => rel a b ∧ ¬ rel b a
      le_refl := by
        intro x
        exact Or.inr <| Or.inl rfl
      le_trans := by
        intro x y z hxy hyz
        rcases hxy with hx0 | hxy | hy3
        · exact Or.inl hx0
        · cases hxy
          exact hyz
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              rcases hyz with hy0 | hyEq | hz3
              · simp at hy0
              · cases hyEq
                exact Or.inr <| Or.inr rfl
              · exact Or.inr <| Or.inr hz3
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  let hP : @ACR.Prov (ULift Nat) hA :=
    { prov := provFn }
  let hR : @ACR.Reft (ULift Nat) hA :=
    { reft := reftFn }
  letI : ACR (ULift Nat) := hA
  letI : ACR.Prov (ULift Nat) := hP
  letI : ACR.Reft (ULift Nat) := hR
  let hAPS : @ACR.APS (ULift Nat) hA hP hR :=
    { prov_mono := by
        intro x y hxy
        change rel (provFn x) (provFn y)
        simp [rel, provFn]
      reft_anti_mono := by
        intro x y hxy
        change rel (reftFn y) (reftFn x)
        rcases hxy with hx0 | hxy | hy3
        · cases x with
          | up n =>
              simp at hx0
              subst hx0
              simp [rel, reftFn]
        · cases hxy
          simp [rel]
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              by_cases hx : x.down = 1 ∨ x.down = 3
              · simp [rel, reftFn, hx]
              · simp [rel, reftFn, hx]
      top_le_reft_bot := by
        change rel ⟨2⟩ (reftFn ⟨0⟩)
        simp [rel, reftFn]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxry
        change rel x (reftFn ⟨2⟩)
        simp [rel, reftFn]
      reft_le_prov_reft := by
        intro x
        change rel (reftFn x) (provFn (reftFn x))
        simp [rel, provFn] }
  letI : ACR.APS (ULift Nat) := hAPS
  refine ⟨ULift Nat, hA, hP, hR, hAPS, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change ¬ rel ⟨2⟩ ⟨0⟩
    simp [rel]
  · refine ⟨⟨⟨1⟩, ?_⟩⟩
    constructor
    · change rel ⟨1⟩ (reftFn ⟨1⟩)
      simp [rel, reftFn]
    · change rel (reftFn ⟨1⟩) ⟨1⟩
      simp [rel, reftFn]
  · refine ⟨⟨1⟩, ?_⟩
    constructor
    · constructor
      · change rel ⟨1⟩ (reftFn ⟨1⟩)
        simp [rel, reftFn]
      · change rel (reftFn ⟨1⟩) ⟨1⟩
        simp [rel, reftFn]
    · intro h
      have h31 := h.2
      change rel (reftFn ⟨2⟩) ⟨1⟩ at h31
      simp [rel, reftFn] at h31


/-- ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ACR.Consistent α ∧ Nonempty... -/
theorem thm_reft_fixedpoint_not_above_reft_top_000019 : ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) ∧ ∃ x : α, x ≐ ⊠x ∧ ¬ (⊠(⊤ : α) ≤ x) := by
  let rel : ULift Nat → ULift Nat → Prop := fun x y => x.down = 0 ∨ x = y ∨ y.down = 3
  let provFn : ULift Nat → ULift Nat := fun _ => ⟨3⟩
  let reftFn : ULift Nat → ULift Nat := fun x => if x.down = 1 ∨ x.down = 3 then ⟨1⟩ else ⟨3⟩
  let hA : ACR (ULift Nat) :=
    { top := ⟨2⟩
      bot := ⟨0⟩
      le := rel
      lt := fun a b => rel a b ∧ ¬ rel b a
      le_refl := by
        intro x
        exact Or.inr <| Or.inl rfl
      le_trans := by
        intro x y z hxy hyz
        rcases hxy with hx0 | hxy | hy3
        · exact Or.inl hx0
        · cases hxy
          exact hyz
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              rcases hyz with hy0 | hyEq | hz3
              · simp at hy0
              · cases hyEq
                exact Or.inr <| Or.inr rfl
              · exact Or.inr <| Or.inr hz3
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  let hP : @ACR.Prov (ULift Nat) hA :=
    { prov := provFn }
  let hR : @ACR.Reft (ULift Nat) hA :=
    { reft := reftFn }
  letI : ACR (ULift Nat) := hA
  letI : ACR.Prov (ULift Nat) := hP
  letI : ACR.Reft (ULift Nat) := hR
  let hAPS : @ACR.APS (ULift Nat) hA hP hR :=
    { prov_mono := by
        intro x y hxy
        change rel (provFn x) (provFn y)
        simp [rel, provFn]
      reft_anti_mono := by
        intro x y hxy
        change rel (reftFn y) (reftFn x)
        rcases hxy with hx0 | hxy | hy3
        · cases x with
          | up n =>
              simp at hx0
              subst hx0
              simp [rel, reftFn]
        · cases hxy
          simp [rel]
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              by_cases hx : x.down = 1 ∨ x.down = 3
              · simp [rel, reftFn, hx]
              · simp [rel, reftFn, hx]
      top_le_reft_bot := by
        change rel ⟨2⟩ (reftFn ⟨0⟩)
        simp [rel, reftFn]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxry
        change rel x (reftFn ⟨2⟩)
        simp [rel, reftFn]
      reft_le_prov_reft := by
        intro x
        change rel (reftFn x) (provFn (reftFn x))
        simp [rel, provFn] }
  letI : ACR.APS (ULift Nat) := hAPS
  refine ⟨ULift Nat, hA, hP, hR, hAPS, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change ¬ rel ⟨2⟩ ⟨0⟩
    simp [rel]
  · refine ⟨⟨⟨1⟩, ?_⟩⟩
    constructor
    · change rel ⟨1⟩ (reftFn ⟨1⟩)
      simp [rel, reftFn]
    · change rel (reftFn ⟨1⟩) ⟨1⟩
      simp [rel, reftFn]
  · refine ⟨⟨1⟩, ?_⟩
    constructor
    · constructor
      · change rel ⟨1⟩ (reftFn ⟨1⟩)
        simp [rel, reftFn]
      · change rel (reftFn ⟨1⟩) ⟨1⟩
        simp [rel, reftFn]
    · intro h
      change rel (reftFn ⟨2⟩) ⟨1⟩ at h
      simp [rel, reftFn] at h


/-- ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {h : ACR.HenkinFixpoint α}, h.1 ≤ ⊠h.1 ↔ h.1 ≤ ⊠(⊤ : α) (auto-generated from op_000006) -/
theorem thm_henkin_le_reft_self_iff_top_000006 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {h : ACR.HenkinFixpoint α}, h.1 ≤ ⊠h.1 ↔ h.1 ≤ ⊠(⊤ : α) := by
  intro α _ _ _ _ _ h
  constructor
  · intro hh
    exact ACR.le_reft_top_of_le_prov_of_le_reft h.2.1 hh
  · intro hh
    exact le_trans hh (ACR.reft_anti_mono (ACR.le_top (x := h.1)))


/-- ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ∃ (x y : α), x ≐ ⊠x ∧ y ≐ ⊠... -/
theorem thm_distinct_reft_fixpoints_exist_000011 : ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ∃ (x y : α), x ≐ ⊠x ∧ y ≐ ⊠y ∧ ¬ (x ≐ y) := by
  let rel : ULift Nat → ULift Nat → Prop := fun x y => x.down = 0 ∨ x = y ∨ y.down = 3
  let provFn : ULift Nat → ULift Nat := fun _ => ⟨3⟩
  let reftFn : ULift Nat → ULift Nat := fun x =>
    if x.down = 0 then ⟨3⟩ else if x.down = 3 then ⟨0⟩ else x
  let hA : ACR (ULift Nat) :=
    { top := ⟨0⟩
      bot := ⟨0⟩
      le := rel
      lt := fun a b => rel a b ∧ ¬ rel b a
      le_refl := by
        intro x
        exact Or.inr <| Or.inl rfl
      le_trans := by
        intro x y z hxy hyz
        rcases hxy with hx0 | hxy | hy3
        · exact Or.inl hx0
        · cases hxy
          exact hyz
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              rcases hyz with hy0 | hyEq | hz3
              · simp at hy0
              · cases hyEq
                exact Or.inr <| Or.inr rfl
              · exact Or.inr <| Or.inr hz3
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  let hP : @ACR.Prov (ULift Nat) hA :=
    { prov := provFn }
  let hR : @ACR.Reft (ULift Nat) hA :=
    { reft := reftFn }
  letI : ACR (ULift Nat) := hA
  letI : ACR.Prov (ULift Nat) := hP
  letI : ACR.Reft (ULift Nat) := hR
  let hAPS : @ACR.APS (ULift Nat) hA hP hR :=
    { prov_mono := by
        intro x y hxy
        change rel (provFn x) (provFn y)
        simp [rel, provFn]
      reft_anti_mono := by
        intro x y hxy
        change rel (reftFn y) (reftFn x)
        rcases hxy with hx0 | hxy | hy3
        · cases x with
          | up n =>
              simp at hx0
              subst hx0
              simp [rel, reftFn]
        · cases hxy
          simp [rel]
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              simp [rel, reftFn]
      top_le_reft_bot := by
        change rel ⟨0⟩ (reftFn ⟨0⟩)
        simp [rel, reftFn]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxry
        change rel x (reftFn ⟨0⟩)
        simpa [provFn, reftFn] using hxy
      reft_le_prov_reft := by
        intro x
        change rel (reftFn x) (provFn (reftFn x))
        simp [rel, provFn] }
  letI : ACR.APS (ULift Nat) := hAPS
  refine ⟨ULift Nat, hA, hP, hR, hAPS, ?_⟩
  refine ⟨⟨1⟩, ⟨2⟩, ?_⟩
  constructor
  · constructor
    · change rel ⟨1⟩ (reftFn ⟨1⟩)
      simp [rel, reftFn]
    · change rel (reftFn ⟨1⟩) ⟨1⟩
      simp [rel, reftFn]
  · constructor
    · constructor
      · change rel ⟨2⟩ (reftFn ⟨2⟩)
        simp [rel, reftFn]
      · change rel (reftFn ⟨2⟩) ⟨2⟩
        simp [rel, reftFn]
    · intro h
      have h12 := h.1
      change rel ⟨1⟩ ⟨2⟩ at h12
      simpa [rel] using h12


/-- ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ((∀ {x : α}, x ≐ ⊠x → x ≐ □x) ↔ (□(⊠(⊤ : α)) ≤ ⊠(⊤ : α))) (auto-generated from op_000029) -/
theorem thm_reft_fixedpoints_henkin_criterion_000029 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ((∀ {x : α}, x ≐ ⊠x → x ≐ □x) ↔ (□(⊠(⊤ : α)) ≤ ⊠(⊤ : α))) := by
  intro α _ _ _ _ _ hg
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  constructor
  · intro h
    have hfix : (⊠(⊤ : α)) ≐ ⊠(⊠(⊤ : α)) := by
      constructor
      · simpa using (ACR.reft_anti_mono (ACR.le_top (x := ⊠(⊤ : α))))
      · simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    have hbox : (⊠(⊤ : α)) ≐ □(⊠(⊤ : α)) := h hfix
    simpa using hbox.2
  · intro h x hx
    have hxTop : x ≐ ⊠(⊤ : α) := ACR.gf_equiv_reft_top (g := ⟨x, hx⟩)
    constructor
    · calc
        x ≤ ⊠x := hx.1
        _ ≤ □⊠x := ACR.reft_le_prov_reft
        _ ≤ □x := ACR.prov_mono hx.2
    · calc
        □x ≤ □(⊠(⊤ : α)) := ACR.prov_mono hxTop.1
        _ ≤ ⊠(⊤ : α) := h
        _ ≤ x := hxTop.2


/-- ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ACR.Consistent α ∧ Nonempty... -/
theorem thm_exists_consistent_model_without_joint_fixpoint_000031 : ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) ∧ Nonempty (ACR.HenkinFixpoint α) ∧ ¬ ∃ x : α, x ≐ ⊠x ∧ x ≐ □x := by
  let rel : ULift Nat → ULift Nat → Prop := fun x y => x.down = 0 ∨ x = y ∨ y.down = 3
  let provFn : ULift Nat → ULift Nat := fun _ => ⟨3⟩
  let reftFn : ULift Nat → ULift Nat := fun x => if x.down = 1 ∨ x.down = 3 then ⟨1⟩ else ⟨3⟩
  let hA : ACR (ULift Nat) :=
    { top := ⟨2⟩
      bot := ⟨0⟩
      le := rel
      lt := fun a b => rel a b ∧ ¬ rel b a
      le_refl := by
        intro x
        exact Or.inr <| Or.inl rfl
      le_trans := by
        intro x y z hxy hyz
        rcases hxy with hx0 | hxy | hy3
        · exact Or.inl hx0
        · cases hxy
          exact hyz
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              rcases hyz with hy0 | hyEq | hz3
              · simp at hy0
              · cases hyEq
                exact Or.inr <| Or.inr rfl
              · exact Or.inr <| Or.inr hz3
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  let hP : @ACR.Prov (ULift Nat) hA :=
    { prov := provFn }
  let hR : @ACR.Reft (ULift Nat) hA :=
    { reft := reftFn }
  letI : ACR (ULift Nat) := hA
  letI : ACR.Prov (ULift Nat) := hP
  letI : ACR.Reft (ULift Nat) := hR
  let hAPS : @ACR.APS (ULift Nat) hA hP hR :=
    { prov_mono := by
        intro x y hxy
        change rel (provFn x) (provFn y)
        simp [rel, provFn]
      reft_anti_mono := by
        intro x y hxy
        change rel (reftFn y) (reftFn x)
        rcases hxy with hx0 | hxy | hy3
        · cases x with
          | up n =>
              simp at hx0
              subst hx0
              simp [rel, reftFn]
        · cases hxy
          simp [rel]
        · cases y with
          | up n =>
              simp at hy3
              subst hy3
              by_cases hx : x.down = 1 ∨ x.down = 3
              · simp [rel, reftFn, hx]
              · simp [rel, reftFn, hx]
      top_le_reft_bot := by
        change rel ⟨2⟩ (reftFn ⟨0⟩)
        simp [rel, reftFn]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxry
        change rel x (reftFn ⟨2⟩)
        simp [rel, reftFn]
      reft_le_prov_reft := by
        intro x
        change rel (reftFn x) (provFn (reftFn x))
        simp [rel, provFn] }
  letI : ACR.APS (ULift Nat) := hAPS
  refine ⟨ULift Nat, hA, hP, hR, hAPS, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ¬ rel ⟨2⟩ ⟨0⟩
    simp [rel]
  · refine ⟨⟨⟨1⟩, ?_⟩⟩
    constructor
    · change rel ⟨1⟩ (reftFn ⟨1⟩)
      simp [rel, reftFn]
    · change rel (reftFn ⟨1⟩) ⟨1⟩
      simp [rel, reftFn]
  · refine ⟨⟨⟨3⟩, ?_⟩⟩
    constructor
    · change rel ⟨3⟩ (provFn ⟨3⟩)
      simp [rel, provFn]
    · change rel (provFn ⟨3⟩) ⟨3⟩
      simp [rel, provFn]
  · rintro ⟨x, hx, hbox⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hbox with ⟨hbox1, hbox2⟩
    cases x with
    | up n =>
        have h3 : rel (provFn ⟨n⟩) ⟨n⟩ := by
          simpa using hbox2
        simp [rel, provFn] at h3
        have hn : n = 3 := by
          rcases h3 with h | h
          · exact h.symm
          · exact h
        subst n
        have h31 : rel ⟨3⟩ (reftFn ⟨3⟩) := by
          simpa using hx1
        simp [rel, reftFn] at h31


/-- ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], Nonempty (ACR.GödelFixpoint α) → ((⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ↔ ∀ {x : α}, x ≐ ⊠x → x ≐ ⊠(⊤ : α)) (auto-generated from op_000032) -/
theorem thm_double_reft_top_iff_all_fixpoints_reft_top_000032 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], Nonempty (ACR.GödelFixpoint α) → ((⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ↔ ∀ {x : α}, x ≐ ⊠x → x ≐ ⊠(⊤ : α)) := by
  intro α _ _ _ _ hg
  constructor
  · intro h x hx
    have hxBox : x ≤ □x := by
      calc
        x ≤ ⊠x := hx.1
        _ ≤ □⊠x := ACR.reft_le_prov_reft
        _ ≤ □x := ACR.prov_mono hx.2
    have hxTop : x ≤ ⊠(⊤ : α) := by
      exact ACR.le_reft_top_of_le_prov_of_le_reft hxBox hx.1
    constructor
    · exact hxTop
    · calc
        ⊠(⊤ : α) ≤ ⊠⊠(⊤ : α) := h.2
        _ ≤ ⊠x := ACR.reft_anti_mono hxTop
        _ ≤ x := hx.2
  · intro h
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    constructor
    · simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    · obtain ⟨g⟩ := hg
      have hgTop : g.1 ≐ ⊠(⊤ : α) := h g.2
      calc
        ⊠(⊤ : α) ≤ g.1 := hgTop.2
        _ ≤ ⊠g.1 := g.2.1
        _ ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono hgTop.2


/-- ∃ (α : Type _), ∃ (hA : ACR α), ∃ (hP : @ACR.Prov α hA), ∃ (hR : @ACR.Reft α hA), ∃ (hAPS : @ACR.APS α hA hP hR), letI : ACR α := hA; letI : ACR.Prov α := hP; letI : ACR.Reft α := hR; letI : ACR.APS α := hAPS; ∃ g : ACR.GödelFixpoint α, ... -/
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
