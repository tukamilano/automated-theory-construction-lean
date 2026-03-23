import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


theorem thm_op_000001 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ g : ACR.GödelFixpoint α, g.1 ≤ □g.1 := by
  intros α hACR hProv hReft hAPS g
  exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))


theorem thm_op_000002 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, ACR.Equivalent g.1 h.1 := by
  intro α _ _ _ _ _ g h
  have hg : g.1 ≡ ⊠⊤ := ACR.gf_equiv_reft_top (g := g)
  have hh : h.1 ≡ ⊠⊤ := ACR.gf_equiv_reft_top (g := h)
  exact ⟨le_trans hg.1 hh.2, le_trans hh.1 hg.2⟩


theorem thm_op_000003 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ⊠(⊤ : α) ≡ ⊠⊠(⊤ : α) := by
  intro α
  intros
  change (⊠(⊤ : α) ≤ ⊠⊠(⊤ : α)) ∧ (⊠⊠(⊤ : α) ≤ ⊠(⊤ : α))
  constructor
  · let g : ACR.GödelFixpoint α := ‹Nonempty (ACR.GödelFixpoint α)›.some
    have h₁ : ⊠(⊤ : α) ≤ g.1 := (ACR.gf_equiv_reft_top (g := g)).2
    have h₂ : g.1 ≤ ⊠g.1 := g.2.1
    have h₃ : ⊠g.1 ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono h₁
    exact le_trans h₁ (le_trans h₂ h₃)
  · simpa using (ACR.reft_reft_top_le_reft_top (α := α))


theorem thm_op_000004 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ∃ g : ACR.GödelFixpoint α, g.1 ≡ ⊠(⊤ : α) := by
  intro α _ _ _ _ _ _
  let g : ACR.GödelFixpoint α := ‹Nonempty (ACR.GödelFixpoint α)›.some
  refine ⟨g, ?_⟩
  exact ACR.gf_equiv_reft_top


theorem thm_op_000005 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ g : ACR.GödelFixpoint α, ACR.Consistent α → ¬ (g.1 ≤ (⊥ : α)) := by
  intro α hACR hProv hReft hAPS g hC hg0
  apply hC
  change (⊤ : α) ≤ (⊥ : α)
  calc
    (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
    _ ≤ ⊠g.1 := ACR.reft_anti_mono hg0
    _ ≤ g.1 := g.2.2
    _ ≤ (⊥ : α) := hg0


theorem thm_op_000007 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g : ACR.GödelFixpoint α, ACR.Equivalent (□g.1) (□(⊠(⊤ : α))) := by
  intro α _ _ _ _ _ g
  have hg : g.1 ≡ ⊠⊤ := ACR.gf_equiv_reft_top (g := g)
  exact ⟨ACR.prov_mono hg.1, ACR.prov_mono hg.2⟩


theorem thm_op_000008 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g : ACR.GödelFixpoint α, g.1 ≤ □(⊠(⊤ : α)) := by
  intro α _ _ _ _ _ g
  calc
    g.1 ≤ □g.1 := by
      exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))
    _ ≤ □(⊠(⊤ : α)) := by
      apply ACR.prov_mono
      exact (ACR.gf_equiv_reft_top (g := g)).1


theorem thm_op_000009 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ACR.Consistent α ↔ ¬ ((⊠(⊤ : α)) ≤ (⊥ : α)) := by
  intro α _ _ _ _ _ _
  constructor
  · intro h
    simpa using ACR.irrefutable_reft_top (α := α) h
  · intro h
    exact fun h' => h (le_trans (ACR.le_top (x := ⊠(⊤ : α))) h')


theorem thm_op_000010 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) ↔ ⊠(⊤ : α) ≡ ⊠⊠(⊤ : α) := by
  intro α _ _ _ _ _
  constructor
  · intro hne
    letI : Nonempty (ACR.GödelFixpoint α) := hne
    simpa using (AutomatedTheoryConstruction.thm_op_000003 (α := α))
  · intro h
    refine ⟨⟨⊠(⊤ : α), ?_⟩⟩
    simpa using h


theorem thm_op_000011 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, g.1 ≡ h.1 := by
  intro α _ _ _ _ _
  intro g h
  have hg := ACR.gf_equiv_reft_top (g := g)
  have hh := ACR.gf_equiv_reft_top (g := h)
  exact ⟨le_trans hg.1 hh.2, le_trans hh.1 hg.2⟩


theorem thm_op_000012 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g : ACR.GödelFixpoint α, ACR.Consistent α ↔ ¬ (g.1 ≤ (⊥ : α)) := by
  intro α _ _ _ _ _ g
  constructor
  · intro hC
    exact AutomatedTheoryConstruction.thm_op_000005 (g := g) hC
  · intro hg
    intro hI
    exact hg (le_trans (ACR.le_top (x := g.1)) hI)


theorem thm_op_000013 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ∀ x : α, ⊠(⊥ : α) ≤ x → ¬ (x ≤ (⊥ : α)) := by
  intro α hACR hProv hReft hAPS hC x hx hx0
  apply hC
  change (⊤ : α) ≤ (⊥ : α)
  calc
    (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
    _ ≤ x := hx
    _ ≤ (⊥ : α) := hx0


theorem thm_op_000014 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ g : ACR.GödelFixpoint α, ACR.Consistent α → ¬ (□(g.1) ≤ (⊥ : α)) := by
  intro α hACR hProv hReft hAPS g hC hbox
  have hg : g.1 ≤ □g.1 := le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))
  have hg0 : g.1 ≤ (⊥ : α) := le_trans hg hbox
  exact (AutomatedTheoryConstruction.thm_op_000005 (g := g) hC) hg0


theorem thm_op_000016 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∃ h : α, h ≤ □h ∧ □h ≤ h) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _
  rintro ⟨h, hle, hge⟩
  exact ⟨⟨h, ⟨hle, hge⟩⟩⟩


theorem thm_op_000006_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], Nonempty (ACR.GödelFixpoint α) → Nonempty (ACR.HenkinFixpoint α)) := by
  intro h
  letI : LE (ULift Int) := ⟨fun x y => x.down ≤ y.down⟩
  letI : LT (ULift Int) := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩
  letI : Top (ULift Int) := ⟨⟨0⟩⟩
  letI : Bot (ULift Int) := ⟨⟨0⟩⟩
  let acrInst : ACR (ULift Int) :=
    { toTop := inferInstance
      toBot := inferInstance
      toLE := inferInstance
      toLT := inferInstance
      le_refl := by
        intro a
        change a.down ≤ a.down
        omega
      le_trans := by
        intro a b c hab hbc
        change a.down ≤ b.down at hab
        change b.down ≤ c.down at hbc
        change a.down ≤ c.down
        omega
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  letI : ACR (ULift Int) := acrInst
  let provInst : ACR.Prov (ULift Int) :=
    { prov := fun x => ⟨x.down + 1⟩ }
  letI : ACR.Prov (ULift Int) := provInst
  let reftInst : ACR.Reft (ULift Int) :=
    { reft := fun _ => ⟨0⟩ }
  letI : ACR.Reft (ULift Int) := reftInst
  let apsInst : ACR.APS (ULift Int) :=
    { prov_mono := by
        intro x y hxy
        change x.down ≤ y.down at hxy
        change x.down + 1 ≤ y.down + 1
        omega
      reft_anti_mono := by
        intro x y hxy
        change (0 : Int) ≤ 0
        omega
      top_le_reft_bot := by
        change (0 : Int) ≤ 0
        omega
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxr
        change x.down ≤ 0 at hxr
        change x.down ≤ 0
        exact hxr
      reft_le_prov_reft := by
        intro x
        change (0 : Int) ≤ 1
        omega }
  letI : ACR.APS (ULift Int) := apsInst
  have hG : Nonempty (ACR.GödelFixpoint (ULift Int)) := by
    refine ⟨⟨⟨0⟩, ?_⟩⟩
    constructor
    · change (0 : Int) ≤ 0
      omega
    · change (0 : Int) ≤ 0
      omega
  rcases h (α := ULift Int) hG with ⟨hH⟩
  have hcontra : hH.1.down + 1 ≤ hH.1.down := by
    change (□hH.1).down ≤ hH.1.down
    exact hH.2.2
  omega


theorem thm_op_000017 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x y : α}, x ≡ y → □x ≡ □y := by
  intro α _ _ _ _ x y h
  exact ⟨ACR.prov_mono h.1, ACR.prov_mono h.2⟩


theorem thm_op_000018 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, ACR.Equivalent (□g.1) (□h.1) := by
  intro α _ _ _ _ _ g h
  have hg : □g.1 ≡ □(⊠⊤ : α) := by
    exact ⟨ACR.prov_mono (ACR.gf_equiv_reft_top (g := g)).1, ACR.prov_mono (ACR.gf_equiv_reft_top (g := g)).2⟩
  have hh : □h.1 ≡ □(⊠⊤ : α) := by
    exact ⟨ACR.prov_mono (ACR.gf_equiv_reft_top (g := h)).1, ACR.prov_mono (ACR.gf_equiv_reft_top (g := h)).2⟩
  exact ⟨le_trans hg.1 hh.2, le_trans hh.1 hg.2⟩


theorem thm_op_000019 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ACR.Consistent α ↔ ¬ (□(⊠(⊤ : α)) ≤ (⊥ : α)) := by
  intro α _ _ _ _ _ _
  constructor
  · intro h hbox
    exact (ACR.irrefutable_reft_top (α := α) h) (le_trans (ACR.reft_le_prov_reft (x := (⊤ : α))) hbox)
  · intro h hinc
    apply h
    exact le_trans (ACR.le_top (x := □(⊠(⊤ : α)))) hinc


theorem thm_op_000020 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x y : α}, ACR.Equivalent x y → ACR.Equivalent (ACR.Reft.reft x) (ACR.Reft.reft y) := by
  intro α _ _ _ _ x y h
  exact ⟨ACR.reft_anti_mono h.2, ACR.reft_anti_mono h.1⟩


theorem thm_op_000021 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ¬ ACR.Consistent α ↔ ∀ x : α, x ≤ (⊥ : α) := by
  intro α _ _ _ _ _
  constructor
  · intro h x
    have htop : (⊤ : α) ≤ (⊥ : α) := by
      classical
      change ¬¬ ((⊤ : α) ≤ (⊥ : α)) at h
      exact Classical.not_not.mp h
    exact le_trans ACR.le_top htop
  · intro h hc
    exact hc (h ⊤)


theorem thm_op_000022 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α ↔ ¬ ((⊠(⊥ : α)) ≤ (⊥ : α)) := by
  intro α _ _ _ _ _
  constructor
  · intro hC hbot
    apply hC
    change (⊤ : α) ≤ (⊥ : α)
    exact le_trans ACR.top_le_reft_bot hbot
  · intro h hinc
    exact h (le_trans (ACR.le_top (x := ⊠(⊥ : α))) hinc)


theorem thm_op_000023 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ x : α, ACR.Equivalent (⊠(⊠x)) (⊠(⊤ : α)) := by
  intro α instA instP instR instAPS instC5 hg x
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  constructor
  · have hx : x ≤ (⊤ : α) := ACR.le_top
    have htx : ⊠(⊤ : α) ≤ ⊠x := ACR.reft_anti_mono hx
    have hxx : ⊠(⊠x) ≤ ⊠(⊠(⊤ : α)) := ACR.reft_anti_mono htx
    exact le_trans hxx (by simpa using (ACR.reft_reft_top_le_reft_top (α := α)))
  · have hx : ⊠x ≤ (⊤ : α) := ACR.le_top
    exact ACR.reft_anti_mono hx


theorem thm_op_000024 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ x y : α, ⊠(⊤ : α) ≤ x → ⊠(⊤ : α) ≤ y → ACR.Equivalent (⊠x) (⊠y) := by
  intro α hA hP hR hAPS hC5 hg x y hx hy
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  constructor
  · calc
      ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono hx
      _ ≤ ⊠(⊤ : α) := ACR.reft_reft_top_le_reft_top (α := α)
      _ ≤ ⊠y := ACR.reft_anti_mono (ACR.le_top (x := y))
  · calc
      ⊠y ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono hy
      _ ≤ ⊠(⊤ : α) := ACR.reft_reft_top_le_reft_top (α := α)
      _ ≤ ⊠x := ACR.reft_anti_mono (ACR.le_top (x := x))


theorem thm_op_000026 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) ↔ ACR.Equivalent (⊠(⊤ : α)) (⊠⊠(⊤ : α)) := by
  intro α _ _ _ _ _
  constructor
  · intro hne
    letI : Nonempty (ACR.GödelFixpoint α) := hne
    simpa using (AutomatedTheoryConstruction.thm_op_000003 (α := α))
  · intro h
    refine ⟨⟨⊠(⊤ : α), ?_⟩⟩
    simpa using h


theorem thm_op_000027 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, ACR.Equivalent g.1 h.1 := by
  intro α _ _ _ _ _ g h
  show g.1 ≤ h.1 ∧ h.1 ≤ g.1
  constructor
  · exact le_trans (ACR.gf_equiv_reft_top (g := g)).1 (ACR.gf_equiv_reft_top (g := h)).2
  · exact le_trans (ACR.gf_equiv_reft_top (g := h)).1 (ACR.gf_equiv_reft_top (g := g)).2


theorem thm_op_000029 : ∀ {α : Type*} [ACR α], ACR.Consistent α ↔ ∀ x : α, (⊤ : α) ≤ x → ¬ (x ≤ (⊥ : α)) := by
  intro α
  intro _
  constructor
  · intro h x htx hxb
    exact h (le_trans htx hxb)
  · intro h htopbot
    exact h (⊥ : α) htopbot le_rfl


theorem thm_op_000030 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ x : α, ⊠(⊥ : α) ≤ x → (⊤ : α) ≤ x := by
  intro α _ _ _ _ x hx
  exact le_trans ACR.top_le_reft_bot hx


theorem thm_op_000031 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ g : ACR.GödelFixpoint α, □(g.1) ≤ □(□(g.1)) := by
  intro α _ _ _ _
  intro g
  apply ACR.prov_mono
  exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))


theorem thm_op_000032 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∀ x : α, ACR.Prov.prov (ACR.Prov.prov x) ≤ ACR.Prov.prov x) → Nonempty (ACR.GödelFixpoint α) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ hprov hg
  obtain ⟨g⟩ := hg
  refine ⟨⟨ACR.Prov.prov g.1, ?_⟩⟩
  constructor
  · simpa using ACR.prov_mono (thm_op_000001 g)
  · simpa using hprov g.1


theorem thm_op_000033 : ∃ (hA : ACR Int) (hP : @ACR.Prov Int hA) (hR : @ACR.Reft Int hA) (hAPS : @ACR.APS Int hA hP hR), (∀ x y : Int, @LE.le Int hA.toLE x y ↔ x ≤ y) ∧ (@Top.top Int hA.toTop = 0) ∧ (@Bot.bot Int hA.toBot = 0) ∧ (∀ x : Int, @ACR.Prov.prov Int hA hP x = x + 1) ∧ (∀ x : Int, @ACR.Reft.reft Int hA hR x = 0) := by
  let hA : ACR Int :=
    { toTop := ⟨0⟩
      toBot := ⟨0⟩
      toLE := inferInstance
      toLT := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩
      le_refl := by
        intro a
        change a ≤ a
        omega
      le_trans := by
        intro a b c hab hbc
        change a ≤ b at hab
        change b ≤ c at hbc
        change a ≤ c
        omega
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  let hP : @ACR.Prov Int hA :=
    { prov := fun x => x + 1 }
  let hR : @ACR.Reft Int hA :=
    { reft := fun _ => 0 }
  let hAPS : @ACR.APS Int hA hP hR :=
    { prov_mono := by
        intro x y hxy
        change x + 1 ≤ y + 1
        omega
      reft_anti_mono := by
        intro x y hxy
        change (0 : Int) ≤ 0
        omega
      top_le_reft_bot := by
        change (0 : Int) ≤ 0
        omega
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxr
        change x ≤ 0 at hxr
        change x ≤ 0
        exact hxr
      reft_le_prov_reft := by
        intro x
        change (0 : Int) ≤ 1
        omega }
  refine ⟨hA, hP, hR, hAPS, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · rfl
  · rfl
  · intro x
    rfl
  · intro x
    rfl


theorem thm_op_000034 : ∀ (hA : ACR Int) (hP : @ACR.Prov Int hA) (hR : @ACR.Reft Int hA) (hAPS : @ACR.APS Int hA hP hR), (∀ x y : Int, @LE.le Int hA.toLE x y ↔ x ≤ y) → @Top.top Int hA.toTop = 0 → @Bot.bot Int hA.toBot = 0 → (∀ x : Int, @ACR.Prov.prov Int hA hP x = x + 1) → (∀ x : Int, @ACR.Reft.reft Int hA hR x = 0) → ¬ Nonempty (@ACR.HenkinFixpoint Int hA hP) := by
  intro hA hP hR hAPS hle htop hbot hprov hreft hne
  rcases hne with ⟨h⟩
  have hstep : h.1 + 1 ≤ h.1 := by
    have hle' : @ACR.Prov.prov Int hA hP h.1 ≤ h.1 := by
      exact (hle (@ACR.Prov.prov Int hA hP h.1) h.1).1 h.2.2
    simpa [hprov h.1] using hle'
  omega


theorem thm_op_000035 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], Nonempty (ACR.HenkinFixpoint α) ↔ ∃ h : α, ACR.Equivalent h (□h) := by
  intro α _ _ _ _
  constructor
  · rintro ⟨h⟩
    exact ⟨h.1, h.2⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨h, hh⟩⟩


theorem thm_op_000036 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ h : ACR.HenkinFixpoint α, ACR.Equivalent (□h.1) (□(□h.1)) := by
  intro α _ _ _ _ h
  constructor
  · exact ACR.prov_mono h.2.1
  · exact ACR.prov_mono h.2.2


theorem thm_op_000037 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∃ g : ACR.GödelFixpoint α, □(□g.1) ≤ □g.1) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ h
  rcases h with ⟨g, hg⟩
  refine ⟨⟨□g.1, ?_⟩⟩
  constructor
  · exact ACR.prov_mono (le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g)))
  · exact hg


theorem thm_op_000039 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x y : α}, ACR.Equivalent x y → (ACR.Equivalent x (ACR.Prov.prov x) ↔ ACR.Equivalent y (ACR.Prov.prov y)) := by
  intro α _ _ _ _ x y h
  rcases h with ⟨hxy, hyx⟩
  have hprovxy : ACR.Prov.prov x ≤ ACR.Prov.prov y := ACR.prov_mono hxy
  have hprovyx : ACR.Prov.prov y ≤ ACR.Prov.prov x := ACR.prov_mono hyx
  constructor
  · intro hx
    rcases hx with ⟨hxp, hpx⟩
    constructor
    · exact le_trans hyx (le_trans hxp hprovxy)
    · exact le_trans hprovyx (le_trans hpx hxy)
  · intro hy
    rcases hy with ⟨hyp, hpy⟩
    constructor
    · exact le_trans hxy (le_trans hyp hprovyx)
    · exact le_trans hprovxy (le_trans hpy hyx)


theorem thm_op_000040_is_false : ¬(∀ {α : Type*} [ACR α] [PartialOrder α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ h : ACR.HenkinFixpoint α, h.1 = □h.1) := by
  intro hstmt
  letI : Top (ULift Bool) := ⟨⟨true⟩⟩
  letI : Bot (ULift Bool) := ⟨⟨false⟩⟩
  letI : LE (ULift Bool) := ⟨fun _ _ => True⟩
  letI : LT (ULift Bool) := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩
  let acrInst : ACR (ULift Bool) :=
    { toTop := inferInstance
      toBot := inferInstance
      toLE := inferInstance
      toLT := inferInstance
      le_refl := by
        intro _
        trivial
      le_trans := by
        intro _ _ _ _ _
        trivial
      lt_iff_le_not_ge := by
        intro _ _
        rfl }
  letI : ACR (ULift Bool) := acrInst
  letI : ACR.Prov (ULift Bool) := ⟨fun _ => ⟨true⟩⟩
  letI : ACR.Reft (ULift Bool) := ⟨fun _ => ⟨false⟩⟩
  letI : ACR.APS (ULift Bool) :=
    { prov_mono := by
        intro _ _ _
        trivial
      reft_anti_mono := by
        intro _ _ _
        trivial
      top_le_reft_bot := by
        trivial
      le_reft_top_of_le_prov_of_le_reft := by
        intro _ _ _ _
        trivial
      reft_le_prov_reft := by
        intro _
        trivial }
  let h : ACR.HenkinFixpoint (ULift Bool) := ⟨⟨false⟩, by
    constructor <;> trivial⟩
  let poInst : PartialOrder (ULift Bool) :=
    { toLE := ⟨fun x y => x = y⟩
      toLT := ⟨fun _ _ => False⟩
      le_refl := by
        intro x
        rfl
      le_trans := by
        intro a b c hab hbc
        simpa [hab] using hbc
      le_antisymm := by
        intro a b hab _
        exact hab
      lt_iff_le_not_ge := by
        intro a b
        constructor
        · intro hlt
          cases hlt
        · intro hne
          exact False.elim (hne.2 hne.1.symm) }
  letI : PartialOrder (ULift Bool) := poInst
  have hEq := hstmt (α := ULift Bool) h
  change (⟨false⟩ : ULift Bool) = ⟨true⟩ at hEq
  cases hEq


theorem thm_op_000042 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g : ACR.GödelFixpoint α, ACR.Consistent α ↔ ¬ (□g.1 ≤ (⊥ : α)) := by
  intro α _ _ _ _ _ g
  constructor
  . intro hC hbox
    have hg_bot : g.1 ≤ (⊥ : α) := by
      calc
        g.1 ≤ ⊠g.1 := g.2.1
        _ ≤ □g.1 := ACR.reft_gf_le_box_gf
        _ ≤ ⊥ := hbox
    apply hC
    calc
      (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
      _ ≤ ⊠g.1 := ACR.reft_anti_mono hg_bot
      _ ≤ g.1 := g.2.2
      _ ≤ ⊥ := hg_bot
  . intro hbox hinc
    apply hbox
    exact le_trans ACR.le_top hinc


theorem thm_op_000043 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ∀ x : α, ⊠(⊤ : α) ≤ x → (ACR.Consistent α ↔ ¬ (x ≤ (⊥ : α))) := by
  intro α _ _ _ _ _ _ x hx
  constructor
  · intro hcons hxbot
    exact (ACR.irrefutable_reft_top (α := α) hcons) (le_trans hx hxbot)
  · intro hnot
    intro htopbot
    apply hnot
    exact le_trans (ACR.le_top (x := x)) htopbot


theorem thm_op_000044 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x y : α}, ACR.Equivalent x y → (ACR.Equivalent x (ACR.Reft.reft x) ↔ ACR.Equivalent y (ACR.Reft.reft y)) := by
  intro α _ _ _ _ x y hxy
  rcases hxy with ⟨hxy1, hxy2⟩
  constructor
  · intro hx
    rcases hx with ⟨hx1, hx2⟩
    constructor
    · exact le_trans hxy2 (le_trans hx1 (ACR.reft_anti_mono hxy2))
    · exact le_trans (ACR.reft_anti_mono hxy1) (le_trans hx2 hxy1)
  · intro hy
    rcases hy with ⟨hy1, hy2⟩
    constructor
    · exact le_trans hxy1 (le_trans hy1 (ACR.reft_anti_mono hxy1))
    · exact le_trans (ACR.reft_anti_mono hxy2) (le_trans hy2 hxy2)


theorem thm_op_000046 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ¬ ACR.Consistent α ↔ ∀ x : α, □x ≤ (⊥ : α) := by
  intro α _ _ _ _ _
  constructor
  · intro h x
    change ¬ ¬ ((⊤ : α) ≤ (⊥ : α)) at h
    have htopbot : (⊤ : α) ≤ (⊥ : α) := by
      classical
      exact not_not.mp h
    have hx : □x ≤ (⊤ : α) := ACR.le_top
    exact le_trans hx htopbot
  · intro h
    change ¬ ¬ ((⊤ : α) ≤ (⊥ : α))
    intro hC
    apply hC
    calc
      (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
      _ ≤ □(⊠(⊥ : α)) := ACR.reft_le_prov_reft
      _ ≤ (⊥ : α) := h (⊠(⊥ : α))


theorem thm_op_000047 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (ACR.Reft.reft (⊥ : α) ≤ (⊤ : α)) → (ACR.Consistent α ↔ ¬ (ACR.Reft.reft (⊥ : α) ≤ (⊥ : α))) := by
  intro α _ _ _ _ hbot
  constructor
  · intro hcons hreftbot
    exact hcons (le_trans ACR.top_le_reft_bot hreftbot)
  · intro hnot
    simpa [ACR.Consistent, ACR.Inconsistent] using
      (show ¬ ((⊤ : α) ≤ (⊥ : α)) from fun hinc => hnot (le_trans hbot hinc))


theorem thm_op_000048 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Equivalent (⊠(⊥ : α)) (⊤ : α) := by
  intro α _ _ _ _ _
  change (⊠(⊥ : α) ≤ (⊤ : α)) ∧ ((⊤ : α) ≤ ⊠(⊥ : α))
  exact ⟨ACR.le_top (x := ⊠(⊥ : α)), ACR.top_le_reft_bot (α := α)⟩


theorem thm_op_000050 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ x y : α, ACR.Equivalent (⊠(⊠x)) (⊠(⊠y)) := by
  intro α _ _ _ _ _ hG x y
  letI : Nonempty (ACR.GödelFixpoint α) := hG
  have hxx_top : ⊠(⊠x) ≤ ⊠(⊤ : α) := by
    have hx_top : x ≤ (⊤ : α) := ACR.le_top
    have htop_reftx : ⊠(⊤ : α) ≤ ⊠x := ACR.reft_anti_mono hx_top
    have hxx : ⊠(⊠x) ≤ ⊠(⊠(⊤ : α)) := ACR.reft_anti_mono htop_reftx
    exact le_trans hxx (ACR.reft_reft_top_le_reft_top (α := α))
  have hyy_top : ⊠(⊠y) ≤ ⊠(⊤ : α) := by
    have hy_top : y ≤ (⊤ : α) := ACR.le_top
    have htop_refty : ⊠(⊤ : α) ≤ ⊠y := ACR.reft_anti_mono hy_top
    have hyy : ⊠(⊠y) ≤ ⊠(⊠(⊤ : α)) := ACR.reft_anti_mono htop_refty
    exact le_trans hyy (ACR.reft_reft_top_le_reft_top (α := α))
  have htop_xx : ⊠(⊤ : α) ≤ ⊠(⊠x) := by
    exact ACR.reft_anti_mono (ACR.le_top : ⊠x ≤ (⊤ : α))
  have htop_yy : ⊠(⊤ : α) ≤ ⊠(⊠y) := by
    exact ACR.reft_anti_mono (ACR.le_top : ⊠y ≤ (⊤ : α))
  constructor
  · exact le_trans hxx_top htop_yy
  · exact le_trans hyy_top htop_xx


theorem thm_op_000051 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ x : α, ⊠(⊤ : α) ≤ x → ∀ g : ACR.GödelFixpoint α, ACR.Equivalent (⊠x) g.1 := by
  intro α _ _ _ _ _ hg x hx g
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  constructor
  · calc
      ⊠x ≤ ⊠(⊠(⊤ : α)) := ACR.reft_anti_mono hx
      _ ≤ ⊠(⊤ : α) := ACR.reft_reft_top_le_reft_top (α := α)
      _ ≤ g.1 := (ACR.gf_equiv_reft_top (g := g)).2
  · calc
      g.1 ≤ ⊠(⊤ : α) := (ACR.gf_equiv_reft_top (g := g)).1
      _ ≤ ⊠x := by
        apply ACR.reft_anti_mono
        exact ACR.le_top


theorem thm_op_000053 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → ∀ g h : ACR.GödelFixpoint α, g = h := by
  intro α _ _ _ _ _ hantisym g h
  apply Subtype.ext
  exact hantisym
    (le_trans (ACR.gf_equiv_reft_top (g := g)).1 (ACR.gf_equiv_reft_top (g := h)).2)
    (le_trans (ACR.gf_equiv_reft_top (g := h)).1 (ACR.gf_equiv_reft_top (g := g)).2)


theorem thm_op_000025_is_false : ¬(∀ {α : Type*} [ACR α] [PartialOrder α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, g = h) := by
  intro hstmt
  letI : Top (ULift Bool) := ⟨⟨true⟩⟩
  letI : Bot (ULift Bool) := ⟨⟨false⟩⟩
  letI : LE (ULift Bool) := ⟨fun _ _ => True⟩
  letI : LT (ULift Bool) := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩
  let acrInst : ACR (ULift Bool) :=
    { toTop := inferInstance
      toBot := inferInstance
      toLE := inferInstance
      toLT := inferInstance
      le_refl := by
        intro _
        trivial
      le_trans := by
        intro _ _ _ _ _
        trivial
      lt_iff_le_not_ge := by
        intro _ _
        rfl }
  letI : ACR (ULift Bool) := acrInst
  letI : ACR.Prov (ULift Bool) := ⟨fun x => x⟩
  letI : ACR.Reft (ULift Bool) := ⟨fun x => x⟩
  letI : ACR.APS (ULift Bool) :=
    { prov_mono := by
        intro _ _ _
        trivial
      reft_anti_mono := by
        intro _ _ _
        trivial
      top_le_reft_bot := by
        trivial
      le_reft_top_of_le_prov_of_le_reft := by
        intro _ _ _ _
        trivial
      reft_le_prov_reft := by
        intro _
        trivial }
  letI : ACR.C5 (ULift Bool) :=
    { le_top := by
        intro _
        trivial }
  let g : ACR.GödelFixpoint (ULift Bool) := ⟨⟨false⟩, by
    constructor <;> trivial⟩
  let h : ACR.GödelFixpoint (ULift Bool) := ⟨⟨true⟩, by
    constructor <;> trivial⟩
  let poInst : PartialOrder (ULift Bool) :=
    { toLE := ⟨fun x y => x = y⟩
      toLT := ⟨fun _ _ => False⟩
      le_refl := by
        intro x
        rfl
      le_trans := by
        intro a b c hab hbc
        simpa [hab] using hbc
      le_antisymm := by
        intro a b hab _
        exact hab
      lt_iff_le_not_ge := by
        intro a b
        constructor
        · intro hlt
          cases hlt
        · intro hne
          exact False.elim (hne.2 hne.1.symm) }
  letI : PartialOrder (ULift Bool) := poInst
  have hVal : g.1 = h.1 := congrArg Subtype.val (hstmt (α := ULift Bool) g h)
  change (⟨false⟩ : ULift Bool) = ⟨true⟩ at hVal
  cases hVal


theorem thm_op_000055 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) ↔ ACR.Equivalent (⊠(⊤ : α)) (⊠(⊠(⊤ : α))) := by
  intro α _ _ _ _ _
  simpa using (AutomatedTheoryConstruction.thm_op_000026 (α := α))


theorem thm_op_000056 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ x : α, ACR.Equivalent x (⊠(⊤ : α)) → ACR.Equivalent x (⊠x) := by
  intro α _ _ _ _ _ hg x hx
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  constructor
  · calc
      x ≤ ⊠(⊤ : α) := hx.1
      _ ≤ ⊠x := ACR.reft_anti_mono (ACR.le_top (x := x))
  · calc
      ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono hx.2
      _ ≤ ⊠(⊤ : α) := ACR.reft_reft_top_le_reft_top (α := α)
      _ ≤ x := hx.2


theorem thm_op_000057 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x y : α}, ACR.Equivalent x y → ACR.Equivalent (ACR.Reft.reft x) (ACR.Reft.reft y) := by
  intro α _ _ _ _ x y h
  exact ⟨ACR.reft_anti_mono h.2, ACR.reft_anti_mono h.1⟩


theorem thm_op_000058 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ∀ x : α, (∃ g : ACR.GödelFixpoint α, ACR.Equivalent x g.1) ↔ ACR.Equivalent x (ACR.Reft.reft (⊤ : α)) := by
  intro α _ _ _ _ _ _ x
  constructor
  · rintro ⟨g, hxg⟩
    have hg : ACR.Equivalent g.1 (ACR.Reft.reft (⊤ : α)) := ACR.gf_equiv_reft_top (g := g)
    exact ⟨le_trans hxg.1 hg.1, le_trans hg.2 hxg.2⟩
  · intro hxt
    obtain ⟨g⟩ := (‹Nonempty (ACR.GödelFixpoint α)› : Nonempty (ACR.GödelFixpoint α))
    have hg : ACR.Equivalent g.1 (ACR.Reft.reft (⊤ : α)) := ACR.gf_equiv_reft_top (g := g)
    refine ⟨g, ?_⟩
    exact ⟨le_trans hxt.1 hg.2, le_trans hg.1 hxt.2⟩


theorem thm_op_000059 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (∀ {x y : α}, ACR.Equivalent x y → x = y) → ∀ g : ACR.GödelFixpoint α, g.1 = ⊠(⊤ : α) := by
  intro α _ _ _ _ _ hEq g
  exact hEq (x := g.1) (y := ⊠(⊤ : α)) (ACR.gf_equiv_reft_top (g := g))


theorem thm_op_000060 : ∃ (α : Type*) (_ : ACR α) (_ : PartialOrder α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α) (_ : ACR.C5 α), ∃ g : ACR.GödelFixpoint α, ACR.Equivalent g.1 (⊠(⊤ : α)) ∧ g.1 ≠ ⊠(⊤ : α) := by
  let hPO : PartialOrder (ULift Bool) :=
    { le := Eq
      lt := fun a b => a = b ∧ ¬ b = a
      le_refl := by intro a; rfl
      le_trans := by intro a b c hab hbc; exact hab.trans hbc
      lt_iff_le_not_ge := by intro a b; rfl
      le_antisymm := by intro a b hab _; exact hab }
  let hA : ACR (ULift Bool) :=
    { toTop := ⟨⟨true⟩⟩
      toBot := ⟨⟨false⟩⟩
      toPreorder :=
        { le := fun _ _ => True
          lt := fun _ _ => True ∧ ¬ True
          le_refl := by intro _; trivial
          le_trans := by intro _ _ _ _ _; trivial
          lt_iff_le_not_ge := by intro _ _; rfl } }
  letI : ACR (ULift Bool) := hA
  let hP : ACR.Prov (ULift Bool) := { prov := fun x => x }
  letI : ACR.Prov (ULift Bool) := hP
  let hR : ACR.Reft (ULift Bool) := { reft := fun x => x }
  letI : ACR.Reft (ULift Bool) := hR
  let hAPS : ACR.APS (ULift Bool) :=
    { prov_mono := by intro _ _ _; trivial
      reft_anti_mono := by intro _ _ _; trivial
      top_le_reft_bot := by trivial
      le_reft_top_of_le_prov_of_le_reft := by intro _ _ _ _; trivial
      reft_le_prov_reft := by intro _; trivial }
  letI : ACR.APS (ULift Bool) := hAPS
  let hC5 : ACR.C5 (ULift Bool) := { le_top := by intro _; trivial }
  let g : ACR.GödelFixpoint (ULift Bool) := ⟨⟨false⟩, by constructor <;> trivial⟩
  exact ⟨ULift Bool, hA, hPO, hP, hR, hAPS, hC5, g, by
    constructor
    · constructor <;> trivial
    · change (⟨false⟩ : ULift Bool) ≠ ⟨true⟩
      decide⟩


theorem thm_op_000062 : ∃ (α : Type*) (_ : ACR α), ACR.Consistent α ∧ ∃ x : α, ¬ ((⊤ : α) ≤ x) ∧ ¬ (x ≤ (⊥ : α)) := by
  let acr : ACR (ULift (Sum Unit Bool)) :=
    { toTop := ⟨⟨Sum.inl ()⟩⟩
      toBot := ⟨⟨Sum.inr false⟩⟩
      toPreorder :=
        { le := Eq
          lt := fun a b => a = b ∧ ¬ b = a
          le_refl := by
            intro a
            rfl
          le_trans := by
            intro a b c hab hbc
            exact hab.trans hbc
          lt_iff_le_not_ge := by
            intro a b
            rfl } }
  refine ⟨ULift (Sum Unit Bool), acr, ?_⟩
  letI : ACR (ULift (Sum Unit Bool)) := acr
  refine ⟨?_, ⟨⟨Sum.inr true⟩, ?_, ?_⟩⟩
  · intro h
    change (⟨Sum.inl ()⟩ : ULift (Sum Unit Bool)) = ⟨Sum.inr false⟩ at h
    cases h
  · intro h
    change (⟨Sum.inl ()⟩ : ULift (Sum Unit Bool)) = ⟨Sum.inr true⟩ at h
    cases h
  · intro h
    change (⟨Sum.inr true⟩ : ULift (Sum Unit Bool)) = ⟨Sum.inr false⟩ at h
    cases h


theorem thm_op_000063_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ x : α, ACR.Reft.reft (⊥ : α) ≤ x → (ACR.Consistent α ↔ ¬ (x ≤ (⊥ : α)))) := by
  intro h
  letI : LE (ULift Int) := ⟨fun x y => x.down ≤ y.down⟩
  letI : LT (ULift Int) := ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩
  letI : Top (ULift Int) := ⟨⟨0⟩⟩
  letI : Bot (ULift Int) := ⟨⟨0⟩⟩
  let acrInst : ACR (ULift Int) :=
    { toTop := inferInstance
      toBot := inferInstance
      toLE := inferInstance
      toLT := inferInstance
      le_refl := by
        intro a
        change a.down ≤ a.down
        omega
      le_trans := by
        intro a b c hab hbc
        change a.down ≤ b.down at hab
        change b.down ≤ c.down at hbc
        change a.down ≤ c.down
        omega
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  letI : ACR (ULift Int) := acrInst
  let provInst : ACR.Prov (ULift Int) :=
    { prov := fun x => ⟨x.down + 1⟩ }
  letI : ACR.Prov (ULift Int) := provInst
  let reftInst : ACR.Reft (ULift Int) :=
    { reft := fun _ => ⟨0⟩ }
  letI : ACR.Reft (ULift Int) := reftInst
  let apsInst : ACR.APS (ULift Int) :=
    { prov_mono := by
        intro x y hxy
        change x.down ≤ y.down at hxy
        change x.down + 1 ≤ y.down + 1
        omega
      reft_anti_mono := by
        intro x y hxy
        change (0 : Int) ≤ 0
        omega
      top_le_reft_bot := by
        change (0 : Int) ≤ 0
        omega
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxr
        change x.down ≤ 0 at hxr
        change x.down ≤ 0
        exact hxr
      reft_le_prov_reft := by
        intro x
        change (0 : Int) ≤ 1
        omega }
  letI : ACR.APS (ULift Int) := apsInst
  have hiff := h (α := ULift Int) ⟨1⟩ (by
    change (0 : Int) ≤ 1
    omega)
  have hnot : ¬ ((⟨1⟩ : ULift Int) ≤ (⊥ : ULift Int)) := by
    change ¬ ((1 : Int) ≤ 0)
    omega
  have hC : ACR.Consistent (ULift Int) := hiff.mpr hnot
  exact hC (by
    change (0 : Int) ≤ 0
    omega)


theorem thm_op_000064 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (ACR.Reft.reft (⊥ : α) ≤ (⊤ : α)) ↔ ∀ x : α, (ACR.Reft.reft (⊥ : α) ≤ x ↔ (⊤ : α) ≤ x) := by
  intro α _ _ _ _
  constructor
  · intro h x
    constructor
    · intro hx
      exact le_trans ACR.top_le_reft_bot hx
    · intro hx
      exact le_trans h hx
  · intro h
    exact (h (⊤ : α)).2 le_rfl


theorem thm_op_000066 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ x : α, x ≤ ACR.Prov.prov x → ACR.Prov.prov (ACR.Prov.prov x) ≤ ACR.Prov.prov x → ACR.Equivalent (ACR.Prov.prov x) (ACR.Prov.prov (ACR.Prov.prov x)) := by
  intro α _ _ _ _ x hx hxx
  constructor
  · simpa using (ACR.prov_mono (x := x) (y := ACR.Prov.prov x) hx)
  · exact hxx


theorem thm_op_000067 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (∀ x : α, ACR.Prov.prov (ACR.Prov.prov x) ≤ ACR.Prov.prov x) → Nonempty (ACR.GödelFixpoint α) → ACR.Equivalent (ACR.Prov.prov (ACR.Reft.reft (⊤ : α))) (ACR.Prov.prov (ACR.Prov.prov (ACR.Reft.reft (⊤ : α)))) := by
  intro α hA hP hR hAPS hC5 hpp hgf
  constructor
  · have h1 : ACR.Reft.reft (⊤ : α) ≤ ACR.Prov.prov (ACR.Reft.reft (⊤ : α)) :=
      ACR.reft_le_prov_reft (x := (⊤ : α))
    exact ACR.prov_mono h1
  · simpa using hpp (ACR.Reft.reft (⊤ : α))


theorem thm_op_000068 : ∀ (hA : ACR Int) (hP : @ACR.Prov Int hA) (hR : @ACR.Reft Int hA) (hAPS : @ACR.APS Int hA hP hR), (∀ x y : Int, @LE.le Int hA.toLE x y ↔ x ≤ y) → @Top.top Int hA.toTop = 0 → @Bot.bot Int hA.toBot = 0 → (∀ x : Int, @ACR.Prov.prov Int hA hP x = x + 1) → (∀ x : Int, @ACR.Reft.reft Int hA hR x = 0) → ¬ @ACR.Consistent Int hA := by
  intro hA hP hR hAPS hle htop hbot hprov hreft
  intro hCons
  apply hCons
  simpa [ACR.Inconsistent, htop, hbot] using (hle 0 0).2 le_rfl


theorem thm_op_000069 : ∀ (hA : ACR Int) (hP : @ACR.Prov Int hA) (hR : @ACR.Reft Int hA) (hAPS : @ACR.APS Int hA hP hR), (∀ x y : Int, @LE.le Int hA.toLE x y ↔ x ≤ y) → @Top.top Int hA.toTop = 0 → @Bot.bot Int hA.toBot = 0 → (∀ x : Int, @ACR.Prov.prov Int hA hP x = x + 1) → (∀ x : Int, @ACR.Reft.reft Int hA hR x = 0) → ∀ g : @ACR.GödelFixpoint Int hA hR, g.1 = 0 := by
  intro hA hP hR hAPS hle _ _ _ hreft g
  have hg0 : g.1 ≤ 0 := by
    apply (hle g.1 0).mp
    simpa [hreft g.1] using g.2.1
  have h0g : 0 ≤ g.1 := by
    apply (hle 0 g.1).mp
    simpa [hreft g.1] using g.2.2
  exact Int.le_antisymm hg0 h0g


theorem thm_op_000070 : ∀ {α : Type*} [ACR α] [ACR.Prov α], (∀ x : α, ¬ (□x ≤ x)) → ¬ Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ hno hne
  rcases hne with ⟨h⟩
  exact hno h.1 h.2.2


theorem thm_op_000071 : ∀ (hA : ACR Int) (hP : @ACR.Prov Int hA) (hR : @ACR.Reft Int hA) (hAPS : @ACR.APS Int hA hP hR), (∀ x y : Int, @LE.le Int hA.toLE x y ↔ x ≤ y) → @Top.top Int hA.toTop = 0 → @Bot.bot Int hA.toBot = 0 → (∀ x : Int, @ACR.Prov.prov Int hA hP x = x + 1) → (∀ x : Int, @ACR.Reft.reft Int hA hR x = 0) → ¬ Nonempty (@ACR.C5 Int hA hP hR hAPS) := by
  intro hA hP hR hAPS hle htop hbot hprov hreft hne
  letI : ACR Int := hA
  letI : ACR.Prov Int := hP
  letI : ACR.Reft Int := hR
  letI : ACR.APS Int := hAPS
  letI : ACR.C5 Int := hne.some
  have h1 : @LE.le Int hA.toLE 1 (@Top.top Int hA.toTop) := by
    exact ACR.le_top (x := (1 : Int))
  have h1std : (1 : Int) ≤ @Top.top Int hA.toTop := (hle 1 (@Top.top Int hA.toTop)).1 h1
  have h2 : (1 : Int) ≤ 0 := by
    rwa [htop] at h1std
  have hfalse : ¬ ((1 : Int) ≤ 0) := by
    decide
  exact hfalse h2


theorem thm_op_000072 : ∀ (hA : ACR Int) (hP : @ACR.Prov Int hA) (hR : @ACR.Reft Int hA), (∀ x y : Int, @LE.le Int hA.toLE x y ↔ x ≤ y) → @Top.top Int hA.toTop = 0 → @Bot.bot Int hA.toBot = 0 → (∀ x : Int, @ACR.Prov.prov Int hA hP x = x + 1) → (∀ x : Int, @ACR.Reft.reft Int hA hR x = 0) → Nonempty (@ACR.APS Int hA hP hR) := by
  intro hA hP hR hle htop hbot hprov hreft
  refine ⟨{
    prov_mono := ?_,
    reft_anti_mono := ?_,
    top_le_reft_bot := ?_,
    le_reft_top_of_le_prov_of_le_reft := ?_,
    reft_le_prov_reft := ?_ }⟩
  · intro x y hxy
    rw [hprov x, hprov y]
    exact (hle (x + 1) (y + 1)).2 (Int.add_le_add_right ((hle x y).1 hxy) 1)
  · intro x y _
    rw [hreft y, hreft x]
  · rw [htop, hbot, hreft 0]
  · intro x y _ hxr
    rw [htop, hreft 0]
    rw [hreft y] at hxr
    exact hxr
  · intro x
    rw [hreft x, hprov 0]
    exact (hle 0 (0 + 1)).2 (show (0 : Int) ≤ 1 from Int.one_nonneg)


theorem thm_op_000073 : ∀ (hA : ACR Int) (hP : @ACR.Prov Int hA) (hR : @ACR.Reft Int hA) (hAPS : @ACR.APS Int hA hP hR), (∀ x y : Int, @LE.le Int hA.toLE x y ↔ x ≤ y) → @Top.top Int hA.toTop = 0 → @Bot.bot Int hA.toBot = 0 → (∀ x : Int, @ACR.Prov.prov Int hA hP x = x + 1) → (∀ x : Int, @ACR.Reft.reft Int hA hR x = 0) → ¬ Nonempty (@ACR.HenkinFixpoint Int hA hP) := by
  intro hA hP hR hAPS hle htop hbot hprov hreft hne
  rcases hne with ⟨h⟩
  have hstep : h.1 + 1 ≤ h.1 := by
    have hle' : @ACR.Prov.prov Int hA hP h.1 ≤ h.1 := by
      exact (hle (@ACR.Prov.prov Int hA hP h.1) h.1).1 h.2.2
    simpa [hprov h.1] using hle'
  omega


theorem thm_op_000015 : ∃ (α : Type*) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α), Nonempty (ACR.GödelFixpoint α) ∧ ¬ Nonempty (ACR.HenkinFixpoint α) := by
  classical
  exact Classical.byContradiction (fun h => thm_op_000006_is_false (by
    intro α _ _ _ _ hG
    exact Classical.byContradiction (fun hH =>
      h ⟨α, ‹ACR α›, ‹ACR.Prov α›, ‹ACR.Reft α›, ‹ACR.APS α›, ⟨hG, hH⟩⟩)))


theorem thm_op_000074_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∀ {x y : α}, x ≤ y → □y ≤ x → x ≡ □y) → ∀ h₁ h₂ : ACR.HenkinFixpoint α, h₁.1 ≡ h₂.1) := by
  intro hstmt
  letI : Top (ULift Bool) := ⟨⟨true⟩⟩
  letI : Bot (ULift Bool) := ⟨⟨false⟩⟩
  letI : LE (ULift Bool) := ⟨Eq⟩
  letI : LT (ULift Bool) := ⟨fun x y => x = y ∧ ¬ y = x⟩
  let acrInst : ACR (ULift Bool) :=
    { toTop := inferInstance
      toBot := inferInstance
      toLE := inferInstance
      toLT := inferInstance
      le_refl := by
        intro x
        rfl
      le_trans := by
        intro a b c hab hbc
        exact hab.trans hbc
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  letI : ACR (ULift Bool) := acrInst
  let provInst : ACR.Prov (ULift Bool) := ⟨fun x => x⟩
  letI : ACR.Prov (ULift Bool) := provInst
  let reftInst : ACR.Reft (ULift Bool) := ⟨fun _ => ⟨true⟩⟩
  letI : ACR.Reft (ULift Bool) := reftInst
  let apsInst : ACR.APS (ULift Bool) :=
    { prov_mono := by
        intro x y hxy
        simpa using hxy
      reft_anti_mono := by
        intro x y hxy
        rfl
      top_le_reft_bot := by
        rfl
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxr
        simpa using hxr
      reft_le_prov_reft := by
        intro x
        rfl }
  letI : ACR.APS (ULift Bool) := apsInst
  have hpred : ∀ {x y : ULift Bool}, x ≤ y → □y ≤ x → x ≡ □y := by
    intro x y hxy hyx
    constructor
    · simpa using hxy
    · exact hyx
  let hFalse : ACR.HenkinFixpoint (ULift Bool) := ⟨⟨false⟩, by
    constructor <;> rfl⟩
  let hTrue : ACR.HenkinFixpoint (ULift Bool) := ⟨⟨true⟩, by
    constructor <;> rfl⟩
  have hEq : hFalse.1 ≡ hTrue.1 := hstmt (α := ULift Bool) hpred hFalse hTrue
  have hVal : hFalse.1 = hTrue.1 := hEq.1
  change (⟨false⟩ : ULift Bool) = ⟨true⟩ at hVal
  cases hVal


theorem thm_op_000077 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∃ g : ACR.GödelFixpoint α, □(□(g.1)) ≤ □(g.1)) → ∃ h : ACR.HenkinFixpoint α, ∃ g : ACR.GödelFixpoint α, h.1 = □(g.1) := by
  intro α _ _ _ _ h
  rcases h with ⟨g, hg⟩
  refine ⟨⟨□(g.1), ?_⟩, g, rfl⟩
  constructor
  · exact ACR.prov_mono (le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g)))
  · exact hg


theorem thm_op_000078 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∃ g : ACR.GödelFixpoint α, □(□g.1) ≤ □g.1) → ∃ x : α, x ≡ □x ∧ ∃ g : ACR.GödelFixpoint α, x = □g.1 := by
  intro α _ _ _ _ h
  rcases h with ⟨g, hbox⟩
  refine ⟨□g.1, ?_, ⟨g, rfl⟩⟩
  constructor
  · exact ACR.prov_mono (le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g)))
  · exact hbox


theorem thm_op_000038 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ _ _
  refine ⟨⟨(⊤ : α), ?_⟩⟩
  constructor
  · calc
      (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
      _ ≤ □(⊠(⊥ : α)) := ACR.reft_le_prov_reft
      _ ≤ □(⊤ : α) := ACR.prov_mono (ACR.le_top (x := ⊠(⊥ : α)))
  · exact ACR.le_top


theorem thm_op_000081 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x y : α}, ACR.Equivalent x y → ACR.Equivalent (ACR.Prov.prov x) (ACR.Prov.prov y) := by
  intro α _ _ _ _ x y h
  exact And.intro (ACR.prov_mono h.1) (ACR.prov_mono h.2)


theorem thm_op_000082 : ∀ {α : Type*} [ACR α] {x y : α}, ACR.Equivalent x y → (((⊤ : α) ≤ x ↔ (⊤ : α) ≤ y) ∧ (x ≤ (⊥ : α) ↔ y ≤ (⊥ : α))) := by
  intro α _ x y h
  rcases h with ⟨hxy, hyx⟩
  constructor
  · constructor
    · intro hx
      exact le_trans hx hxy
    · intro hy
      exact le_trans hy hyx
  · constructor
    · intro hxbot
      exact le_trans hyx hxbot
    · intro hybot
      exact le_trans hxy hybot


theorem thm_op_000083 : ∀ {α : Type*} [ACR α] [ACR.Prov α], (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → ∀ h : ACR.HenkinFixpoint α, h.1 = □h.1 := by
  intro α _ _ hanti h
  exact hanti h.2.1 h.2.2


theorem thm_op_000084 : ∀ {α : Type*} (hA : ACR α) (hPO : PartialOrder α) (hP : @ACR.Prov α hA) (hR : @ACR.Reft α hA) (hAPS : @ACR.APS α hA hP hR), (∀ x y : α, @LE.le α hPO.toLE x y ↔ @LE.le α hA.toLE x y) → ∀ h : @ACR.HenkinFixpoint α hA hP, h.1 = @ACR.Prov.prov α hA hP h.1 := by
  intro α hA hPO hP hR hAPS hord h
  letI : PartialOrder α := hPO
  exact le_antisymm ((hord _ _).mpr h.2.1) ((hord _ _).mpr h.2.2)


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
