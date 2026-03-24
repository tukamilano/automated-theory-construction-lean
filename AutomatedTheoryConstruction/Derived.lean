import Mathlib.Logic.Function.Iterate
import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


theorem thm_double_reft_top_iff_godel_fixpoint_000001 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ↔ Nonempty (ACR.GödelFixpoint α) := by
  intro α _ _ _ _ _
  constructor
  · intro h
    exact ⟨⟨⊠(⊤ : α), ⟨h.2, h.1⟩⟩⟩
  · intro hg
    constructor
    · letI : Nonempty (ACR.GödelFixpoint α) := hg
      simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    · exact ACR.reft_anti_mono (ACR.le_top (x := ⊠(⊤ : α)))


theorem thm_equiv_reft_top_implies_reft_fixpoint_000002 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {x : α}, Nonempty (ACR.GödelFixpoint α) → x ≐ ⊠(⊤ : α) → x ≐ ⊠x := by
  intro α _ _ _ _ _ x hg hx
  change x ≤ ⊠x ∧ ⊠x ≤ x
  change x ≤ ⊠(⊤ : α) ∧ ⊠(⊤ : α) ≤ x at hx
  rcases hx with ⟨hxt, htx⟩
  constructor
  · have htop : x ≤ (⊤ : α) := ACR.le_top (α := α) (x := x)
    exact le_trans hxt (ACR.reft_anti_mono htop)
  · have hxx : ⊠x ≤ ⊠(⊠(⊤ : α)) := ACR.reft_anti_mono htx
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    have htop : ⊠(⊠(⊤ : α)) ≤ ⊠(⊤ : α) := ACR.reft_reft_top_le_reft_top (α := α)
    exact le_trans hxx (le_trans htop htx)


theorem thm_godel_fixpoint_box_irrefutable_000003 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ∀ g : ACR.GödelFixpoint α, ¬ (⊬ (□g.1)) := by
  intro α _ _ _ _ hCons g hbox
  apply hCons
  change (⊤ : α) ≤ ⊥
  have hg_bot : g.1 ≤ (⊥ : α) := by
    calc
      g.1 ≤ ⊠g.1 := g.2.1
      _ ≤ □g.1 := ACR.reft_gf_le_box_gf (g := g)
      _ ≤ ⊥ := hbox
  have hreft_bot : ⊠(⊥ : α) ≤ g.1 := by
    calc
      ⊠(⊥ : α) ≤ ⊠g.1 := ACR.reft_anti_mono hg_bot
      _ ≤ g.1 := g.2.2
  calc
    (⊤ : α) ≤ ⊠⊥ := ACR.top_le_reft_bot
    _ ≤ g.1 := hreft_bot
    _ ≤ ⊥ := hg_bot


theorem thm_henkin_fixpoint_le_reft_top_000004 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {h : ACR.HenkinFixpoint α}, h.1 ≤ ⊠h.1 → h.1 ≤ ⊠(⊤ : α) := by
  intro α _ _ _ _ h hh
  exact ACR.le_reft_top_of_le_prov_of_le_reft h.2.1 hh


theorem thm_reft_fixpoints_equivalent_000006 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {x y : α}, x ≐ ⊠x → y ≐ ⊠y → x ≐ y := by
  intro α _ _ _ _ _ x y hx hy
  let gx : ACR.GödelFixpoint α := ⟨x, hx⟩
  let gy : ACR.GödelFixpoint α := ⟨y, hy⟩
  have hx' : x ≐ ⊠(⊤ : α) := ACR.gf_equiv_reft_top (g := gx)
  have hy' : y ≐ ⊠(⊤ : α) := ACR.gf_equiv_reft_top (g := gy)
  constructor
  · exact le_trans hx'.1 hy'.2
  · exact le_trans hy'.1 hx'.2


theorem thm_equiv_reft_top_irrefutable_000007 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {x : α}, ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → x ≐ ⊠(⊤ : α) → ¬ (⊬ x) := by
  intro α _ _ _ _ _ x hC hg hx
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  intro hxr
  exact ACR.irrefutable_reft_top (α := α) hC (le_trans hx.2 hxr)


theorem thm_godel_fixpoint_irrefutable_000008 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ∀ g : ACR.GödelFixpoint α, ¬ (⊬ g.1) := by
  intro α _ _ _ _ hC g hg
  apply hC
  change (⊤ : α) ≤ ⊥
  have h₁ : ⊠(⊥ : α) ≤ ⊠g.1 := ACR.reft_anti_mono hg
  have h₂ : ⊠(⊥ : α) ≤ g.1 := le_trans h₁ g.2.2
  calc
    (⊤ : α) ≤ ⊠⊥ := ACR.top_le_reft_bot
    _ ≤ g.1 := h₂
    _ ≤ ⊥ := hg


theorem thm_box_reft_top_irrefutable_000009 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → ¬ (⊬ (□(⊠(⊤ : α)))) := by
  intro α _ _ _ _ _ hC hg hbox
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  have hreft_top : ¬ (⊬ (⊠(⊤ : α))) := ACR.irrefutable_reft_top (α := α) hC
  apply hreft_top
  exact le_trans (ACR.reft_le_prov_reft (x := (⊤ : α))) hbox


theorem thm_le_any_reft_of_self_bounds_000010 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {x y : α}, x ≤ □x → x ≤ ⊠x → x ≤ ⊠y := by
  intro α _ _ _ _ _ x y hxbox hxreft
  have htop : x ≤ ⊠(⊤ : α) := by
    exact ACR.le_reft_top_of_le_prov_of_le_reft hxbox hxreft
  have hmono : ⊠(⊤ : α) ≤ ⊠y := by
    exact ACR.reft_anti_mono (ACR.le_top (x := y))
  exact le_trans htop hmono


theorem thm_all_reft_irrefutable_000011 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → ∀ x : α, ¬ (⊬ (⊠ x)) := by
  intro α _ _ _ _ _ h hg x hx
  letI : Nonempty (ACR.GödelFixpoint α) := hg
  exact ACR.irrefutable_reft_top h (le_trans (ACR.reft_anti_mono (ACR.le_top (x := x))) hx)


theorem thm_reft_fixpoint_iff_double_reft_top_000012 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {x : α}, x ≐ ⊠(⊤ : α) → (x ≐ ⊠x ↔ ⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) := by
  intro α _ _ _ _ _ x hx
  constructor
  · intro hfix
    letI : Nonempty (ACR.GödelFixpoint α) := ⟨⟨x, hfix⟩⟩
    change ⊠⊠(⊤ : α) ≤ ⊠(⊤ : α) ∧ ⊠(⊤ : α) ≤ ⊠⊠(⊤ : α)
    constructor
    · simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    · exact ACR.reft_anti_mono (ACR.le_top (α := α) (x := ⊠(⊤ : α)))
  · intro hdd
    change x ≤ ⊠x ∧ ⊠x ≤ x
    change x ≤ ⊠(⊤ : α) ∧ ⊠(⊤ : α) ≤ x at hx
    rcases hx with ⟨hxt, htx⟩
    change ⊠⊠(⊤ : α) ≤ ⊠(⊤ : α) ∧ ⊠(⊤ : α) ≤ ⊠⊠(⊤ : α) at hdd
    constructor
    · have htop : x ≤ (⊤ : α) := ACR.le_top (α := α) (x := x)
      exact le_trans hxt (ACR.reft_anti_mono htop)
    · have hxx : ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono htx
      exact le_trans hxx (le_trans hdd.1 htx)


theorem thm_all_reft_fixpoints_iff_double_reft_top_000013 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (∀ {x : α}, x ≐ ⊠x ↔ x ≐ ⊠(⊤ : α)) ↔ (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) := by
  intro α _ _ _ _ _
  constructor
  · intro h
    have h' : (⊠(⊤ : α)) ≐ ⊠⊠(⊤ : α) :=
      (h (x := ⊠(⊤ : α))).2 ⟨le_rfl, le_rfl⟩
    exact ⟨h'.2, h'.1⟩
  · intro hfix
    intro x
    constructor
    · intro hx
      simpa using (ACR.gf_equiv_reft_top (α := α) (g := (⟨x, hx⟩ : ACR.GödelFixpoint α)))
    · intro hx
      rcases hx with ⟨hxt, htx⟩
      constructor
      · have htop : x ≤ (⊤ : α) := ACR.le_top (α := α) (x := x)
        exact le_trans hxt (ACR.reft_anti_mono htop)
      · have hxx : ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono htx
        exact le_trans hxx (le_trans hfix.1 htx)


theorem thm_reft_fixpoint_iff_reft_top_000014 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ {x : α}, x ≐ ⊠x ↔ x ≐ ⊠(⊤ : α) := by
  intro α _ _ _ _ _ hg x
  constructor
  · intro hx
    simpa using (ACR.gf_equiv_reft_top (α := α) (g := (⟨x, hx⟩ : ACR.GödelFixpoint α)))
  · intro hx
    rcases hx with ⟨hxt, htx⟩
    constructor
    · have htop : x ≤ (⊤ : α) := ACR.le_top (α := α) (x := x)
      exact le_trans hxt (ACR.reft_anti_mono htop)
    · have hxx : ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono htx
      letI : Nonempty (ACR.GödelFixpoint α) := hg
      exact le_trans hxx (le_trans (ACR.reft_reft_top_le_reft_top (α := α)) htx)


theorem thm_reft_top_box_iff_all_reft_fixpoints_000015 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ((⊠(⊤ : α)) ≐ □(⊠(⊤ : α))) ↔ ∀ {x : α}, x ≐ ⊠x → x ≐ □x := by
  intro α _ _ _ _ _
  constructor
  · intro h x hx
    have hg : Nonempty (ACR.GödelFixpoint α) := ⟨⟨x, hx⟩⟩
    have htop : ⊠(⊤ : α) ≐ □(⊠(⊤ : α)) := h hg
    have hxtop : x ≐ ⊠(⊤ : α) := by
      simpa using (ACR.gf_equiv_reft_top (α := α) (g := (⟨x, hx⟩ : ACR.GödelFixpoint α)))
    constructor
    · calc
        x ≤ ⊠(⊤ : α) := hxtop.1
        _ ≤ □(⊠(⊤ : α)) := htop.1
        _ ≤ □x := ACR.prov_mono hxtop.2
    · calc
        □x ≤ □(⊠(⊤ : α)) := ACR.prov_mono hxtop.1
        _ ≤ ⊠(⊤ : α) := htop.2
        _ ≤ x := hxtop.2
  · intro hall hg
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    have hfix : (⊠(⊤ : α)) ≐ ⊠⊠(⊤ : α) := by
      constructor
      · exact ACR.reft_anti_mono (ACR.le_top (x := ⊠(⊤ : α)))
      · simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    exact hall (x := ⊠(⊤ : α)) hfix


theorem thm_godel_fixpoint_iff_double_reft_top_000016 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) ↔ (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) := by
  intro α _ _ _ _ _
  constructor
  · intro hg
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    constructor
    · simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    · exact ACR.reft_anti_mono (ACR.le_top (x := ⊠(⊤ : α)))
  · intro h
    exact ⟨⟨⊠(⊤ : α), ⟨h.2, h.1⟩⟩⟩


theorem thm_inconsistent_iff_all_refutable_000017 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Inconsistent α ↔ ∀ x : α, ⊬ x := by
  intro α _ _ _ _ _
  constructor
  · intro h x
    exact le_trans (ACR.le_top (x := x)) h
  · intro h
    simpa [ACR.Inconsistent] using h (⊤ : α)


theorem thm_consistent_iff_all_godel_irrefutable_000018 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → (ACR.Consistent α ↔ ∀ g : ACR.GödelFixpoint α, ¬ (⊬ g.1)) := by
  intro α _ _ _ _ _ hg
  constructor
  · intro hCons
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    intro g hgBot
    have htop : (⊠ ((⊤ : α))) ≤ g.1 := (ACR.gf_equiv_reft_top (α := α) (g := g)).2
    exact ACR.irrefutable_reft_top (α := α) hCons (le_trans htop hgBot)
  · intro hAll
    intro hIncon
    obtain ⟨g⟩ := hg
    have htop : g.1 ≤ (⊤ : α) := ACR.le_top
    have hbot : g.1 ≤ (⊥ : α) := le_trans htop hIncon
    exact hAll g hbot


theorem thm_godel_fixpoint_equiv_irrefutable_000019 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ∀ {x : α}, (∃ g : ACR.GödelFixpoint α, x ≐ g.1) → ¬ (⊬ x) := by
  intro α _ _ _ _ hCons x hx hxbot
  rcases hx with ⟨g, hxg⟩
  apply hCons
  change (⊤ : α) ≤ ⊥
  have h1 : g.1 ≤ (⊥ : α) := le_trans hxg.2 hxbot
  have h2 : ⊠(⊥ : α) ≤ ⊠g.1 := ACR.reft_anti_mono h1
  have h3 : ⊠(⊥ : α) ≤ g.1 := le_trans h2 g.2.2
  calc
    (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
    _ ≤ g.1 := h3
    _ ≤ (⊥ : α) := h1


theorem thm_iterate_box_reft_top_irrefutable_000020 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → ∀ n : Nat, ¬ (⊬ (Nat.iterate (fun x : α => □x) n (⊠ (⊤ : α)))) := by
  intro α _ _ _ _ _ hCons hg n
  let f : α → α := fun x => □x
  cases n with
  | zero =>
      letI : Nonempty (ACR.GödelFixpoint α) := hg
      simpa [f, Nat.iterate] using (ACR.irrefutable_reft_top (α := α) hCons)
  | succ n =>
      obtain ⟨g⟩ := hg
      have hg_eq : g.1 ≐ ⊠(⊤ : α) := ACR.gf_equiv_reft_top (α := α) (g := g)
      have hg_le_boxg : g.1 ≤ □g.1 := by
        exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))
      have hiter_mono : ∀ m : Nat, ∀ {x y : α}, x ≤ y → Nat.iterate f m x ≤ Nat.iterate f m y := by
        intro m
        induction m with
        | zero =>
            intro x y hxy
            simpa [Nat.iterate]
        | succ m ih =>
            intro x y hxy
            simpa [f, Nat.iterate] using ih (x := □x) (y := □y) (ACR.prov_mono hxy)
      have hboxg_chain : ∀ m : Nat, □g.1 ≤ Nat.iterate f m (□g.1) := by
        intro m
        induction m with
        | zero =>
            simp [Nat.iterate]
        | succ m ih =>
            calc
              □g.1 ≤ Nat.iterate f m (□g.1) := ih
              _ ≤ Nat.iterate f m (□□g.1) := hiter_mono m (ACR.prov_mono hg_le_boxg)
              _ = Nat.iterate f (Nat.succ m) (□g.1) := by
                simp [f, Nat.iterate]
      intro hIter
      have hboxg_le_iterg : □g.1 ≤ Nat.iterate f (Nat.succ n) g.1 := by
        simpa [f, Nat.iterate] using hboxg_chain n
      have hiterg_le_itertop : Nat.iterate f (Nat.succ n) g.1 ≤ Nat.iterate f (Nat.succ n) (⊠(⊤ : α)) :=
        hiter_mono (Nat.succ n) hg_eq.1
      exact
        (AutomatedTheoryConstruction.thm_godel_fixpoint_box_irrefutable_000003 (α := α) hCons g)
          (le_trans hboxg_le_iterg (le_trans hiterg_le_itertop hIter))

theorem thm_not_both_box_reft_top_refutable_000021 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → ¬ (⊬ □(⊠(⊤ : α)) ∧ ⊬ ⊠(⊤ : α)) := by
  intro α _ _ _ _ _ hCons hGodel h
  letI : Nonempty (ACR.GödelFixpoint α) := hGodel
  exact (ACR.irrefutable_reft_top (α := α) hCons) h.2


theorem thm_le_godel_fixpoint_of_self_bounds_000023 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ {x : α}, x ≤ □x → x ≤ ⊠x → ∀ g : ACR.GödelFixpoint α, x ≤ g.1 := by
  intro α _ _ _ _ _ _ x hxBox hxReft g
  exact le_trans (thm_le_any_reft_of_self_bounds_000010 (x := x) (y := g.1) hxBox hxReft) g.2.2


theorem thm_consistent_iff_all_reft_irrefutable_000024 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → (ACR.Consistent α ↔ ∀ x : α, ¬ (⊬ (⊠ x))) := by
  intro α _ _ _ _ _ hgf
  letI : Nonempty (ACR.GödelFixpoint α) := hgf
  constructor
  · intro hCons x hx
    apply ACR.irrefutable_reft_top (α := α) hCons
    exact le_trans (ACR.reft_anti_mono (ACR.le_top (x := x))) hx
  · intro hall hIncon
    exact (hall ⊤) (le_trans (ACR.le_top (x := ⊠ (⊤ : α))) hIncon)


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


theorem thm_double_reft_below_reft_000031 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → ∀ x : α, ⊠⊠x ≤ ⊠x := by
  intro α _ _ _ _ _ hG x
  letI : Nonempty (ACR.GödelFixpoint α) := hG
  have hx_top : x ≤ (⊤ : α) := ACR.le_top
  have htop : ⊠(⊤ : α) ≤ ⊠x := ACR.reft_anti_mono hx_top
  have hxx : ⊠⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono htop
  exact le_trans hxx (le_trans (ACR.reft_reft_top_le_reft_top (α := α)) htop)

end AutomatedTheoryConstruction
