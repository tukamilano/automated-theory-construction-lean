import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

/-- Gödel fixpoints exist exactly when double reft top is equivalent to reft top. -/
theorem thm_godel_fixpoint_iff_reft_000002 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) ↔ ⊠⊠(⊤ : α) ≐ ⊠⊤ := by
  intro α _ _ _ _ _
  constructor
  · intro hg
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    exact ⟨ACR.reft_reft_top_le_reft_top (α := α), ACR.reft_anti_mono (ACR.le_top (x := ⊠⊤))⟩
  · intro h
    refine ⟨⟨⊠⊤, ?_⟩⟩
    exact ⟨h.2, h.1⟩

/-- Any two Godel fixpoints are equivalent. -/
theorem thm_godel_fixpoint_unique_000001 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {g h : ACR.GödelFixpoint α}, ACR.Equivalent g.1 h.1 := by
  intro α _ _ _ _ _ g h
  have hg : ACR.Equivalent g.1 (⊠(⊤ : α)) := ACR.gf_equiv_reft_top
  have hh : ACR.Equivalent h.1 (⊠(⊤ : α)) := ACR.gf_equiv_reft_top
  constructor
  · exact le_trans hg.1 hh.2
  · exact le_trans hh.1 hg.2

inductive Two where
  | ff
  | tt
deriving DecidableEq

instance : LE Two where
  le x y := match x, y with
    | .ff, _ => True
    | .tt, .tt => True
    | .tt, .ff => False

instance : Top Two where
  top := .tt

instance : Bot Two where
  bot := .ff

instance : Preorder Two where
  le := (· ≤ ·)
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial

instance : ACR (ULift Two) where
  toTop := ULift.instTop
  toBot := ULift.instBot
  toPreorder := ULift.instPreorder

instance : ACR.Prov (ULift Two) where
  prov := id

instance : ACR.Reft (ULift Two) where
  reft x := match x.down with
    | .ff => ⟨.tt⟩
    | .tt => ⟨.ff⟩

instance : ACR.APS (ULift Two) where
  prov_mono := by
    intro x y h
    simpa using h
  reft_anti_mono := by
    intro x y h
    cases x using ULift.casesOn with
    | _ x =>
      cases y using ULift.casesOn with
      | _ y =>
        cases x <;> cases y <;> trivial
  top_le_reft_bot := by
    trivial
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hxy hxr
    cases x using ULift.casesOn with
    | _ x =>
      cases y using ULift.casesOn with
      | _ y =>
        cases x <;> cases y <;> trivial
  reft_le_prov_reft := by
    intro x
    cases x using ULift.casesOn with
    | _ x =>
      cases x <;> trivial

instance : ACR.C5 (ULift Two) where
  le_top := by
    intro x
    cases x using ULift.casesOn with
    | _ x =>
      cases x <;> trivial

/-- A structure with a Henkin but no Godel fixpoint. -/
theorem thm_henkin_without_godel_model_000013 : ∃ (α : Type*) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α) (_ : ACR.C5 α), Nonempty (ACR.HenkinFixpoint α) ∧ ¬ Nonempty (ACR.GödelFixpoint α) := by
  refine ⟨ULift Two, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  constructor
  · refine ⟨⟨⊥, ?_⟩⟩
    constructor <;> rfl
  · intro h
    rcases h with ⟨⟨g, hg⟩⟩
    cases g using ULift.casesOn with
    | _ g =>
      cases g with
      | ff => exact hg.2
      | tt => exact hg.1

/-- An ACR system where `⊠⊠⊤` is equivalent to `⊠⊤` but no Godel fixpoint exists. -/
theorem thm_reft_top_equiv_no_godel_000008_is_false : ¬(∃ (α : Type*) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α), (⊠⊠(⊤ : α) ≐ ⊠⊤) ∧ ¬ Nonempty (ACR.GödelFixpoint α)) := by
  rintro ⟨α, _, _, _, _, hEq, hNo⟩
  apply hNo
  refine ⟨⟨⊠(⊤ : α), ?_⟩⟩
  simpa [ACR.Equivalent] using And.symm hEq


instance : ACR PUnit where
  toTop := inferInstance
  toBot := inferInstance
  toPreorder := inferInstance

instance : ACR.Prov PUnit where
  prov _ := PUnit.unit

instance : ACR.Reft PUnit where
  reft _ := PUnit.unit

instance : ACR.APS PUnit where
  prov_mono := by
    intro x y hxy
    exact PUnit.le (□x) (□y)
  reft_anti_mono := by
    intro x y hxy
    exact PUnit.le (⊠y) (⊠x)
  top_le_reft_bot := by
    trivial
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hxy hxr
    exact PUnit.le x (⊠⊤)
  reft_le_prov_reft := by
    intro x
    exact PUnit.le (⊠x) (□⊠x)

instance : ACR.C5 PUnit where
  le_top := by
    intro x
    exact PUnit.le x ⊤

/-- An inconsistent C5 APS model with a Godel fixpoint exists. -/
theorem thm_inconsistent_godel_model_exists_000009 : ∃ (α : Type*) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α) (_ : ACR.C5 α), ¬ ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) := by
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  constructor
  · intro h
    apply h
    trivial
  · refine ⟨⟨PUnit.unit, ?_⟩⟩
    constructor <;> trivial

/-- Gödel fixpoint existence implies Henkin fixpoint existence. -/
theorem thm_godel_implies_henkin_fixpoint_000014 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ _ _
  refine ⟨⟨⊤, ?_⟩⟩
  constructor
  · have h1 : (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
    have h2 : ⊠(⊥ : α) ≤ □(⊠(⊥ : α)) := ACR.reft_le_prov_reft
    have h3 : □(⊠(⊥ : α)) ≤ □((⊤ : α)) := ACR.prov_mono (ACR.le_top (x := ⊠(⊥ : α)))
    exact le_imp_le_of_le_of_le h1 h3 h2
  · simpa using (ACR.le_top (x := □((⊤ : α))))


universe u

inductive CounterexampleThree : Type u where
  | zero | one | two
deriving DecidableEq

def counterexampleReft : CounterexampleThree → CounterexampleThree
  | CounterexampleThree.zero => CounterexampleThree.one
  | CounterexampleThree.one => CounterexampleThree.two
  | CounterexampleThree.two => CounterexampleThree.two

instance : ACR CounterexampleThree where
  top := CounterexampleThree.zero
  bot := CounterexampleThree.one
  le x y := x = y
  le_refl := by
    intro a
    rfl
  le_trans := by
    intro a b c hab hbc
    simpa [hab] using hbc

instance : ACR.Reft CounterexampleThree where
  reft := counterexampleReft

/-- Gödel fixed points are equivalent to reft-top being one. -/
theorem thm_godel_fixpoint_reft_top_000017_is_false : ¬(∀ (α : Type*) [ACR α] [ACR.Reft α], (Nonempty (ACR.GödelFixpoint α) ↔ ∃ g : α, g = ⊠(⊤ : α) ∧ g ≐ ⊠g) ∧ ((⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ↔ ∃ g : α, g = ⊠(⊤ : α) ∧ g ≐ ⊠g)) := by
  intro h
  have hiff := (h (α := CounterexampleThree)).1
  have hgf : Nonempty (ACR.GödelFixpoint CounterexampleThree) := by
    refine ⟨⟨CounterexampleThree.two, ?_⟩⟩
    constructor <;> rfl
  have hex : ∃ g : CounterexampleThree, g = ⊠(⊤ : CounterexampleThree) ∧ g ≐ ⊠g :=
    hiff.mp hgf
  rcases hex with ⟨g, hg, hfix⟩
  have hg' : g = CounterexampleThree.one := by
    simpa [counterexampleReft] using hg
  cases hg'
  have hone : CounterexampleThree.one = CounterexampleThree.two := by
    change CounterexampleThree.one ≤ CounterexampleThree.two
    simpa [counterexampleReft] using hfix.1
  cases hone

/-- Subsingleton ACRs are inconsistent and have a Godel fixpoint. -/
theorem thm_subsingleton_inconsistent_godel_000020 : ∀ (α : Type*) [Subsingleton α] [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ¬ ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) := by
  intro α _ _ _ _ _ _
  constructor
  · intro hC
    apply hC
    exact (Subsingleton.elim (⊤ : α) ⊥).le
  · refine ⟨⟨⊤, ?_⟩⟩
    constructor
    · exact le_of_subsingleton
    · exact ACR.le_top

abbrev NoHenkinTopEq (α : Type*) [ACR α] [ACR.Prov α] [ACR.Reft α] : Prop :=
  ACR.Consistent α ∧ (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ∧ ¬ Nonempty (ACR.HenkinFixpoint α)

instance uliftNatACR : ACR (ULift Nat) where
  top := ⟨1⟩
  bot := ⟨0⟩
  toPreorder := inferInstance

instance uliftNatProv : ACR.Prov (ULift Nat) where
  prov x := ⟨x.down.succ⟩

instance uliftNatReft : ACR.Reft (ULift Nat) where
  reft _ := ⟨1⟩

instance uliftNatAPS : ACR.APS (ULift Nat) where
  prov_mono := by
    intro x y h
    exact Nat.succ_le_succ h
  reft_anti_mono := by
    intro x y h
    show (1 : Nat) ≤ 1
    exact NeZero.one_le
  top_le_reft_bot := by
    show (1 : Nat) ≤ 1
    exact NeZero.one_le
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hxy hxr
    simpa [uliftNatReft] using hxr
  reft_le_prov_reft := by
    intro x
    show (1 : Nat) ≤ 2
    exact NeZero.one_le

/-- A consistent APS model with top-box collapse and no Henkin fixpoint. -/
theorem thm_consistent_topbox_no_henkin_000026 : ∃ (α : Type*) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α), NoHenkinTopEq α := by
  refine ⟨ULift Nat, uliftNatACR, uliftNatProv, uliftNatReft, uliftNatAPS, ?_⟩
  constructor
  · show ¬ ((1 : Nat) ≤ 0)
    exact Nat.not_add_one_le_zero 0
  constructor
  · constructor
    · show (1 : Nat) ≤ 1
      exact NeZero.one_le
    · show (1 : Nat) ≤ 1
      exact NeZero.one_le
  · intro h
    rcases h with ⟨⟨n, hn⟩⟩
    have hs : ¬ ((⟨n.down.succ⟩ : ULift Nat) ≤ n) := by
      intro hle
      exact (Nat.not_succ_le_self n.down) hle
    apply hs
    simpa [uliftNatProv] using hn.2

/-- Finite consistent top-box collapse yields a Henkin fixpoint. -/
theorem thm_finite_topbox_henkin_exists_000029 : ∀ (α : Type*) [Finite α] [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ _ _ _
  let f : α → α := fun x => □x
  let g : α := ⊠ (⊤ : α)
  have hmono : Monotone f := by
    intro x y hxy
    exact ACR.prov_mono hxy
  have hg : g ≤ f g := by
    exact ACR.reft_le_prov_reft
  have horbit : Monotone fun n : ℕ => f^[n] g :=
    Monotone.monotone_iterate_of_le_map hmono hg
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, f^[m] g = f^[n] g ∧ m ≠ n := by
    simpa [Function.Injective, and_comm] using
      not_injective_infinite_finite (fun k : ℕ => f^[k] g)
  rcases lt_or_gt_of_ne hne with hmn | hnm
  · refine ⟨⟨f^[m] g, ?_⟩⟩
    constructor
    · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
    · have hle : f^[m + 1] g ≤ f^[n] g := horbit (Nat.succ_le_of_lt hmn)
      simpa [f, Function.iterate_succ_apply', heq] using hle
  · refine ⟨⟨f^[n] g, ?_⟩⟩
    constructor
    · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ n)
    · have hle : f^[n + 1] g ≤ f^[m] g := horbit (Nat.succ_le_of_lt hnm)
      simpa [f, Function.iterate_succ_apply', heq] using hle


instance : ACR.Prov CounterexampleThree where
  prov x := match x with
    | CounterexampleThree.zero => CounterexampleThree.one
    | CounterexampleThree.one => CounterexampleThree.two
    | CounterexampleThree.two => CounterexampleThree.zero

/-- A constant reflection expansion yields consistency, top reflection idempotence, and no Henkin fixpoint. -/
theorem thm_constant_reft_aps_no_henkin_000030_is_false : ¬(∀ (β : Type*) [ACR β] [ACR.Prov β], (∀ {x y : β}, x ≤ y → □x ≤ □y) → (∀ x : β, ¬ (□x ≤ x)) → ∀ c : β, ⊤ ≤ c → ¬ ((⊤ : β) ≤ ⊥) → ∃ (_ : ACR.Reft β) (_ : ACR.APS β), (∀ x : β, ⊠x = c) ∧ ACR.Consistent β ∧ (⊠⊠(⊤ : β) ≐ ⊠(⊤ : β)) ∧ ¬ Nonempty (ACR.HenkinFixpoint β)) := by
  intro h
  have hmono : ∀ {x y : CounterexampleThree}, x ≤ y → □x ≤ □y := by
    intro x y hxy
    cases hxy
    exact Std.IsPreorder.le_refl (□x)
  have hnfix : ∀ x : CounterexampleThree, ¬ (□x ≤ x) := by
    intro x hle
    cases x <;> cases hle
  have hex := @h CounterexampleThree inferInstance inferInstance hmono hnfix CounterexampleThree.zero rfl (by intro hbot; cases hbot)
  rcases hex with ⟨_hreft, _haps, hconst, _hcons, _hidem, _hnoHenkin⟩
  have hraw : ⊠CounterexampleThree.zero ≤ □(⊠CounterexampleThree.zero) := ACR.reft_le_prov_reft (x := CounterexampleThree.zero)
  rw [hconst CounterexampleThree.zero] at hraw
  change CounterexampleThree.zero = CounterexampleThree.one at hraw
  cases hraw

/-- A finite forward box-orbit from a pre-fixed point yields a Henkin fixpoint. -/
theorem thm_finite_box_orbit_henkin_000032 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∃ x : α, x ≤ □x ∧ Set.Finite {y : α | ∃ n : ℕ, ((fun z => □z)^[n]) x = y}) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ h
  rcases h with ⟨x, hx, hfin⟩
  let f : α → α := fun z => □z
  have hmono : Monotone f := by
    intro a b hab
    exact ACR.prov_mono hab
  have horbit : Monotone fun n : ℕ => f^[n] x :=
    Monotone.monotone_iterate_of_le_map hmono (by simpa [f] using hx)
  let s : Set α := {y : α | ∃ n : ℕ, f^[n] x = y}
  have hsfin : s.Finite := by
    exact (Set.finite_iff_finite_of_encard_eq_encard rfl).mp hfin
  classical
  letI := hsfin.fintype
  let g : ℕ → s := fun k => ⟨f^[k] x, ⟨k, rfl⟩⟩
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, g m = g n ∧ m ≠ n := by
    simpa [g, Function.Injective, and_comm] using
      not_injective_infinite_finite g
  have heq' : f^[m] x = f^[n] x := by
    simpa [g] using congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hne with hmn | hnm
  · refine ⟨⟨f^[m] x, ?_⟩⟩
    constructor
    · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
    · have hle : f^[m + 1] x ≤ f^[n] x := horbit (Nat.succ_le_of_lt hmn)
      simpa [f, Function.iterate_succ_apply', heq'] using hle
  · refine ⟨⟨f^[n] x, ?_⟩⟩
    constructor
    · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ n)
    · have hle : f^[n + 1] x ≤ f^[m] x := horbit (Nat.succ_le_of_lt hnm)
      simpa [f, Function.iterate_succ_apply', heq'] using hle

/-- Finite ACR structures admit a Henkin fixpoint. -/
theorem thm_finite_henkin_fixpoint_exists_000031 : ∀ (α : Type*) [Finite α] [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ _
  exact AutomatedTheoryConstruction.thm_finite_box_orbit_henkin_000032 (α := α) ⟨⊠(⊤ : α), ACR.reft_le_prov_reft, Set.toFinite _⟩

/-- A Godel fixpoint has infinite box-iterate orbit if no Henkin fixpoint exists. -/
theorem thm_godel_orbit_infinite_000038 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → ¬ Nonempty (ACR.HenkinFixpoint α) → ∀ g : ACR.GödelFixpoint α, Set.Infinite {y : α | ∃ n : ℕ, ((fun z => □z)^[n]) g.1 = y} := by
  intro α _ _ _ _ _ _ hno g
  by_contra hfinite
  have hgbox : g.1 ≤ □g.1 := by
    exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))
  exact hno <| AutomatedTheoryConstruction.thm_finite_box_orbit_henkin_000032 (α := α) ⟨g.1, hgbox, Set.not_infinite.mp hfinite⟩

end AutomatedTheoryConstruction
