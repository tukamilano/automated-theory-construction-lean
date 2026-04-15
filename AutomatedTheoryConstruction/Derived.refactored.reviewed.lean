import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.

universe u

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
  · exact ACR.le_top


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
    Monotone.monotone_iterate_of_le_map hmono hx
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

/-- A stabilized reflected top yields a Henkin fixpoint from a Godel fixpoint. -/
theorem thm_henkin_exists_from_godel_000039_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → Nonempty (ACR.GödelFixpoint α) → (⊠⊠(⊤ : α) ≐ ⊠⊤) → Nonempty (ACR.HenkinFixpoint α)) := by
  intro h
  rcases AutomatedTheoryConstruction.thm_consistent_topbox_no_henkin_000026 with
    ⟨α, hACR, hProv, hReft, hAPS, hNoHenkin⟩
  letI := hACR
  letI := hProv
  letI := hReft
  letI := hAPS
  have hEq : (⊠⊠(⊤ : α) ≐ ⊠⊤) := hNoHenkin.2.1
  have hGodel : Nonempty (ACR.GödelFixpoint α) := by
    by_contra hNoGodel
    exact AutomatedTheoryConstruction.thm_reft_top_equiv_no_godel_000008_is_false
      ⟨α, hACR, hProv, hReft, hAPS, hEq, hNoGodel⟩
  exact hNoHenkin.2.2 (h (α := α) hNoHenkin.1 hGodel hEq)

inductive Op000033Model where
  | ff | tt
deriving DecidableEq

instance : ACR (ULift.{u, 0} Op000033Model) where
  top := ⟨Op000033Model.ff⟩
  bot := ⟨Op000033Model.tt⟩
  le x y := x.down = Op000033Model.ff ∨ y.down = Op000033Model.tt
  le_refl := by
    intro x
    cases x using ULift.casesOn with
    | _ x =>
      cases x with
      | ff => exact Or.symm (Or.inr rfl)
      | tt => exact Or.inr rfl
  le_trans := by
    intro a b c hab hbc
    cases a using ULift.casesOn with
    | _ a =>
      cases b using ULift.casesOn with
      | _ b =>
        cases c using ULift.casesOn with
        | _ c =>
          cases a <;> cases b <;> cases c <;> simp at hab hbc ⊢

instance : ACR.Prov (ULift.{u, 0} Op000033Model) where
  prov x :=
    match x.down with
    | Op000033Model.ff => ⟨Op000033Model.tt⟩
    | Op000033Model.tt => ⟨Op000033Model.ff⟩

/-- Criterion for extending to an APS with constant reflection value c. -/
theorem thm_constant_reft_extension_criterion_000033_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] (c : α), (∃ hR : ACR.Reft α, ∃ hA : @ACR.APS α _ _ hR, ∀ x : α, @ACR.Reft.reft α _ hR x = c) ↔ ((⊤ : α) ≤ c ∧ c ≤ □c)) := by
  intro h
  have hex :=
    (h (α := ULift Op000033Model) (c := (⟨Op000033Model.ff⟩ : ULift Op000033Model))).2 (by
      constructor
      · exact Or.inl rfl
      · exact Or.inl rfl)
  rcases hex with ⟨hR, hA, _⟩
  letI : ACR.Reft (ULift Op000033Model) := hR
  letI : ACR.APS (ULift Op000033Model) := hA
  have hmono :=
    ACR.prov_mono (x := ((⟨Op000033Model.ff⟩ : ULift Op000033Model)))
      (y := ((⟨Op000033Model.tt⟩ : ULift Op000033Model))) (Or.inl rfl)
  change Op000033Model.tt = Op000033Model.ff ∨ Op000033Model.ff = Op000033Model.tt at hmono
  cases hmono with
  | inl hEq => cases hEq
  | inr hEq => cases hEq

/-- A repeated box iterate on a Godel fixpoint yields a Henkin fixpoint. -/
theorem thm_box_orbit_repeat_henkin_000042 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], Nonempty (ACR.GödelFixpoint α) → (∃ g : ACR.GödelFixpoint α, ∃ m n : ℕ, m < n ∧ ((fun z : α => □z)^[m]) g.1 ≐ ((fun z : α => □z)^[n]) g.1) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ _ hrep
  rcases hrep with ⟨g, m, n, hmn, heq⟩
  let f : α → α := fun z => □z
  have hmono : Monotone f := by
    intro a b hab
    exact ACR.prov_mono hab
  have hg : g.1 ≤ f g.1 := by
    show g.1 ≤ □g.1
    exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))
  have horbit : Monotone fun k : ℕ => f^[k] g.1 :=
    Monotone.monotone_iterate_of_le_map hmono hg
  refine ⟨⟨f^[m] g.1, ?_⟩⟩
  constructor
  · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
  · have hle : f^[m + 1] g.1 ≤ f^[n] g.1 := horbit (Nat.succ_le_of_lt hmn)
    simpa [f, Function.iterate_succ_apply'] using le_trans hle heq.2

/-- A constant reflection operator exists exactly for postfixed constants above top. -/
theorem thm_constant_reft_iff_bounds_000044 : ∀ {α : Type*} [ACR α] [ACR.Prov α] (c : α), Monotone (fun x : α => □x) → ((∃ hR : ACR.Reft α, ∃ hA : @ACR.APS α _ _ hR, ∀ x : α, @ACR.Reft.reft α _ hR x = c) ↔ ((⊤ : α) ≤ c ∧ c ≤ □c)) := by
  intro α _ _ c hmono
  constructor
  · rintro ⟨hR, _, hconst⟩
    letI : ACR.Reft α := hR
    constructor
    · simpa [hconst ⊥] using (ACR.top_le_reft_bot (α := α))
    · simpa [hconst c] using (ACR.reft_le_prov_reft (α := α) (x := c))
  · rintro ⟨htop, hbox⟩
    let hR : ACR.Reft α := { reft := fun _ => c }
    have hA : @ACR.APS α _ _ hR :=
      { prov_mono := by
          intro x y hxy
          exact hmono hxy
        reft_anti_mono := by
          intro x y hxy
          exact le_rfl
        top_le_reft_bot := by
          simpa using htop
        le_reft_top_of_le_prov_of_le_reft := by
          intro x y hxy hxr
          simpa using hxr
        reft_le_prov_reft := by
          intro x
          simpa using hbox }
    exact ⟨hR, hA, by intro x; rfl⟩

/-- Constant reflection admits an APS exactly under monotonicity and bounds on c. -/
theorem thm_constant_reft_aps_iff_000050 : ∀ {α : Type*} [ACR α] [ACR.Prov α] (c : α), let hR : ACR.Reft α := { reft := fun _ : α => c }; Nonempty (@ACR.APS α _ _ hR) ↔ (Monotone (fun x : α => □x) ∧ (⊤ : α) ≤ c ∧ c ≤ □c) := by
  intro α _ _ c
  let hR : ACR.Reft α := { reft := fun _ : α => c }
  letI : ACR.Reft α := hR
  change Nonempty (@ACR.APS α _ _ hR) ↔
      (Monotone (fun x : α => □x) ∧ (⊤ : α) ≤ c ∧ c ≤ □c)
  constructor
  · rintro ⟨hA⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      exact hA.prov_mono hxy
    · simpa [hR] using hA.top_le_reft_bot
    · simpa [hR] using (hA.reft_le_prov_reft (x := ⊥))
  · rintro ⟨hm, htop, hpc⟩
    refine ⟨{
      prov_mono := ?_,
      reft_anti_mono := ?_,
      top_le_reft_bot := ?_,
      le_reft_top_of_le_prov_of_le_reft := ?_,
      reft_le_prov_reft := ?_
    }⟩
    · exact fun {x y} a => Monotone.imp hm a
    · intro x y hxy
      change c ≤ c
      exact Std.IsPreorder.le_refl c
    · simpa [hR] using htop
    · intro x y hxy hxr
      simpa [hR] using hxr
    · intro x
      simpa [hR] using hpc

inductive Op000035Bool where
  | ff | tt
  deriving DecidableEq

instance : ACR (ULift Op000035Bool) where
  top := ⟨.tt⟩
  bot := ⟨.ff⟩
  le x y := x.down = y.down
  le_refl := by
    intro x
    exact ULift.down_inj.mpr rfl
  le_trans := by
    intro a b c hab hbc
    simpa [hab] using hbc

instance : ACR.Prov (ULift Op000035Bool) where
  prov _ := ⟨.ff⟩

/-- Constant reflection is equivalent to a box fixed point in equality-preorder models. -/
theorem thm_constant_reflection_iff_box_fixpoint_000035_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α], (∀ {x y : α}, x ≤ y ↔ x = y) → Monotone (fun x : α => □x) → ((∃ c : α, ∃ hR : ACR.Reft α, ∃ hA : @ACR.APS α _ _ hR, ∀ x : α, @ACR.Reft.reft α _ hR x = c) ↔ ∃ c : α, c = □c)) := by
  intro h
  have hEq : ∀ {x y : ULift Op000035Bool}, x ≤ y ↔ x = y := by
    intro x y
    constructor
    · intro hxy
      cases x using ULift.casesOn with
      | _ x =>
        cases y using ULift.casesOn with
        | _ y =>
          cases x <;> cases y <;> cases hxy <;> rfl
    · exact fun a => Std.le_of_eq a
  have hMono : Monotone (fun x : ULift Op000035Bool => □x) := by
    intro x y hxy
    rfl
  have hiff := h (α := ULift Op000035Bool) hEq hMono
  have hleft : ∃ c : ULift Op000035Bool, ∃ hR : ACR.Reft (ULift Op000035Bool), ∃ hA : @ACR.APS (ULift Op000035Bool) _ _ hR, ∀ x : ULift Op000035Bool, @ACR.Reft.reft (ULift Op000035Bool) _ hR x = c :=
    hiff.2 ⟨⟨Op000035Bool.ff⟩, rfl⟩
  rcases hleft with ⟨c, hR, _, hconst⟩
  letI : ACR.Reft (ULift Op000035Bool) := hR
  have hbounds := (thm_constant_reft_iff_bounds_000044 (α := ULift Op000035Bool) (c := c) hMono).1 ⟨hR, inferInstance, hconst⟩
  cases c using ULift.casesOn with
  | _ c =>
      cases c with
      | ff =>
          cases hbounds.1
      | tt =>
          cases hbounds.2

/-- Constant-reflection APS exists exactly when box is monotone and some postfixed point lies above top. -/
theorem thm_constant_aps_iff_bounds_000051 : ∀ {α : Type*} [ACR α] [ACR.Prov α], (∃ c : α, let hR : ACR.Reft α := { reft := fun _ : α => c }; Nonempty (@ACR.APS α _ _ hR)) ↔ (Monotone (fun x : α => □x) ∧ ∃ c : α, (⊤ : α) ≤ c ∧ c ≤ □c) := by
  intro α _ _
  constructor
  · rintro ⟨c, hA⟩
    have h := (thm_constant_reft_aps_iff_000050 (α := α) (c := c)).1 hA
    rcases h with ⟨hmono, htop, hbox⟩
    exact ⟨hmono, ⟨c, htop, hbox⟩⟩
  · rintro ⟨hmono, ⟨c, htop, hbox⟩⟩
    exact ⟨c, (thm_constant_reft_aps_iff_000050 (α := α) (c := c)).2 ⟨hmono, htop, hbox⟩⟩

abbrev boxk {α : Type*} [ACR α] [ACR.Prov α] (k : ℕ) : α → α := (fun z : α => □z)^[k]

/-- A finite positive box-iterate orbit yields a fixed point of that iterate. -/
theorem thm_finite_boxk_orbit_henkin_000037 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (k : ℕ), 0 < k → (∃ x : α, x ≤ boxk k x ∧ Set.Finite {y : α | ∃ n : ℕ, (boxk k)^[n] x = y}) → ∃ h : α, h ≐ boxk k h := by
  intro α _ _ _ _ k hk h
  rcases h with ⟨x, hx, hfin⟩
  let f : α → α := boxk k
  have hmonoBox : Monotone (fun z : α => □z) := by
    intro a b hab
    exact ACR.prov_mono hab
  have hmono : Monotone f := by
    exact Monotone.iterate hmonoBox k
  have horbit : Monotone fun n : ℕ => f^[n] x :=
    Monotone.monotone_iterate_of_le_map hmono (by exact le_of_eq_of_le rfl hx)
  let s : Set α := {y : α | ∃ n : ℕ, f^[n] x = y}
  have hsfin : s.Finite := by
    exact (Set.finite_iff_finite_of_encard_eq_encard rfl).mp hfin
  classical
  letI := hsfin.fintype
  let g : ℕ → s := fun n => ⟨f^[n] x, ⟨n, rfl⟩⟩
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, g m = g n ∧ m ≠ n := by
    simpa [g, Function.Injective, and_comm] using not_injective_infinite_finite g
  have hmn_eq : f^[m] x = f^[n] x := by
    simpa [g] using congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hne with hmn | hnm
  · refine ⟨f^[m] x, ?_⟩
    constructor
    · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
    · have hle : f^[m + 1] x ≤ f^[n] x := horbit (Nat.succ_le_of_lt hmn)
      simpa [f, Function.iterate_succ_apply', hmn_eq] using hle
  · refine ⟨f^[n] x, ?_⟩
    constructor
    · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ n)
    · have hle : f^[n + 1] x ≤ f^[m] x := horbit (Nat.succ_le_of_lt hnm)
      simpa [f, Function.iterate_succ_apply', hmn_eq] using hle

/-- A repeated positive box-iterate orbit yields a box-k fixed point. -/
theorem thm_boxk_orbit_repeat_fixpoint_000047 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (k : ℕ) {x : α} {m n : ℕ}, 0 < k → x ≤ ((fun z : α => □z)^[k]) x → m < n → ((((fun z : α => □z)^[k])^[m]) x ≐ (((fun z : α => □z)^[k])^[n]) x) → ∃ h : α, h ≐ ((fun z : α => □z)^[k]) h := by
  intro α _ _ _ _ k x m n _hk hx hmn hrepeat
  let f : α → α := ((fun z : α => □z)^[k])
  have hmonoBox : Monotone (fun z : α => □z) := by
    intro a b hab
    exact ACR.prov_mono hab
  have hmono : Monotone f := by
    exact Monotone.iterate hmonoBox k
  have horbit : Monotone (fun t : ℕ => f^[t] x) :=
    Monotone.monotone_iterate_of_le_map hmono (by exact le_of_eq_of_le rfl hx)
  refine ⟨f^[m] x, ?_⟩
  constructor
  · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
  · have hle : f^[m + 1] x ≤ f^[n] x := horbit (Nat.succ_le_of_lt hmn)
    have hback : f^[n] x ≤ f^[m] x := by
      simpa [f] using hrepeat.2
    exact le_trans (by simpa [f, Function.iterate_succ_apply'] using hle) hback

/-- A repeated inflationary box orbit yields a Henkin fixpoint. -/
theorem thm_box_orbit_repeat_henkin_000046 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] {x : α} {m n : ℕ}, x ≤ □x → m < n → ((fun z : α => □z)^[m]) x ≐ ((fun z : α => □z)^[n]) x → ∃ h : α, h ≐ □h := by
  intro α _ _ _ _ x m n hx hmn hEq
  let f : α → α := fun z : α => □z
  have hmono : Monotone f := by
    intro a b hab
    exact ACR.prov_mono hab
  have horbit : Monotone (fun t : ℕ => f^[t] x) :=
    Monotone.monotone_iterate_of_le_map hmono (by exact le_of_eq_of_le rfl hx)
  refine ⟨f^[m] x, ?_⟩
  constructor
  · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
  · have hle : f^[m + 1] x ≤ f^[n] x := horbit (Nat.succ_le_of_lt hmn)
    have hback : f^[n] x ≤ f^[m] x := by
      simpa [f] using hEq.2
    exact le_trans (by simpa [f, Function.iterate_succ_apply'] using hle) hback

/-- Henkin fixed points are equivalent to repeating inflationary box orbits. -/
theorem thm_henkin_iff_box_orbit_repeat_000057 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∃ h : α, h ≐ □h) ↔ ∃ x : α, x ≤ □x ∧ ∃ m n : ℕ, m < n ∧ ((fun z : α => □z)^[m]) x ≐ ((fun z : α => □z)^[n]) x := by
  intro α _ _ _ _
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, hh.1, 0, 1, Nat.zero_lt_one, ?_⟩
    simpa using hh
  · rintro ⟨x, hx, m, n, hmn, hEq⟩
    exact AutomatedTheoryConstruction.thm_box_orbit_repeat_henkin_000046 hx hmn hEq

/-- A repeated positive box-power orbit on a Godel fixpoint yields a Henkin fixpoint. -/
theorem thm_boxk_repeat_henkin_000069 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (k : ℕ), 0 < k → Nonempty (ACR.GödelFixpoint α) → (∃ g : ACR.GödelFixpoint α, ∃ m n : ℕ, m < n ∧ ((((fun z : α => □z)^[k])^[m]) g.1 ≐ ((((fun z : α => □z)^[k])^[n]) g.1))) → Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ k hk hG hrep
  refine thm_box_orbit_repeat_henkin_000042 hG ?_
  rcases hrep with ⟨g, m, n, hmn, hEq⟩
  refine ⟨g, k * m, k * n, Nat.mul_lt_mul_of_pos_left hmn hk, ?_⟩
  simpa [Function.iterate_mul] using hEq

/-- Henkin fixpoints iff a positive box-k orbit repeats on a Godel fixpoint. -/
theorem thm_henkin_iff_boxk_orbit_repeat_000074_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (k : ℕ), 0 < k → (Nonempty (ACR.HenkinFixpoint α) ↔ ∃ g : ACR.GödelFixpoint α, ∃ m n : ℕ, m < n ∧ (((((fun z : α => □z)^[k])^[m]) g.1 ≐ ((((fun z : α => □z)^[k])^[n]) g.1))))) := by
  intro h
  rcases AutomatedTheoryConstruction.thm_henkin_without_godel_model_000013 with
    ⟨α, hACR, hProv, hReft, hAPS, hC5, hHenkin, hNoGodel⟩
  letI : ACR α := hACR
  letI : ACR.Prov α := hProv
  letI : ACR.Reft α := hReft
  letI : ACR.APS α := hAPS
  letI : ACR.C5 α := hC5
  have hiff := h (α := α) 1 Nat.one_pos
  have hRight :
      ∃ g : ACR.GödelFixpoint α, ∃ m n : ℕ, m < n ∧
        (((((fun z : α => □z)^[1])^[m]) g.1 ≐ ((((fun z : α => □z)^[1])^[n]) g.1))) :=
    hiff.mp hHenkin
  rcases hRight with ⟨g, m, n, hmn, hEq⟩
  exact hNoGodel ⟨g⟩

inductive Op000082Two where
  | ff
  | tt
deriving DecidableEq

instance : LE Op000082Two where
  le x y := match x, y with
    | .ff, _ => True
    | .tt, .tt => True
    | .tt, .ff => False

instance : Top Op000082Two where
  top := .tt

instance : Bot Op000082Two where
  bot := .ff

instance : Preorder Op000082Two where
  le := (· ≤ ·)
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial

instance : ACR (ULift Op000082Two) where
  toTop := ULift.instTop
  toBot := ULift.instBot
  toPreorder := ULift.instPreorder

instance : ACR.Prov (ULift Op000082Two) where
  prov := id

instance : ACR.Reft (ULift Op000082Two) where
  reft x := match x.down with
    | .ff => ⟨.tt⟩
    | .tt => ⟨.ff⟩

instance : ACR.APS (ULift Op000082Two) where
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

instance : ACR.C5 (ULift Op000082Two) where
  le_top := by
    intro x
    cases x using ULift.casesOn with
    | _ x =>
      cases x <;> trivial

/-- Existence of a consistent Gödel-free model with fixed points for every positive box iterate. -/
theorem thm_godel_free_iterate_fixed_model_000082 : ∃ α : Type*, ∃ _ : ACR α, ∃ _ : ACR.Prov α, ∃ _ : ACR.Reft α, ∃ _ : ACR.APS α, ∃ _ : ACR.C5 α, ACR.Consistent α ∧ ¬ Nonempty (ACR.GödelFixpoint α) ∧ ∀ k : ℕ, 0 < k → ∃ x : α, x ≐ ((fun z : α => □z)^[k]) x := by
  refine ⟨ULift Op000082Two, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  constructor
  · intro h
    simpa using h
  constructor
  · intro h
    rcases h with ⟨⟨g, hg⟩⟩
    cases g using ULift.casesOn with
    | _ g =>
      cases g with
      | ff => exact hg.2
      | tt => exact hg.1
  · intro k hk
    refine ⟨(⟨Op000082Two.ff⟩ : ULift Op000082Two), ?_⟩
    have hiter : ∀ n : ℕ, ((fun z : ULift Op000082Two => □z)^[n]) (⟨Op000082Two.ff⟩ : ULift Op000082Two) = (⟨Op000082Two.ff⟩ : ULift Op000082Two) := by
      intro n
      induction n with
      | zero =>
          rfl
      | succ n ih =>
          change (fun z : ULift Op000082Two => □z) (((fun z : ULift Op000082Two => □z)^[n]) (⟨Op000082Two.ff⟩ : ULift Op000082Two)) = (⟨Op000082Two.ff⟩ : ULift Op000082Two)
          simpa using ih
    constructor
    · exact ge_of_eq (hiter k)
    · exact (hiter k).le

/-- Finite even-cardinality consistent models with no Godel fixpoint. -/
theorem thm_even_card_no_godel_family_000086 : ∀ m : ℕ, 0 < m → ∃ α : Type*, ∃ _ : Fintype α, ∃ _ : ACR α, ∃ _ : ACR.Prov α, ∃ _ : ACR.Reft α, ∃ _ : ACR.APS α, ∃ _ : ACR.C5 α, ACR.Consistent α ∧ Fintype.card α = 2 * m ∧ ¬ Nonempty (ACR.GödelFixpoint α) ∧ ∀ x : α, x ≐ □x := by
  intro m hm
  have h2m : 0 < 2 * m := by
    exact Nat.succ_mul_pos 1 hm
  let α := ULift (Fin (2 * m))
  let b : α := ⟨⟨0, h2m⟩⟩
  let t : α := ⟨⟨2 * m - 1, by
    exact Nat.sub_one_lt_of_lt h2m⟩⟩
  let provFn : α → α := fun x => x
  let reftFn : α → α := fun x => if x = b then t else b
  letI : Fintype α := inferInstance
  letI : ACR α :=
    { toTop := ⟨t⟩
      toBot := ⟨b⟩
      toPreorder := inferInstance }
  have hb_le_t : b ≤ t := by
    change b.down.val ≤ t.down.val
    exact (Nat.le_sub_one_iff_lt h2m).mpr h2m
  have ht_ne_b : t ≠ b := by
    intro h
    have hval : t.down.val = b.down.val := by
      exact Eq.symm
          ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (congrArg Fin.val (congrArg ULift.down (id (Eq.symm h))))))
    dsimp [b, t] at hval
    omega
  letI : ACR.Prov α := ⟨provFn⟩
  letI : ACR.Reft α := ⟨reftFn⟩
  letI : ACR.APS α :=
    { prov_mono := by
        intro x y hxy
        change provFn x ≤ provFn y
        exact le_of_eq_of_le rfl hxy
      reft_anti_mono := by
        intro x y hxy
        change reftFn y ≤ reftFn x
        by_cases hx : x = b
        · by_cases hy : y = b
          · simp [reftFn, hx, hy]
          · simp [reftFn, hx, hy, hb_le_t]
        · have hy : y ≠ b := by
            intro hy
            apply hx
            apply ULift.ext
            apply Fin.ext
            have hxle : x ≤ b := by
              exact le_of_le_of_eq hxy hy
            change x.down.val = b.down.val
            change x.down.val ≤ b.down.val at hxle
            exact Nat.eq_zero_of_le_zero hxle
          simp [reftFn, hx, hy]
      top_le_reft_bot := by
        change t ≤ reftFn b
        simp [reftFn]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxr
        change x ≤ provFn y at hxy
        change x ≤ reftFn y at hxr
        change x ≤ reftFn t
        by_cases hy : y = b
        · have hxb : x ≤ b := by
            exact le_of_le_of_eq hxy hy
          simpa [reftFn, ht_ne_b] using hxb
        · have hxb : x ≤ b := by
            simpa [reftFn, hy] using hxr
          simpa [reftFn, ht_ne_b] using hxb
      reft_le_prov_reft := by
        intro x
        change reftFn x ≤ provFn (reftFn x)
        exact Std.IsPreorder.le_refl (reftFn x) }
  letI : ACR.C5 α :=
    { le_top := by
        intro x
        change x.down.val ≤ t.down.val
        dsimp [t]
        omega }
  have hcons : ACR.Consistent α := by
    intro hinc
    change t.down.val ≤ b.down.val at hinc
    dsimp [b, t] at hinc
    omega
  have hno : ¬ Nonempty (ACR.GödelFixpoint α) := by
    intro hg
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    have hirr : ¬ ((⊠(⊤ : α)) ≤ (⊥ : α)) := ACR.irrefutable_reft_top (α := α) hcons
    apply hirr
    change reftFn t ≤ b
    simp [reftFn, ht_ne_b]
  refine ⟨ULift (Fin (2 * m)), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨hcons, ?_⟩
  refine ⟨by
    simp [α], ?_⟩
  refine ⟨hno, ?_⟩
  intro x
  constructor <;> change x ≤ provFn x <;> simp [provFn]


instance : LE (ULift ℕ) where
  le _ _ := True

instance : Top (ULift ℕ) where
  top := ⟨0⟩

instance : Bot (ULift ℕ) where
  bot := ⟨0⟩

instance : Preorder (ULift ℕ) where
  le := (· ≤ ·)
  lt _ _ := False
  le_refl := by
    intro x
    trivial
  le_trans := by
    intro a b c hab hbc
    trivial
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro h
      cases h
    · intro h
      exact h.2 trivial

instance : ACR (ULift ℕ) where
  toTop := inferInstance
  toBot := inferInstance
  toPreorder := inferInstance

instance : ACR.Prov (ULift ℕ) where
  prov x := ⟨x.down + 1⟩

instance : ACR.Reft (ULift ℕ) where
  reft x := x

instance : ACR.APS (ULift ℕ) where
  prov_mono := by
    intro x y h
    trivial
  reft_anti_mono := by
    intro x y h
    trivial
  top_le_reft_bot := by
    trivial
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hxy hxr
    trivial
  reft_le_prov_reft := by
    intro x
    trivial

/-- Henkin fixpoints are equivalent to a finite orbit below a positive box iterate. -/
theorem thm_henkin_boxk_finite_orbit_000099_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (k : ℕ), 0 < k → (Nonempty (ACR.HenkinFixpoint α) ↔ ∃ x : α, x ≤ ((fun z : α => □z)^[k]) x ∧ Set.Finite {y : α | ∃ n : ℕ, (((fun z : α => □z)^[k])^[n]) x = y})) := by
  intro h
  have hHenkin : Nonempty (ACR.HenkinFixpoint (ULift ℕ)) := by
    refine ⟨⟨(⟨0⟩ : ULift ℕ), ?_⟩⟩
    constructor <;> trivial
  have hiff := h (α := ULift ℕ) 1 Nat.one_pos
  rcases hiff.mp hHenkin with ⟨x, hx, hfin⟩
  let s : Set (ULift ℕ) := {y : ULift ℕ | ∃ n : ℕ, (((fun z : ULift ℕ => □z)^[1])^[n]) x = y}
  have hsfin : s.Finite := by
    exact (Set.finite_iff_finite_of_encard_eq_encard rfl).mp hfin
  have hiter : ∀ n : ℕ, ((fun z : ULift ℕ => □z)^[n]) x = ⟨x.down + n⟩ := by
    intro n
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        rw [ih]
        rfl
  classical
  letI := hsfin.fintype
  let g : ℕ → s := fun n => ⟨⟨x.down + n⟩, ⟨n, by
    simpa [Function.iterate_mul] using hiter n⟩⟩
  have hg_inj : Function.Injective g := by
    intro m n hmn
    have hvals : x.down + m = x.down + n := by
      exact congrArg (fun z : s => z.1.down) hmn
    exact Nat.add_left_cancel hvals
  exact (not_injective_infinite_finite g) hg_inj


inductive Op000103Three : Type u where
  | a | b | c
deriving DecidableEq

def op000103Reft : Op000103Three → Op000103Three
  | .a => .c
  | .b => .a
  | .c => .b

instance : Top Op000103Three where
  top := .a

instance : Bot Op000103Three where
  bot := .b

instance : LE Op000103Three where
  le x y := x = y

instance : Preorder Op000103Three where
  le := (· ≤ ·)
  le_refl := by
    intro x
    rfl
  le_trans := by
    intro x y z hxy hyz
    cases hxy
    exact le_of_eq_of_le rfl hyz

instance : ACR Op000103Three where
  toTop := inferInstance
  toBot := inferInstance
  toPreorder := inferInstance

instance : ACR.Prov Op000103Three where
  prov := id

instance : ACR.Reft Op000103Three where
  reft := op000103Reft

instance : ACR.APS Op000103Three where
  prov_mono := by
    intro x y hxy
    simpa using hxy
  reft_anti_mono := by
    intro x y hxy
    cases hxy
    exact Std.IsPreorder.le_refl (⊠x)
  top_le_reft_bot := by
    rfl
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hxy hxr
    cases x <;> cases y <;> cases hxy <;> cases hxr
  reft_le_prov_reft := by
    intro x
    rfl

/-- Irrefutable reft-top yields a Gödel fixpoint. -/
theorem thm_godel_exists_from_irrefutable_reft_top_000103_is_false : ¬(∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ¬ (⊬ ⊠(⊤ : α)) → Nonempty (ACR.GödelFixpoint α)) := by
  intro h
  have hcons : ACR.Consistent Op000103Three := by
    intro hinc
    cases hinc
  have hnirr : ¬ (⊬ ⊠(⊤ : Op000103Three)) := by
    intro hbad
    cases hbad
  have hspec :
      ACR.Consistent Op000103Three →
        ¬ (⊬ ⊠(⊤ : Op000103Three)) →
        Nonempty (ACR.GödelFixpoint Op000103Three) := by
    exact fun a a_1 => Nonempty.map (fun a => a) (h hcons hnirr)
  have hg : Nonempty (ACR.GödelFixpoint Op000103Three) := hspec hcons hnirr
  rcases hg with ⟨⟨g, hg⟩⟩
  cases g <;> cases hg.1

inductive Op000102Two where
  | ff
  | tt
  deriving DecidableEq, Fintype

instance : LE Op000102Two where
  le x y := match x, y with
    | .ff, _ => True
    | .tt, .tt => True
    | .tt, .ff => False

instance : Top Op000102Two where
  top := .tt

instance : Bot Op000102Two where
  bot := .ff

instance : Preorder Op000102Two where
  le := (· ≤ ·)
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial

instance : ACR Op000102Two where
  toTop := inferInstance
  toBot := inferInstance
  toPreorder := inferInstance

abbrev Op000102Lift := ULift.{u, 0} Op000102Two

instance : LE Op000102Lift where
  le x y := x.down ≤ y.down

instance : Top Op000102Lift where
  top := ⟨⊤⟩

instance : Bot Op000102Lift where
  bot := ⟨⊥⟩

instance : Preorder Op000102Lift where
  le := (· ≤ ·)
  le_refl := by
    exact fun a => Std.IsPreorder.le_refl a
  le_trans := by
    exact fun a b c a_1 a_2 => Std.IsPreorder.le_trans a b c a_1 a_2

instance : ACR Op000102Lift where
  toTop := inferInstance
  toBot := inferInstance
  toPreorder := inferInstance

instance : ACR.Prov Op000102Lift where
  prov := id

instance : ACR.Reft Op000102Lift where
  reft _ := ⊤

instance : ACR.APS Op000102Lift where
  prov_mono := by
    intro x y hxy
    simpa using hxy
  reft_anti_mono := by
    intro x y hxy
    change (⊤ : Op000102Lift) ≤ ⊤
    trivial
  top_le_reft_bot := by
    change (⊤ : Op000102Lift) ≤ ⊤
    trivial
  le_reft_top_of_le_prov_of_le_reft := by
    intro x y hxy hxr
    change x ≤ (⊤ : Op000102Lift)
    cases x with
    | up x =>
        cases x <;> trivial
  reft_le_prov_reft := by
    intro x
    change (⊤ : Op000102Lift) ≤ ⊤
    trivial

instance : ACR.C5 Op000102Lift where
  le_top := by
    intro x
    cases x with
    | up x =>
        cases x <;> trivial

/-- Gödel fixpoints exist exactly for odd finite cardinality in a finite chain with universal Henkin fixedness. -/
theorem thm_godel_fixpoint_odd_cardinality_000102_is_false : ¬(∀ {α : Type*} [Fintype α] [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α → (∀ x : α, x ≐ □x) → (∀ x y : α, x ≤ y ∨ y ≤ x) → (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → (Nonempty (ACR.GödelFixpoint α) ↔ ∃ m : ℕ, Fintype.card α = 2 * m + 1)) := by
  intro h
  have hcons : ACR.Consistent Op000102Lift := by
    intro hinc
    cases hinc
  have hbox : ∀ x : Op000102Lift, x ≐ □x := by
    intro x
    constructor <;> exact le_rfl
  have htotal : ∀ x y : Op000102Lift, x ≤ y ∨ y ≤ x := by
    intro x y
    cases x with
    | up x =>
        cases y with
        | up y =>
            cases x <;> cases y <;> simp [LE.le]
  have hantisymm : ∀ {x y : Op000102Lift}, x ≤ y → y ≤ x → x = y := by
    intro x y hxy hyx
    cases x with
    | up x =>
        cases y with
        | up y =>
            cases x <;> cases y <;> simp [LE.le] at hxy hyx ⊢
  have hiff := @h Op000102Lift inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance hcons hbox htotal hantisymm
  have hG : Nonempty (ACR.GödelFixpoint Op000102Lift) := by
    refine ⟨⟨⊤, ?_⟩⟩
    constructor <;> exact Std.IsPreorder.le_refl ⊤
  rcases hiff.mp hG with ⟨m, hm⟩
  have hcard₂ : Fintype.card Op000102Two = 2 := by
    native_decide
  have hcard' : Fintype.card Op000102Lift = Fintype.card Op000102Two := by
    exact Fintype.card_ulift Op000102Two
  omega

/-- Finite consistent linear models of every positive size. -/
theorem thm_finite_consistent_linear_models_000109_is_false : ¬(∀ n : ℕ, 1 ≤ n → ∃ (α : Type*) (_ : Fintype α) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α) (_ : ACR.C5 α), ACR.Consistent α ∧ (∀ x : α, x ≐ □x) ∧ (∀ x y : α, x ≤ y ∨ y ≤ x) ∧ (∀ x y : α, x ≤ y → y ≤ x → x = y) ∧ Nonempty (ACR.GödelFixpoint α) ∧ Fintype.card α = n) := by
  intro h
  specialize h 1 le_rfl
  rcases h with ⟨α, _, _, _, _, _, _, hcons, _, _, _, _, hcard⟩
  have hsub : Subsingleton α :=
    (Fintype.card_le_one_iff_subsingleton).mp (by exact Nat.le_of_eq hcard)
  haveI : Subsingleton α := hsub
  have hincon : ACR.Inconsistent α := by
    change ((⊤ : α) ≤ (⊥ : α))
    exact le_of_subsingleton
  exact (iff_false_intro hcons).mp hincon

/-- Finite linear consistent models with no Godel fixpoints of any size at least two. -/
theorem thm_finite_linear_no_godel_family_000110 : ∀ n : ℕ, 2 ≤ n → ∃ (α : Type*) (_ : Fintype α) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α) (_ : ACR.C5 α), ACR.Consistent α ∧ (∀ x : α, x ≐ □x) ∧ (∀ x y : α, x ≤ y ∨ y ≤ x) ∧ (∀ x y : α, x ≤ y → y ≤ x → x = y) ∧ IsEmpty (ACR.GödelFixpoint α) ∧ Fintype.card α = n := by
  intro n hn
  have hpos : 0 < n := by
    omega
  let α := ULift (Fin n)
  let b : α := ⟨⟨0, hpos⟩⟩
  let t : α := ⟨⟨n - 1, by
    exact Nat.sub_one_lt_of_lt hpos⟩⟩
  let provFn : α → α := fun x => x
  let reftFn : α → α := fun x => if x = b then t else b
  letI : Fintype α := inferInstance
  letI : ACR α :=
    { toTop := ⟨t⟩
      toBot := ⟨b⟩
      toPreorder := inferInstance }
  have hb_le_t : b ≤ t := by
    change b.down.val ≤ t.down.val
    exact (Nat.le_sub_one_iff_lt hpos).mpr hpos
  have ht_ne_b : t ≠ b := by
    intro h
    have hval : t.down.val = b.down.val := by
      exact Eq.symm
          ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (congrArg Fin.val (congrArg ULift.down (id (Eq.symm h))))))
    dsimp [b, t] at hval
    omega
  letI : ACR.Prov α := ⟨provFn⟩
  letI : ACR.Reft α := ⟨reftFn⟩
  letI : ACR.APS α :=
    { prov_mono := by
        intro x y hxy
        change provFn x ≤ provFn y
        exact le_of_eq_of_le rfl hxy
      reft_anti_mono := by
        intro x y hxy
        change reftFn y ≤ reftFn x
        by_cases hx : x = b
        · by_cases hy : y = b
          · simp [reftFn, hx, hy]
          · simp [reftFn, hx, hy, hb_le_t]
        · have hy : y ≠ b := by
            intro hy
            apply hx
            apply ULift.ext
            apply Fin.ext
            have hxle : x ≤ b := by
              exact le_of_le_of_eq hxy hy
            change x.down.val = b.down.val
            change x.down.val ≤ b.down.val at hxle
            exact Nat.eq_zero_of_le_zero hxle
          simp [reftFn, hx, hy]
      top_le_reft_bot := by
        change t ≤ reftFn b
        simp [reftFn]
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxr
        change x ≤ provFn y at hxy
        change x ≤ reftFn y at hxr
        change x ≤ reftFn t
        by_cases hy : y = b
        · have hxb : x ≤ b := by
            exact le_of_le_of_eq hxy hy
          simpa [reftFn, ht_ne_b] using hxb
        · have hxb : x ≤ b := by
            simpa [reftFn, hy] using hxr
          simpa [reftFn, ht_ne_b] using hxb
      reft_le_prov_reft := by
        intro x
        change reftFn x ≤ provFn (reftFn x)
        exact Std.IsPreorder.le_refl (reftFn x) }
  letI : ACR.C5 α :=
    { le_top := by
        intro x
        change x.down.val ≤ t.down.val
        dsimp [t]
        omega }
  have hcons : ACR.Consistent α := by
    intro hinc
    change t.down.val ≤ b.down.val at hinc
    dsimp [b, t] at hinc
    omega
  have hno : ¬ Nonempty (ACR.GödelFixpoint α) := by
    intro hg
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    have hirr : ¬ ((⊠(⊤ : α)) ≤ (⊥ : α)) := ACR.irrefutable_reft_top (α := α) hcons
    apply hirr
    change reftFn t ≤ b
    simp [reftFn, ht_ne_b]
  have hempty : IsEmpty (ACR.GödelFixpoint α) := not_nonempty_iff.mp hno
  refine ⟨α, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨hcons, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x
    constructor <;> change x ≤ provFn x <;> simp [provFn]
  refine ⟨?_, ?_⟩
  · exact fun x y => Std.IsLinearPreorder.le_total x y
  refine ⟨?_, ?_⟩
  · intro x y hxy hyx
    exact le_antisymm hxy hyx
  refine ⟨hempty, ?_⟩
  simp [α]

/-- A size-one ACR type is inconsistent. -/
theorem thm_card_one_inconsistent_000112 : ∀ (α : Type*) [Fintype α] [ACR α], Fintype.card α = 1 → ¬ ACR.Consistent α := by
  intro α _ _ hcard hC
  apply hC
  rw [Fintype.card_eq_one_iff] at hcard
  rcases hcard with ⟨x, hx⟩
  have htop : (⊤ : α) = x := hx _
  have hbot : (⊥ : α) = x := hx _
  have htb : (⊤ : α) = ⊥ := htop.trans hbot.symm
  simp [ACR.Inconsistent, htb]

/-- Finite consistent trivial-box chain models exist in every size at least two. -/
theorem thm_finite_trivial_box_chain_models_000113 : ∀ n : ℕ, 2 ≤ n → ∃ (α : Type*) (_ : Fintype α) (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α) (_ : ACR.C5 α), ACR.Consistent α ∧ (∀ x : α, x ≐ □x) ∧ (∀ x y : α, x ≤ y ∨ y ≤ x) ∧ (∀ x y : α, x ≤ y → y ≤ x → x = y) ∧ Nonempty (ACR.GödelFixpoint α) ∧ Fintype.card α = n := by
  intro n hn
  have hpos : 0 < n := by omega
  let b : ULift (Fin n) := ⟨⟨0, hpos⟩⟩
  let t : ULift (Fin n) := ⟨⟨n - 1, by exact Nat.sub_one_lt_of_lt hpos⟩⟩
  letI : LE (ULift (Fin n)) := ⟨fun x y => x.down ≤ y.down⟩
  letI : LT (ULift (Fin n)) := ⟨fun x y => x.down < y.down⟩
  letI : Top (ULift (Fin n)) := ⟨t⟩
  letI : Bot (ULift (Fin n)) := ⟨b⟩
  letI : Preorder (ULift (Fin n)) :=
    { le := (· ≤ ·)
      lt := (· < ·)
      le_refl := by
        exact fun a => Std.IsPreorder.le_refl a
      le_trans := by
        exact fun a b c a_1 a_2 => Std.IsPreorder.le_trans a b c a_1 a_2
      lt_iff_le_not_ge := by
        exact fun a b => Std.LawfulOrderLT.lt_iff a b }
  letI : ACR (ULift (Fin n)) :=
    { toTop := inferInstance
      toBot := inferInstance
      toPreorder := inferInstance }
  letI : ACR.Prov (ULift (Fin n)) := ⟨id⟩
  letI : ACR.Reft (ULift (Fin n)) := ⟨fun _ => t⟩
  letI : ACR.APS (ULift (Fin n)) :=
    { prov_mono := by
        intro x y hxy
        simpa using hxy
      reft_anti_mono := by
        intro x y hxy
        change t.down ≤ t.down
        exact Fin.ge_of_eq rfl
      top_le_reft_bot := by
        change t.down ≤ t.down
        exact Fin.ge_of_eq rfl
      le_reft_top_of_le_prov_of_le_reft := by
        intro x y hxy hxr
        simpa using hxr
      reft_le_prov_reft := by
        intro x
        change t.down ≤ t.down
        exact Fin.ge_of_eq rfl }
  letI : ACR.C5 (ULift (Fin n)) := ⟨by
    intro x
    change x.down.val ≤ n - 1
    exact Nat.le_pred_of_lt x.down.is_lt
  ⟩
  refine ⟨ULift (Fin n), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  constructor
  · intro h
    change n - 1 ≤ 0 at h
    omega
  constructor
  · intro x
    constructor <;> rfl
  constructor
  · exact fun x y => Std.IsLinearPreorder.le_total x y
  constructor
  · intro x y hxy hyx
    apply ULift.ext
    exact le_antisymm hxy hyx
  constructor
  · refine ⟨⟨t, ?_⟩⟩
    constructor <;> change t.down ≤ t.down <;> exact le_rfl
  · simp

/-- Finite consistent ACR structures exist exactly from size two onward. -/
theorem thm_finite_consistent_acr_threshold_000116 : ∀ n : ℕ, (∃ (α : Type*) (_ : Fintype α) (_ : ACR α), ACR.Consistent α ∧ Fintype.card α = n) ↔ 2 ≤ n := by
  intro n
  constructor
  · rintro ⟨α, hF, hA, hcons, hcard⟩
    letI : Fintype α := hF
    letI : ACR α := hA
    have hzero : n ≠ 0 := by
      intro hn0
      letI : Nonempty α := ⟨⊤⟩
      have hne : Fintype.card α ≠ 0 := Fintype.card_ne_zero
      apply hne
      simpa [hcard] using hn0
    have hone : n ≠ 1 := by
      intro hn1
      have hsub : Subsingleton α :=
        (Fintype.card_le_one_iff_subsingleton).mp (by simp [hcard, hn1])
      letI : Subsingleton α := hsub
      apply hcons
      change ((⊤ : α) ≤ (⊥ : α))
      exact le_of_subsingleton
    omega
  · intro hn
    rcases AutomatedTheoryConstruction.thm_finite_linear_no_godel_family_000110 n hn with
      ⟨α, hF, hA, hP, hR, hAPS, hC5, hcons, hbox, hlin, hanti, hnog, hcard⟩
    exact ⟨α, hF, hA, hcons, hcard⟩

/-- A greatest-element order admits identity box, constant reft, and a Godel fixpoint when consistent. -/
theorem thm_greatest_trivial_box_godel_000117 : ∀ (α : Type*) [ACR α], (∀ x : α, x ≤ (⊤ : α)) → ∃ (P : ACR.Prov α) (R : ACR.Reft α) (_ : @ACR.APS α _ P R), (∀ x : α, P.prov x = x) ∧ (∀ x : α, R.reft x = (⊤ : α)) ∧ (¬ ((⊤ : α) ≤ (⊥ : α)) → ACR.Consistent α ∧ Nonempty (@ACR.GödelFixpoint α _ R)) := by
  intro α _ htop
  let P : ACR.Prov α := { prov := fun x => x }
  let R : ACR.Reft α := { reft := fun _ => ⊤ }
  letI : ACR.Prov α := P
  letI : ACR.Reft α := R
  have hA : @ACR.APS α _ P R := by
    refine
      { prov_mono := ?_
        reft_anti_mono := ?_
        top_le_reft_bot := ?_
        le_reft_top_of_le_prov_of_le_reft := ?_
        reft_le_prov_reft := ?_ }
    · intro x y hxy
      exact hxy
    · intro x y hxy
      exact le_rfl
    · exact le_rfl
    · intro x y hxy hyr
      exact htop x
    · intro x
      exact le_rfl
  refine ⟨P, R, hA, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro h
    constructor
    · exact h
    · refine ⟨⟨⊤, ?_⟩⟩
      constructor <;> exact le_rfl

/-- Every cardinal except one admits a consistent total antisymmetric trivial-box model with a Gödel fixpoint. -/
theorem thm_cardinal_godel_model_exists_000118_is_false : ¬(∀ κ : Cardinal, κ ≠ 1 → ∃ α : Type*, ∃ _ : ACR α, ∃ _ : ACR.Prov α, ∃ _ : ACR.Reft α, ∃ _ : ACR.APS α, ∃ _ : ACR.C5 α, ACR.Consistent α ∧ (∀ x : α, x ≐ □x) ∧ (∀ x y : α, x ≤ y ∨ y ≤ x) ∧ (∀ x y : α, x ≤ y → y ≤ x → x = y) ∧ Nonempty (ACR.GödelFixpoint α) ∧ Cardinal.lift (Cardinal.mk α) = κ) := by
  intro h
  rcases h 0 (by simp) with ⟨α, hACR, hProv, hReft, hAPS, hC5, hCons, hBox, hTot, hAnti, hGF, hκ⟩
  letI := hACR
  have hmk : Cardinal.mk α = 0 := by
    exact Eq.symm ((fun {a} => Cardinal.zero_eq_lift_iff.mp) (id (Eq.symm hκ)))
  have hEmpty : IsEmpty α := Cardinal.mk_eq_zero_iff.mp hmk
  exact hEmpty.false (⊤ : α)

/-- Consistent ACR structures exist exactly on nontrivial types. -/
theorem thm_consistent_acr_iff_nontrivial_000119 : ∀ α : Type*, (∃ h : ACR α, @ACR.Consistent α h) ↔ Nontrivial α := by
  intro α
  constructor
  · rintro ⟨h, hc⟩
    letI : ACR α := h
    refine ⟨⟨⊤, ⊥, ?_⟩⟩
    intro hEq
    apply hc
    change (⊤ : α) ≤ ⊥
    exact Std.le_of_eq hEq
  · intro hnt
    letI : Nontrivial α := hnt
    obtain ⟨t, b, htb⟩ := exists_pair_ne α
    let h : ACR α :=
      { top := t
        bot := b
        le := fun x y => x = y
        le_refl := by
          exact fun a => ((fun a => a) ∘ fun a => a) rfl
        le_trans := by
          exact fun a b c a_1 a_2 => cast (congrArg (Eq a) a_2) a_1 }
    refine ⟨h, ?_⟩
    change ¬ ((t : α) = b)
    exact Ne.intro htb

/-- An `ACR` structure exists exactly on nonempty types. -/
theorem thm_acr_exists_iff_nonempty_000123 : ∀ α : Type*, (∃ h : ACR α, True) ↔ Nonempty α := by
  intro α
  constructor
  · rintro ⟨_, -⟩
    exact bot_nonempty α
  · rintro ⟨a⟩
    refine ⟨{
      top := a
      bot := a
      le := fun _ _ => True
      le_refl := by
        intro x
        trivial
      le_trans := by
        intro a b c hab hbc
        trivial
    }, trivial⟩

/-- Universal ACR inconsistency characterizes subsingleton carriers. -/
theorem thm_all_acr_inconsistent_iff_subsingleton_000124 : ∀ α : Type*, (∀ h : ACR α, ¬ @ACR.Consistent α h) ↔ Subsingleton α := by
  classical
  intro α
  constructor
  · intro h
    rw [subsingleton_iff]
    intro a b
    by_contra hne
    letI : ACR α :=
      { top := a
        bot := b
        le := Eq
        lt := fun _ _ => False
        le_refl := by
          exact fun a => ((fun a => a) ∘ fun a => a) rfl
        le_trans := by
          exact fun a b c a_2 a_3 => cast (congrArg (Eq a) a_3) a_2
        lt_iff_le_not_ge := by
          intro x y
          constructor
          · intro hlt
            cases hlt
          · rintro ⟨hxy, hyx⟩
            exact Ne.elim hyx (id (Eq.symm hxy)) }
    have hcons : @ACR.Consistent α inferInstance := by
      intro hab
      exact hne hab
    exact (iff_false_intro (h this)).mp hcons
  · intro hs h
    letI : ACR α := h
    intro hcons
    apply hcons
    simp [ACR.Inconsistent, Subsingleton.elim (⊤ : α) (⊥ : α)]

abbrev CanonicalRealization (α : Type*) [LinearOrder α] [BoundedOrder α] [Nontrivial α] : Prop :=
  ∃ (hA : ACR α) (hP : @ACR.Prov α hA) (hR : @ACR.Reft α hA)
    (hAPS : @ACR.APS α hA hP hR) (_hC5 : @ACR.C5 α hA hP hR hAPS),
    (∀ x : α, @ACR.Prov.prov α hA hP x = x) ∧
    (∀ x : α, @ACR.Reft.reft α hA hR x = @Top.top α hA.toTop) ∧
    @ACR.Consistent α hA ∧ Nonempty (@ACR.GödelFixpoint α hA hR)

/-- Every nontrivial bounded linear order has a consistent canonical realization with a Godel fixpoint. -/
theorem thm_bounded_linear_canonical_realization_000122 : ∀ (α : Type*) [LinearOrder α] [BoundedOrder α] [Nontrivial α], CanonicalRealization α := by
  intro α _ _ _
  let hA : ACR α :=
    { toTop := inferInstance
      toBot := inferInstance
      toPreorder := inferInstance }
  letI : ACR α := hA
  have htop : ∀ x : α, x ≤ (⊤ : α) := fun x => le_top
  rcases AutomatedTheoryConstruction.thm_greatest_trivial_box_godel_000117 α htop with
    ⟨hP, hR, hAPS, hbox, hreft, hgood⟩
  letI : ACR.Prov α := hP
  letI : ACR.Reft α := hR
  letI : ACR.APS α := hAPS
  have hC5 : @ACR.C5 α hA hP hR hAPS :=
    { le_top := fun {x} => le_top }
  have hnot : ¬ ((⊤ : α) ≤ (⊥ : α)) := by
    intro h
    exact top_ne_bot (le_antisymm h bot_le)
  have hcg : ACR.Consistent α ∧ Nonempty (ACR.GödelFixpoint α) := hgood hnot
  exact ⟨hA, hP, hR, hAPS, hC5, hbox, hreft, hcg.1, hcg.2⟩

/-- Full trivial-box realizations exist exactly on nonempty types. -/
theorem thm_trivial_box_package_iff_nonempty_000125 : ∀ α : Type*, (∃ (_ : ACR α) (_ : ACR.Prov α) (_ : ACR.Reft α) (_ : ACR.APS α) (_ : ACR.C5 α), ∀ x : α, x ≐ □x) ↔ Nonempty α := by
  classical
  intro α
  constructor
  · intro h
    rcases h with ⟨hA, _, _, _, _, _⟩
    exact bot_nonempty α
  · intro h
    rcases h with ⟨a⟩
    let instA : ACR α :=
      { top := a
        bot := a
        le := fun _ _ => True
        le_refl := by
          exact fun a => True.intro
        le_trans := by
          exact fun a b c a_2 a_3 => True.intro }
    letI : ACR α := instA
    let instP : ACR.Prov α := { prov := fun x => x }
    letI : ACR.Prov α := instP
    let instR : ACR.Reft α := { reft := fun x => x }
    letI : ACR.Reft α := instR
    let instAPS : ACR.APS α :=
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
    letI : ACR.APS α := instAPS
    let instC5 : ACR.C5 α :=
      { le_top := by
          intro _
          trivial }
    refine ⟨instA, instP, instR, instAPS, instC5, ?_⟩
    intro x
    constructor <;> trivial

/-- Consistent trivial-box realizations exist exactly on nontrivial types. -/
theorem thm_consistent_trivial_box_nontrivial_000126 : ∀ α : Type*, (∃ hA : ACR α, ∃ hP : @ACR.Prov α hA, ∃ hR : @ACR.Reft α hA, ∃ hAPS : @ACR.APS α hA hP hR, ∃ hC5 : @ACR.C5 α hA hP hR hAPS, @ACR.Consistent α hA ∧ ∀ x : α, @ACR.Equivalent α hA x (@ACR.Prov.prov α hA hP x)) ↔ Nontrivial α := by
  intro α
  constructor
  · rintro ⟨hA, hP, hR, hAPS, _, hCons, hEq⟩
    exact (thm_consistent_acr_iff_nontrivial_000119 α).mp ⟨hA, hCons⟩
  · intro hN
    classical
    letI : Nontrivial α := hN
    obtain ⟨bot0, top0, hne⟩ := exists_pair_ne α
    let hA : ACR α :=
      { top := top0
        bot := bot0
        le := fun x y => x = bot0 ∨ y = top0 ∨ x = y
        le_refl := by
          intro x
          exact Or.inr (Or.inr rfl)
        le_trans := by
          intro a b c hab hbc
          rcases hab with ha | hb | hab
          · exact Or.symm (Or.inr ha)
          · rcases hbc with hb' | hc | hbc'
            · exfalso
              exact hne (hb'.symm.trans hb)
            · exact Or.inr (Or.inl hc)
            · exact Or.inr (Or.inl (hbc'.symm ▸ hb))
          · simpa [hab] using hbc }
    let hP : @ACR.Prov α hA := { prov := fun x => x }
    let hR : @ACR.Reft α hA := { reft := fun _ => top0 }
    let hAPS : @ACR.APS α hA hP hR :=
      { prov_mono := by
          intro x y hxy
          simpa using hxy
        reft_anti_mono := by
          intro x y hxy
          exact Or.inr (Or.inl rfl)
        top_le_reft_bot := by
          exact Or.inr (Or.inl rfl)
        le_reft_top_of_le_prov_of_le_reft := by
          intro x y hxy hxr
          exact Or.inr (Or.inl rfl)
        reft_le_prov_reft := by
          intro x
          exact Or.inr (Or.inl rfl) }
    let hC5 : @ACR.C5 α hA hP hR hAPS :=
      { le_top := by
          intro x
          exact Or.inr (Or.inl rfl) }
    letI : ACR α := hA
    letI : ACR.Prov α := hP
    letI : ACR.Reft α := hR
    letI : ACR.APS α := hAPS
    letI : ACR.C5 α := hC5
    refine ⟨hA, hP, hR, hAPS, hC5, ?_⟩
    constructor
    · intro hIncon
      rcases hIncon with htb | hbt | htb
      · exact hne htb.symm
      · exact hne hbt
      · exact hne htb.symm
    · intro x
      constructor <;> exact Or.inr (Or.inr rfl)

/-- Universal trivial-box realizations classify Henkin fixed points by nonemptiness. -/
theorem thm_henkin_fixpoint_nonempty_classification_000128 : ∀ (α : Type*) [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (∀ x : α, x ≐ □x) → ((Nonempty (ACR.HenkinFixpoint α) ↔ Nonempty α) ∧ ∀ x : α, ∃ h : ACR.HenkinFixpoint α, h.1 = x) := by
  intro α _ _ _ _ _ hbox
  constructor
  · constructor
    · exact fun a => bot_nonempty α
    · intro h
      rcases h with ⟨x⟩
      exact ⟨⟨x, hbox x⟩⟩
  · exact fun x => CanLift.prf x (hbox x)

/-- Gödel fixed points exist exactly when top is realized, and all are top. -/
theorem thm_godel_fixpoints_are_top_000127 : ∀ (α : Type*) [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ACR.Consistent α → (∀ x : α, x ≐ □x) → (∀ x : α, ⊠x ≐ (⊤ : α)) → ((Nonempty (ACR.GödelFixpoint α) ↔ ∃ x : α, x ≐ (⊤ : α)) ∧ ∀ g : ACR.GödelFixpoint α, g.1 ≐ (⊤ : α)) := by
  intro α _ _ _ _ _ _ _ hReftTop
  have hgf_top : ∀ g : ACR.GödelFixpoint α, g.1 ≐ (⊤ : α) := by
    intro g
    have hg_reft_top : g.1 ≐ ⊠(⊤ : α) := ACR.gf_equiv_reft_top (g := g)
    have hreft_top : ⊠(⊤ : α) ≐ (⊤ : α) := hReftTop (⊤ : α)
    exact ⟨le_trans hg_reft_top.1 hreft_top.1, le_trans hreft_top.2 hg_reft_top.2⟩
  constructor
  · constructor
    · intro h
      obtain ⟨g⟩ := h
      exact ⟨g.1, hgf_top g⟩
    · intro h
      obtain ⟨x, hx⟩ := h
      refine ⟨⟨x, ?_⟩⟩
      have hreft_x : ⊠x ≐ (⊤ : α) := hReftTop x
      exact ⟨le_trans hx.1 hreft_x.2, le_trans hreft_x.1 hx.2⟩
  · exact fun g => ((fun a => hgf_top g) ∘ fun a => α) α

/-- Universal reflection fixedness implies inconsistency. -/
theorem thm_universal_reft_fixed_inconsistent_000132 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (∀ x : α, x ≐ ⊠x) → ACR.Inconsistent α := by
  intro α _ _ _ _ h
  exact le_trans ACR.top_le_reft_bot (h ⊥).2


noncomputable abbrev chosen_canonical_acr (α : Type*) [LinearOrder α] [BoundedOrder α] [Nontrivial α] : ACR α :=
  Classical.choose (thm_bounded_linear_canonical_realization_000122 (α := α))

noncomputable abbrev chosen_canonical_reft (α : Type*) [LinearOrder α] [BoundedOrder α] [Nontrivial α] :
    @ACR.Reft α (chosen_canonical_acr α) :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec (thm_bounded_linear_canonical_realization_000122 (α := α))))

/-- Every Godel fixpoint in the chosen canonical realization is equivalent to top. -/
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
