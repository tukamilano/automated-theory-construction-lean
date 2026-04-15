import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0001_godel_henkin_fixpoint

set_option autoImplicit false

namespace AutomatedTheoryConstruction

universe u

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
  rcases hex with ⟨hR, hA, _hconst⟩
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
    Monotone.monotone_iterate_of_le_map hmono (by simpa [f] using hg)
  refine ⟨⟨f^[m] g.1, ?_⟩⟩
  constructor
  · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
  · have hle : f^[m + 1] g.1 ≤ f^[n] g.1 := horbit (Nat.succ_le_of_lt hmn)
    simpa [f, Function.iterate_succ_apply'] using le_trans hle heq.2

/-- A constant reflection operator exists exactly for postfixed constants above top. -/
theorem thm_constant_reft_iff_bounds_000044 : ∀ {α : Type*} [ACR α] [ACR.Prov α] (c : α), Monotone (fun x : α => □x) → ((∃ hR : ACR.Reft α, ∃ hA : @ACR.APS α _ _ hR, ∀ x : α, @ACR.Reft.reft α _ hR x = c) ↔ ((⊤ : α) ≤ c ∧ c ≤ □c)) := by
  intro α _ _ c hmono
  constructor
  · rintro ⟨hR, hA, hconst⟩
    letI : ACR.Reft α := hR
    letI : ACR.APS α := hA
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
    · intro x y hxy
      exact hm hxy
    · intro x y hxy
      change c ≤ c
      exact le_rfl
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
  rcases hleft with ⟨c, hR, hA, hconst⟩
  letI : ACR.Reft (ULift Op000035Bool) := hR
  letI : ACR.APS (ULift Op000035Bool) := hA
  have hbounds := (thm_constant_reft_iff_bounds_000044 (α := ULift Op000035Bool) (c := c) hMono).1 ⟨hR, hA, hconst⟩
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
    Monotone.monotone_iterate_of_le_map hmono (by simpa [f] using hx)
  let s : Set α := {y : α | ∃ n : ℕ, f^[n] x = y}
  have hsfin : s.Finite := by
    simpa [s] using hfin
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
    Monotone.monotone_iterate_of_le_map hmono (by simpa [f] using hx)
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
    Monotone.monotone_iterate_of_le_map hmono (by simpa [f] using hx)
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

end AutomatedTheoryConstruction
