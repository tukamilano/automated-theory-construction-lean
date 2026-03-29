import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


/-- A Godel fixpoint exists if reflection at top is idempotent. -/
theorem thm_godel_fixpoint_exists_of_top_reft_idempotence_000001 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) → Nonempty (ACR.GödelFixpoint α) := by
  intro α _ _ _ _ h
  exact ⟨⟨⊠(⊤ : α), ⟨h.2, h.1⟩⟩⟩


/-- Under C5, any two Godel fixpoints are equivalent. -/
theorem thm_godel_fixpoints_equivalent_under_c5_000003 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, g.1 ≐ h.1 := by
  intro α _ _ _ _ _ g h
  have hg : g.1 ≐ ⊠⊤ := ACR.gf_equiv_reft_top
  have hh : h.1 ≐ ⊠⊤ := ACR.gf_equiv_reft_top
  exact ⟨le_trans hg.1 hh.2, le_trans hh.1 hg.2⟩


/-- A Godel fixpoint exists exactly when reft top is idempotent. -/
theorem thm_godel_fixpoint_exists_iff_reft_top_idempotent_000005 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], Nonempty (ACR.GödelFixpoint α) ↔ (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) := by
  intro α _ _ _ _ _
  constructor
  · intro h
    constructor
    · letI : Nonempty (ACR.GödelFixpoint α) := h
      simpa using (ACR.reft_reft_top_le_reft_top (α := α))
    · obtain ⟨g⟩ := h
      have hg := ACR.gf_equiv_reft_top (α := α) (g := g)
      calc
        ⊠(⊤ : α) ≤ g.1 := hg.2
        _ ≤ ⊠g.1 := g.2.1
        _ ≤ ⊠⊠(⊤ : α) := by
          apply ACR.reft_anti_mono
          exact hg.2
  · intro h
    simpa using thm_godel_fixpoint_exists_of_top_reft_idempotence_000001 (α := α) h


/-- Every Godel fixpoint is irrefutable in a consistent ACR. -/
theorem thm_consistent_godel_fixpoint_irrefutable_000002 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ACR.Consistent α → ∀ g : ACR.GödelFixpoint α, ¬ (⊬ g.1) := by
  intro α _ _ _ _ hC g hg
  apply hC
  calc
    ⊤ ≤ ⊠⊥ := ACR.top_le_reft_bot
    _ ≤ ⊠g.1 := ACR.reft_anti_mono hg
    _ ≤ g.1 := g.2.2
    _ ≤ ⊥ := hg


/-- A Henkin fixpoint below its refutation is equivalent to refutation of top. -/
theorem thm_henkin_fixpoint_equiv_reft_top_000004_is_false : ¬(∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {h : ACR.HenkinFixpoint α}, h.1 ≤ ⊠h.1 → h.1 ≐ ⊠(⊤ : α)) := by
  intro hs
  let T := ULift Bool
  letI : ACR T :=
    ACR.mk (α := T)
      (le_refl := by
        intro a
        exact le_rfl)
      (le_trans := by
        intro a b c hab hbc
        exact le_trans hab hbc)
      (lt_iff_le_not_ge := by
        intro a b
        exact lt_iff_le_not_ge)
  let provT : ACR.Prov T := ACR.Prov.mk id
  let reftT : ACR.Reft T := ACR.Reft.mk (fun _ => ⊤)
  letI : ACR.Prov T := provT
  letI : ACR.Reft T := reftT
  let apsT : ACR.APS T :=
    ACR.APS.mk
      (prov_mono := by
        intro x y hxy
        simpa [provT] using hxy)
      (reft_anti_mono := by
        intro _ _ _
        exact le_rfl)
      (top_le_reft_bot := by
        exact le_rfl)
      (le_reft_top_of_le_prov_of_le_reft := by
        intro _ _ _ _
        exact le_top)
      (reft_le_prov_reft := by
        intro _
        exact le_rfl)
  letI : ACR.APS T := apsT
  letI : ACR.C5 T := ACR.C5.mk (le_top := by
    intro _
    exact le_top)
  let h : ACR.HenkinFixpoint T := ⟨⊥, ⟨le_rfl, le_rfl⟩⟩
  have hEq : h.1 ≐ ⊠(⊤ : T) := hs (α := T) (h := h) le_top
  have htb : (⊤ : T) ≤ ⊥ := by
    simpa [h, reftT] using hEq.2
  have hnot : ¬ ((⊤ : T) ≤ (⊥ : T)) := by
    decide
  exact hnot htb


/-- Reft-top idempotence is equivalent to existence of an essentially unique Godel fixpoint up to equivalence. -/
theorem main_thm_godel_fixpoint_exists_iff_essentially_unique : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ↔ ∃ g : ACR.GödelFixpoint α, ∀ h : ACR.GödelFixpoint α, h.1 ≐ g.1 := by
  intro α _ _ _ _ _
  constructor
  · intro h
    obtain ⟨g⟩ := thm_godel_fixpoint_exists_of_top_reft_idempotence_000001 (α := α) h
    refine ⟨g, ?_⟩
    intro hfix
    simpa using thm_godel_fixpoints_equivalent_under_c5_000003 (α := α) hfix g
  · rintro ⟨g, _⟩
    simpa using
      (thm_godel_fixpoint_exists_iff_reft_top_idempotent_000005 (α := α)).mp
        (show Nonempty (ACR.GödelFixpoint α) from ⟨g⟩)


/-- Any Henkin fixpoint is equivalent to reft top when a Godel fixpoint exists. -/
theorem thm_henkin_fixpoint_equiv_reft_top_of_godel_exists_000015_is_false : ¬(∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] {h : ACR.HenkinFixpoint α}, Nonempty (ACR.GödelFixpoint α) → h.1 ≐ ⊠(⊤ : α)) := by
  intro hstmt
  let T := ULift Bool
  letI : ACR T :=
    ACR.mk (α := T)
      (le_refl := by
        intro a
        exact le_rfl)
      (le_trans := by
        intro a b c hab hbc
        exact le_trans hab hbc)
      (lt_iff_le_not_ge := by
        intro a b
        exact lt_iff_le_not_ge)
  let provT : ACR.Prov T := ACR.Prov.mk id
  let reftT : ACR.Reft T := ACR.Reft.mk (fun _ => ⊤)
  letI : ACR.Prov T := provT
  letI : ACR.Reft T := reftT
  let apsT : ACR.APS T :=
    ACR.APS.mk
      (prov_mono := by
        intro x y hxy
        simpa [provT] using hxy)
      (reft_anti_mono := by
        intro _ _ _
        exact le_rfl)
      (top_le_reft_bot := by
        exact le_rfl)
      (le_reft_top_of_le_prov_of_le_reft := by
        intro _ _ _ _
        exact le_top)
      (reft_le_prov_reft := by
        intro _
        exact le_rfl)
  letI : ACR.APS T := apsT
  letI : ACR.C5 T := ACR.C5.mk (le_top := by
    intro _
    exact le_top)
  let h : ACR.HenkinFixpoint T := ⟨⊥, ⟨le_rfl, le_rfl⟩⟩
  let g : ACR.GödelFixpoint T := ⟨⊤, ⟨le_rfl, le_rfl⟩⟩
  let hg : Nonempty (ACR.GödelFixpoint T) := ⟨g⟩
  have hEq : h.1 ≐ ⊠(⊤ : T) := hstmt (α := T) (h := h) hg
  have htb : (⊤ : T) ≤ ⊥ := by
    simpa [h, reftT] using hEq.2
  have hnot : ¬ ((⊤ : T) ≤ (⊥ : T)) := by
    decide
  exact hnot htb


/-- A structure may satisfy reft-top idempotence yet have a Henkin fixpoint not equivalent to reft-top. -/
theorem thm_henkin_counterexample_with_reft_top_idempotence_000018 : ∃ (α : Type _), ∃ (hACR : ACR α), ∃ (hProv : ACR.Prov α), ∃ (hReft : ACR.Reft α), ∃ (hAPS : ACR.APS α), ∃ (hC5 : ACR.C5 α), letI : ACR α := hACR; letI : ACR.Prov α := hProv; letI : ACR.Reft α := hReft; letI : ACR.APS α := hAPS; letI : ACR.C5 α := hC5; (⊠⊠(⊤ : α) ≐ ⊠(⊤ : α)) ∧ ∃ h : ACR.HenkinFixpoint α, h.1 ≤ ⊠h.1 ∧ ¬ (h.1 ≐ ⊠(⊤ : α)) := by
  let leU : ULift Bool → ULift Bool → Prop := fun a b => a.down = false ∨ b.down = true
  let hACR : ACR (ULift Bool) :=
    { top := ⟨true⟩
      bot := ⟨false⟩
      le := leU
      lt := fun a b => leU a b ∧ ¬ leU b a
      le_refl := by
        intro x
        cases x with
        | up x =>
            cases x with
            | false => exact Or.inl rfl
            | true => exact Or.inr rfl
      le_trans := by
        intro x y z hxy hyz
        cases x with
        | up x =>
            cases y with
            | up y =>
                cases z with
                | up z =>
                    cases x <;> cases y <;> cases z <;> simp [leU] at hxy hyz ⊢
      lt_iff_le_not_ge := by
        intro a b
        rfl }
  let hProv : ACR.Prov (ULift Bool) := ⟨id⟩
  let hReft : ACR.Reft (ULift Bool) := ⟨fun _ => ⟨true⟩⟩
  letI : ACR (ULift Bool) := hACR
  letI : ACR.Prov (ULift Bool) := hProv
  letI : ACR.Reft (ULift Bool) := hReft
  let hAPS : ACR.APS (ULift Bool) :=
    { prov_mono := by
        intro x y hxy
        simpa using hxy
      reft_anti_mono := by
        intro _ _ _
        exact Or.inr rfl
      top_le_reft_bot := by
        exact Or.inr rfl
      le_reft_top_of_le_prov_of_le_reft := by
        intro _ _ _ _
        exact Or.inr rfl
      reft_le_prov_reft := by
        intro _
        exact Or.inr rfl }
  letI : ACR.APS (ULift Bool) := hAPS
  let hC5 : ACR.C5 (ULift Bool) :=
    ⟨by
      intro x
      cases x with
      | up x =>
          cases x with
          | false => exact Or.inl rfl
          | true => exact Or.inr rfl⟩
  letI : ACR.C5 (ULift Bool) := hC5
  refine ⟨ULift Bool, hACR, hProv, hReft, hAPS, hC5, ?_⟩
  constructor
  · exact ⟨Or.inr rfl, Or.inr rfl⟩
  · refine ⟨⟨⟨false⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact Or.inr rfl
    · intro hEq
      rcases hEq with ⟨_, hEq₂⟩
      cases hEq₂ with
      | inl h => cases h
      | inr h => cases h

end AutomatedTheoryConstruction
