import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.

section FixpointBasics

variable {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α]

/-- In a consistent ACR, every Gödel fixpoint is not refutable. -/
theorem thm_consistent_godel_fixpoint_not_refutable_000007 :
    ACR.Consistent α → ∀ g : ACR.GödelFixpoint α, ¬ (⊬ g.1) := by
  intro hCons g
  intro hgref
  have h₁ : (g.1 : α) ≤ (⊥ : α) := hgref
  have h₂ : (⊠ (⊥ : α) : α) ≤ ⊠ g.1 := ACR.reft_anti_mono h₁
  have h₃ : (⊠ (⊥ : α) : α) ≤ g.1 := le_trans h₂ g.2.2
  have hIncon : ACR.Inconsistent α :=
    le_trans (le_trans (ACR.top_le_reft_bot (α := α)) h₃) h₁
  exact hCons hIncon

/-- Assuming consistency, `□(⊠g)` is not refutable for any Gödel fixpoint `g`. -/
theorem thm_godel_fixpoint_box_reft_not_refutable_000003 :
    ACR.Consistent α → ∀ g : ACR.GödelFixpoint α, ¬ (⊬ □(⊠ g.1)) := by
  intro hCons g
  intro href
  have hreft : (⊠ g.1 : α) ≤ □(⊠ g.1) := by
    simpa using (ACR.reft_le_prov_reft (x := (g.1 : α)))
  have hbot : (⊠ g.1 : α) ≤ (⊥ : α) := le_trans hreft href
  have hg : (g.1 : α) ≤ (⊥ : α) := le_trans g.2.1 hbot
  exact (thm_consistent_godel_fixpoint_not_refutable_000007 (α := α) hCons g) hg

/-- Every Gödel fixpoint is below `□(⊠⊤)`. -/
theorem thm_godel_fixpoint_le_box_reft_top_000001 :
    ∀ g : ACR.GödelFixpoint α, g.1 ≤ □(⊠(⊤ : α)) := by
  intro g
  exact le_trans (ACR.gf_le_reft_top (g := g)) (ACR.reft_le_prov_reft (x := (⊤ : α)))

/-- Every Gödel fixpoint is less than or equal to its provability image. -/
theorem thm_godel_fixpoint_le_box_self_000009 :
    ∀ g : ACR.GödelFixpoint α, g.1 ≤ ACR.Prov.prov g.1 := by
  intro g
  exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))

/-- A Henkin fixpoint below its refutation is below `□(⊠⊤)`. -/
theorem thm_henkin_fixpoint_le_box_reft_top_000002 :
    ∀ h : ACR.HenkinFixpoint α, h.1 ≤ ⊠h.1 → h.1 ≤ □(⊠(⊤ : α)) := by
  intro h hh
  have hle : h.1 ≤ □(h.1) := by
    simpa using h.2.1
  have hle_reft_top : h.1 ≤ ⊠(⊤ : α) :=
    ACR.le_reft_top_of_le_prov_of_le_reft (x := h.1) (y := h.1) hle (by simpa using hh)
  have hbox : □(h.1) ≤ □(⊠(⊤ : α)) :=
    ACR.prov_mono hle_reft_top
  exact le_trans hle hbox

end FixpointBasics

section ExistenceFromIdempotence

variable {α : Type _} [ACR α] [ACR.Reft α]

/-- If `⊠⊤` is equivalent to `⊠⊠⊤`, then a Gödel fixpoint exists. -/
theorem thm_godel_fixpoint_of_reft_top_equiv_double_000014 :
    (⊠(⊤ : α)) ≐ (⊠⊠(⊤ : α)) → Nonempty (ACR.GödelFixpoint α) := by
  intro h
  refine ⟨⟨⊠(⊤ : α), ?_⟩⟩
  simpa using h

end ExistenceFromIdempotence

section C5Inventory

variable {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α]

private lemma reft_top_le_double_reft_top :
    (⊠(⊤ : α)) ≤ (⊠⊠(⊤ : α)) := by
  have hx : (⊠(⊤ : α)) ≤ (⊤ : α) := by
    simpa using (ACR.le_top (x := (⊠(⊤ : α))))
  simpa using (ACR.reft_anti_mono (x := (⊠(⊤ : α))) (y := (⊤ : α)) hx)

/-- Assuming C5 and a Gödel fixpoint, `⊠⊤` is equivalent to `⊠⊠⊤`. -/
theorem thm_reft_top_equiv_double_reft_top_000008 :
    Nonempty (ACR.GödelFixpoint α) → (⊠(⊤ : α)) ≐ (⊠⊠(⊤ : α)) := by
  intro hg
  constructor
  · exact reft_top_le_double_reft_top (α := α)
  ·
    letI : Nonempty (ACR.GödelFixpoint α) := hg
    simpa using (ACR.reft_reft_top_le_reft_top (α := α))

/-- Under C5, every Gödel fixpoint is equivalent to `⊠⊠⊤`. -/
theorem thm_godel_fixpoint_equiv_double_reft_top_000004 :
    ∀ g : ACR.GödelFixpoint α, g.1 ≐ ⊠⊠(⊤ : α) := by
  intro g
  have hTop : g.1 ≐ (⊠(⊤ : α)) := by
    simpa using (ACR.gf_equiv_reft_top (g := g))
  have hIdem : (⊠(⊤ : α)) ≐ (⊠⊠(⊤ : α)) :=
    thm_reft_top_equiv_double_reft_top_000008 (α := α) ⟨g⟩
  constructor
  · exact le_trans hTop.1 hIdem.1
  · exact le_trans hIdem.2 hTop.2

/-- Assuming C5, all Gödel fixpoints are equivalent (uniqueness up to `≐`). -/
theorem main_thm_godel_fixpoint_unique_equiv :
    ∀ g₁ g₂ : ACR.GödelFixpoint α, g₁.1 ≐ g₂.1 := by
  intro g₁ g₂
  have h₁ : g₁.1 ≐ (⊠(⊤ : α)) := by
    simpa using (ACR.gf_equiv_reft_top (g := g₁))
  have h₂ : g₂.1 ≐ (⊠(⊤ : α)) := by
    simpa using (ACR.gf_equiv_reft_top (g := g₂))
  constructor
  · exact le_trans h₁.1 h₂.2
  · exact le_trans h₂.1 h₁.2

/-- Gödel fixpoints exist if and only if `⊠` is idempotent on top (under the current ACR/APS/C5 assumptions). -/
theorem main_thm_godel_fixpoint_iff_reft_top_idempotent :
    Nonempty (ACR.GödelFixpoint α) ↔ (⊠(⊤ : α)) ≐ (⊠⊠(⊤ : α)) := by
  constructor
  · intro hg
    exact thm_reft_top_equiv_double_reft_top_000008 (α := α) hg
  · intro h
    exact thm_godel_fixpoint_of_reft_top_equiv_double_000014 (α := α) h

/-- Gödel fixpoints exist iff `⊠⊤` is equivalent to `⊠⊠⊤`. -/
theorem thm_godel_fixpoint_nonempty_iff_reft_top_idempotent_000016 :
    Nonempty (ACR.GödelFixpoint α) ↔ (⊠(⊤ : α) ≐ ⊠⊠(⊤ : α)) := by
  simpa using (main_thm_godel_fixpoint_iff_reft_top_idempotent (α := α))

end C5Inventory

end AutomatedTheoryConstruction
