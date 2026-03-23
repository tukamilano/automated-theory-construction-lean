import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


theorem thm_godel_fixpoint_le_prov_000001 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α], ∀ g : ACR.GödelFixpoint α, g.1 ≤ □g.1 := by
  intro α _ _ _ _ g
  exact le_trans g.2.1 (ACR.reft_gf_le_box_gf (g := g))


theorem thm_godel_fixpoints_equivalent_000002 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], ∀ g h : ACR.GödelFixpoint α, g.1 ≡ h.1 := by
  intro α _ _ _ _ _ g h
  have hg : g.1 ≡ ⊠(⊤ : α) := ACR.gf_equiv_reft_top (g := g)
  have hh : h.1 ≡ ⊠(⊤ : α) := ACR.gf_equiv_reft_top (g := h)
  constructor
  · exact le_trans hg.1 hh.2
  · exact le_trans hh.1 hg.2


theorem thm_reft_top_equiv_double_reft_top_000003 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ⊠(⊤ : α) ≡ ⊠⊠(⊤ : α) := by
  intro α _ _ _ _ _ _
  constructor
  · simpa using (ACR.reft_anti_mono (x := ⊠(⊤ : α)) (y := (⊤ : α)) (ACR.le_top (x := ⊠(⊤ : α))))
  · simpa using (ACR.reft_reft_top_le_reft_top (α := α))


theorem thm_exists_godel_fixpoint_equiv_reft_top_000004 : ∀ {α : Type u} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], ∃ g : ACR.GödelFixpoint α, g.1 ≡ ⊠(⊤ : α) := by
  intro α _ _ _ _ _ h
  let g : ACR.GödelFixpoint α := Classical.choice h
  exact ⟨g, ACR.gf_equiv_reft_top (g := g)⟩


theorem thm_henkin_fixpoint_nonempty_000005 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)], Nonempty (ACR.HenkinFixpoint α) := by
  intro α _ _ _ _ _ _
  refine ⟨⟨(⊤ : α), ?_⟩⟩
  constructor
  · calc
      (⊤ : α) ≤ ⊠(⊥ : α) := ACR.top_le_reft_bot
      _ ≤ □⊠(⊥ : α) := ACR.reft_le_prov_reft (x := (⊥ : α))
      _ ≤ □(⊤ : α) := ACR.prov_mono (ACR.le_top (x := (⊠(⊥ : α))))
  · exact ACR.le_top (x := (□(⊤ : α)))


theorem thm_godel_fixpoints_equal_of_antisymm_000007 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α], (∀ ⦃x y : α⦄, x ≤ y → y ≤ x → x = y) → ∀ g h : ACR.GödelFixpoint α, g = h := by
  intro α _ _ _ _ _ hanti g h
  have hEquiv : g.1 ≡ h.1 := thm_godel_fixpoints_equivalent_000002 g h
  have hVal : g.1 = h.1 := hanti hEquiv.1 hEquiv.2
  exact Subtype.ext hVal


theorem thm_equiv_reft_top_iff_reft_fixpoint_000009 : ∀ {α : Type _} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] [ACR.C5 α] [Nonempty (ACR.GödelFixpoint α)] {x : α}, x ≡ ⊠(⊤ : α) ↔ x ≡ ⊠x := by
  intro α _ _ _ _ _ _ x
  constructor
  · intro hx
    constructor
    · exact le_trans hx.1 (ACR.reft_anti_mono (ACR.le_top (x := x)))
    · have h1 : ⊠x ≤ ⊠⊠(⊤ : α) := ACR.reft_anti_mono hx.2
      exact le_trans h1 (le_trans (ACR.reft_reft_top_le_reft_top (α := α)) hx.2)
  · intro hx
    constructor
    · have hxbox : x ≤ □x := by
        calc
          x ≤ ⊠x := hx.1
          _ ≤ □⊠x := ACR.reft_le_prov_reft
          _ ≤ □x := ACR.prov_mono hx.2
      exact ACR.le_reft_top_of_le_prov_of_le_reft hxbox hx.1
    · exact le_trans (ACR.reft_anti_mono (ACR.le_top (x := x))) hx.2

end AutomatedTheoryConstruction
