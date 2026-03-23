module

-- public import Mathlib
public import Mathlib.Logic.Nonempty
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Contrapose

@[expose] public section

class ACR (α : Type*) extends Top α, Bot α, LE α, Preorder α where

namespace ACR

variable {α : Type*} [ACR α] (x : α)

abbrev Provable (x : α) := ⊤ ≤ x
prefix:50 "⊢ " => Provable

abbrev Refutable (x : α) := x ≤ ⊥
prefix:50 "⊬ " => Refutable

@[grind]
def Equivalent (x y : α) := (x ≤ y) ∧ (y ≤ x)
infix:50 " ≡ " => Equivalent

instance [ACR α] : Trans (LE.le (α := α)) (· ≡ ·) (· ≤ ·) where
  trans hab hbc := by grind;

def Inconsistent (α) [ACR α] := (⊤ : α) ≤ ⊥
abbrev Consistent (α) [ACR α] := ¬Inconsistent α

class Prov (α : Type*) [ACR α] where
  prov : α → α
prefix:75 "□" => Prov.prov

class Reft (α : Type*) [ACR α] where
  reft : α → α
prefix:75 "⊠" => Reft.reft

class APS (α : Type*) [ACR α] [Prov α] [Reft α] where
  prov_mono : ∀ {x y : α}, x ≤ y → □x ≤ □y
  reft_anti_mono : ∀ {x y : α}, x ≤ y → ⊠y ≤ ⊠x
  top_le_reft_bot : (⊤ : α) ≤ ⊠⊥
  le_reft_top_of_le_prov_of_le_reft : ∀ {x y : α}, x ≤ □y → x ≤ ⊠y → x ≤ ⊠⊤
  reft_le_prov_reft : ∀ {x : α}, ⊠x ≤ □⊠x
export APS (prov_mono reft_anti_mono top_le_reft_bot le_reft_top_of_le_prov_of_le_reft reft_le_prov_reft)

attribute [grind <=] prov_mono reft_anti_mono
attribute [grind <=] le_reft_top_of_le_prov_of_le_reft
attribute [grind .] top_le_reft_bot reft_le_prov_reft

abbrev GödelFixpoint (α) [ACR α] [Reft α] := { g : α // g ≡ ⊠g }
abbrev HenkinFixpoint (α) [ACR α] [Prov α] := { h : α // h ≡ □h }

variable [Prov α] [Reft α] [APS α] {g : GödelFixpoint α}

@[grind .]
lemma reft_gf_le_box_gf : ⊠g.1 ≤ □g.1 := by trans (□⊠g.1) <;> grind;

@[grind .]
lemma gf_le_reft_top : g.1 ≤ ⊠⊤ := by
  calc
    g.1 ≤ ⊠g.1 := g.2.1
    _   ≤ ⊠⊤   := le_reft_top_of_le_prov_of_le_reft reft_gf_le_box_gf le_rfl;

/-- Theorem 1 (2) -/
@[grind →]
lemma reft_reft_top_le_reft_top [hg : Nonempty (GödelFixpoint α)] : ⊠⊠(⊤ : α) ≤ ⊠⊤ := by
  obtain ⟨g, hg⟩ := hg;
  have : ⊠g ≤ □⊠g := by grind;
  have : □⊠g ≤ □g := by grind;
  calc
    ⊠⊠⊤ ≤ ⊠g := by
      apply reft_anti_mono;
      apply le_reft_top_of_le_prov_of_le_reft;
      . show g ≤ □g;
        grind;
      . exact hg.1;
    ⊠g  ≤ ⊠⊤ := by
      apply le_reft_top_of_le_prov_of_le_reft;
      . show ⊠g ≤ □g;
        grind;
      . show ⊠g ≤ ⊠g;
        apply reft_anti_mono;
        rfl;

/-- Theorem 1 (1) -/
@[grind →]
lemma irrefutable_reft_top (h : Consistent α) [hg : Nonempty (GödelFixpoint α)] : ¬⊬ ⊠(⊤ : α) := by
  contrapose! h;
  let g := hg.some;
  have h₁ : g.1 ≤ (⊥ : α) := le_trans gf_le_reft_top h;
  have h₂ : ⊠(⊥ : α) ≤ ⊠g.1 := reft_anti_mono h₁;
  have h₃ : ⊠(⊥ : α) ≤ g.1 := le_trans h₂ g.2.2;
  calc
    ⊤ ≤ ⊠⊥  := top_le_reft_bot
    _ ≤ g.1 := h₃
    _ ≤ ⊥   := h₁

class C5 (α : Type*) [ACR α] [Prov α] [Reft α] [APS α] where
  le_top : ∀ {x : α}, x ≤ ⊤
export C5 (le_top)
attribute [grind .] le_top

/-- Theorem 2 -/
lemma gf_equiv_reft_top [C5 α] {g : GödelFixpoint α} : g.1 ≡ ⊠⊤ := by
  constructor;
  . grind;
  . have : g.1 ≤ ⊤ := le_top;
    have := reft_anti_mono this;
    apply le_trans;
    . show ⊠⊤ ≤ ⊠g.1;
      apply reft_anti_mono;
      exact le_top;
    . grind;

end ACR

end
