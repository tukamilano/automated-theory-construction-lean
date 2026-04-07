import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_fixedpoint_implies_nn_reft_true_000001 : ∀ (box reft : Prop → Prop), (∀ P Q : Prop, (P → Q) → box P → box Q) → (∀ P Q : Prop, (P → Q) → reft Q → reft P) → reft False → (∀ P Q : Prop, (P → box Q) → (P → reft Q) → (P → reft True)) → (∀ P : Prop, reft P → box (reft P)) → (∃ P : Prop, P ↔ reft P) → ¬¬ reft True := by
  intro box reft hbox hcontra hRF hbridge hboxreft hex
  cases hex with
  | intro P hP =>
    have hPmp : P → reft P := fun p => hP.mp p
    have hPmpr : reft P → P := fun rp => hP.mpr rp
    have hPb : P → box P := by
      intro p
      have rp : reft P := hPmp p
      have bRP : box (reft P) := hboxreft P rp
      exact hbox (reft P) P hPmpr bRP
    have hPT : P → reft True := hbridge P P hPb hPmp
    have nnP : ¬¬ P := by
      intro nP
      have rp : reft P := (hcontra P False nP) hRF
      exact nP (hPmpr rp)
    intro nRT
    have nP : ¬ P := fun p => nRT (hPT p)
    exact nnP nP

end AutomatedTheoryConstruction
