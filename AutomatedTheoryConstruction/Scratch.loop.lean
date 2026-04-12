import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

def atomic_residual_saturation (p : AtomicResidualState) (R : Finset AtomicResidualState) : Nat → Set AtomicResidualState
  | 0 => {q | q = ([# (p.2)], p.2) ∧ q ∈ R}
  | n + 1 =>
      atomic_residual_saturation p R n ∪
        {q | q ∈ R ∧ ∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ atomic_residual_saturation p R n}

def atomic_residual_path_to_base (p q : AtomicResidualState) : Nat → Prop
  | 0 => q = ([# (p.2)], p.2)
  | n + 1 =>
      ∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ atomic_residual_path_to_base p r n

theorem thm_saturation_iff_bounded_path_000146 : ∀ p : AtomicResidualState,
  ∀ R : Finset AtomicResidualState,
    (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) →
      ∀ n : Nat,
        ∀ q : AtomicResidualState,
          q ∈ R →
            (q ∈ atomic_residual_saturation p R n ↔
              ∃ m : Nat, m ≤ n ∧ atomic_residual_path_to_base p q m) := by
  intro p R hR
  have hstep_mem :
      ∀ {q r : AtomicResidualState},
        q ∈ R → AtomicResidualGraphStep q r → r ∈ R := by
    intro q r hqR hstep
    exact (hR r).2 (Relation.ReflTransGen.tail ((hR q).1 hqR) hstep)
  intro n
  induction n with
  | zero =>
      intro q hqR
      constructor
      · intro hqSat
        have hqbase : q = ([# (p.2)], p.2) := by
          simpa [atomic_residual_saturation, hqR] using hqSat
        exact ⟨0, le_rfl, by simpa [atomic_residual_path_to_base] using hqbase⟩
      · rintro ⟨m, hmle, hmPath⟩
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmle
        subst hm0
        simpa [atomic_residual_saturation, atomic_residual_path_to_base, hqR] using hmPath
  | succ n ih =>
      intro q hqR
      constructor
      · intro hqSat
        change q ∈ atomic_residual_saturation p R n ∨
          q ∈ R ∧ ∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ atomic_residual_saturation p R n at hqSat
        rcases hqSat with hOld | hNew
        · rcases (ih q hqR).1 hOld with ⟨m, hmle, hmPath⟩
          exact ⟨m, Nat.le_succ_of_le hmle, hmPath⟩
        · rcases hNew with ⟨_, ⟨r, hstep, hrSat⟩⟩
          have hrR : r ∈ R := hstep_mem hqR hstep
          rcases (ih r hrR).1 hrSat with ⟨m, hmle, hmPath⟩
          refine ⟨m + 1, Nat.succ_le_succ hmle, ?_⟩
          exact ⟨r, hstep, hmPath⟩
      · rintro ⟨m, hmle, hmPath⟩
        change q ∈ atomic_residual_saturation p R n ∨
          q ∈ R ∧ ∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ atomic_residual_saturation p R n
        cases m with
        | zero =>
            have hqSatN : q ∈ atomic_residual_saturation p R n :=
              (ih q hqR).2 ⟨0, Nat.zero_le n, hmPath⟩
            exact Or.inl hqSatN
        | succ m =>
            rcases hmPath with ⟨r, hstep, hrPath⟩
            have hrR : r ∈ R := hstep_mem hqR hstep
            have hrSat : r ∈ atomic_residual_saturation p R n :=
              (ih r hrR).2 ⟨m, Nat.le_of_succ_le_succ hmle, hrPath⟩
            exact Or.inr ⟨hqR, ⟨r, hstep, hrSat⟩⟩

end AutomatedTheoryConstruction
