import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_accepts_reachable_least_fixpoint_000147 : ∀ p : AtomicResidualState, ∀ R : Finset AtomicResidualState,
  (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) →
    let A : Set AtomicResidualState := {q : AtomicResidualState | q ∈ R ∧ AtomicResidualGraphAccepts q}
    let F : Set AtomicResidualState → Set AtomicResidualState := fun S =>
      (({([# (p.2)], p.2)} : Set AtomicResidualState) ∩ (↑R : Set AtomicResidualState)) ∪
        {q : AtomicResidualState | q ∈ R ∧ ∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ S}
    A = F A ∧
      ∀ S : Set AtomicResidualState, S ⊆ (↑R : Set AtomicResidualState) → F S = S → A ⊆ S := by
  intro p R hR
  dsimp
  have hsame :
      ∀ {q : AtomicResidualState},
        Relation.ReflTransGen AtomicResidualGraphStep p q → q.2 = p.2 := by
    intro q hq
    induction hq with
    | refl =>
        rfl
    | tail hreach hstep ih =>
        cases hstep <;> simpa using ih
  have hreachLeast := thm_accepts_least_reachable_subset_000143 p R hR
  dsimp at hreachLeast
  rcases hreachLeast with ⟨_, hA_base, hA_step, hleast⟩
  constructor
  · ext q
    constructor
    · intro hqA
      rcases hqA with ⟨hqR, hqacc⟩
      rcases (thm_residual_accepts_base_or_step_000097 q).mp hqacc with hbase | ⟨r, hstep, hracc⟩
      · left
        constructor
        · show q ∈ ({([# (p.2)], p.2)} : Set AtomicResidualState)
          have hs : q.2 = p.2 := hsame ((hR q).mp hqR)
          simpa [hs] using hbase
        · exact hqR
      · right
        have hreachq : Relation.ReflTransGen AtomicResidualGraphStep p q := (hR q).mp hqR
        have hrR : r ∈ R := (hR r).mpr (Relation.ReflTransGen.tail hreachq hstep)
        exact ⟨hqR, r, hstep, ⟨hrR, hracc⟩⟩
    · intro hqF
      rcases hqF with hqbase | ⟨hqR, r, hstep, hrA⟩
      · rcases hqbase with ⟨hqmem, hqR⟩
        have hqeq : q = ([# (p.2)], p.2) := by
          simpa using hqmem
        have hpR : ([# (p.2)], p.2) ∈ R := by
          simpa [hqeq] using hqR
        simpa [hqeq] using hA_base hpR
      · exact hA_step q hqR ⟨r, hstep, hrA⟩
  · intro S hSR hFS
    have hSbase : (([# (p.2)], p.2) ∈ R) → ([# (p.2)], p.2) ∈ S := by
      intro hpR
      have hpFS :
          ([# (p.2)], p.2) ∈
            (({([# (p.2)], p.2)} : Set AtomicResidualState) ∩ (↑R : Set AtomicResidualState)) ∪
              {q : AtomicResidualState | q ∈ R ∧ ∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ S} := by
        left
        constructor
        · simp
        · exact hpR
      rw [← hFS]
      exact hpFS
    have hSstep :
        ∀ q : AtomicResidualState,
          q ∈ R →
            (∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ S) →
              q ∈ S := by
      intro q hqR hsucc
      have hqFS :
          q ∈
            (({([# (p.2)], p.2)} : Set AtomicResidualState) ∩ (↑R : Set AtomicResidualState)) ∪
              {q : AtomicResidualState | q ∈ R ∧ ∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ S} := by
        right
        exact ⟨hqR, hsucc⟩
      rw [← hFS]
      exact hqFS
    exact hleast S hSR hSbase hSstep

end AutomatedTheoryConstruction
