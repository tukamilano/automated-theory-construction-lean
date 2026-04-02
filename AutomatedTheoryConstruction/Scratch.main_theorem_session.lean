import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem main_thm_ket_injective_of_vacuum_ne_zero : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), bc.vacuum ≠ 0 → Function.Injective bc.ket := by
  intro V _ _ bc hvac
  have hket_ne : ∀ n : ℕ, bc.ket n ≠ 0 := by
    intro n
    induction n with
    | zero =>
        simpa [BosonCore.ket] using hvac
    | succ n ih =>
        intro hk
        have hs : ((↑(n + 1) : ℂ) • bc.ket n) = 0 := by
          calc
            ((↑(n + 1) : ℂ) • bc.ket n) = bc.a (bc.ket (n + 1)) := by rw [bc.a_ket_succ]
            _ = 0 := by simpa [hk]
        have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        exact ih ((smul_eq_zero.mp hs).resolve_left hne)
  have hnum : ∀ n : ℕ, bc.number (bc.ket n) = (↑n : ℂ) • bc.ket n := by
    intro n
    cases n with
    | zero =>
        simpa [BosonCore.ket] using bc.number_vacuum
    | succ n =>
        calc
          bc.number (bc.ket (n + 1)) = bc.aDagger (bc.a (bc.ket (n + 1))) := by rfl
          _ = bc.aDagger ((↑(n + 1) : ℂ) • bc.ket n) := by rw [bc.a_ket_succ]
          _ = (↑(n + 1) : ℂ) • bc.aDagger (bc.ket n) := by rw [map_smul]
          _ = (↑(n + 1) : ℂ) • bc.ket (n + 1) := by rw [bc.aDagger_ket]
  intro n m hEq
  have hn : bc.number (bc.ket m) = (↑n : ℂ) • bc.ket m := by
    simpa [hEq] using hnum n
  have hm : bc.number (bc.ket m) = (↑m : ℂ) • bc.ket m := hnum m
  have hsub : (((↑n : ℂ) - (↑m : ℂ)) • bc.ket m) = 0 := by
    calc
      (((↑n : ℂ) - (↑m : ℂ)) • bc.ket m) = (↑n : ℂ) • bc.ket m - (↑m : ℂ) • bc.ket m := by rw [sub_smul]
      _ = bc.number (bc.ket m) - bc.number (bc.ket m) := by rw [← hn, ← hm]
      _ = 0 := by simp
  have hcast : ((↑n : ℂ) - (↑m : ℂ)) = 0 :=
    (smul_eq_zero.mp hsub).resolve_right (hket_ne m)
  exact Nat.cast_injective (R := ℂ) (sub_eq_zero.mp hcast)

end AutomatedTheoryConstruction
