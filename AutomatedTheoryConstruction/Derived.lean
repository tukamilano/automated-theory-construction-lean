import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


/-- Each Fock ket is an eigenvector of the number operator with eigenvalue n. -/
theorem thm_number_ket_eigenvalue_000002 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number (bc.ket n) = (↑n : ℂ) • bc.ket n := by
  intro V _ _ bc n
  cases n with
  | zero =>
      simpa [BosonCore.ket] using bc.number_vacuum
  | succ n =>
      calc
        bc.number (bc.ket (n + 1)) = bc.aDagger (bc.a (bc.ket (n + 1))) := by rfl
        _ = bc.aDagger ((↑(n + 1) : ℂ) • bc.ket n) := by rw [bc.a_ket_succ]
        _ = (↑(n + 1) : ℂ) • bc.aDagger (bc.ket n) := by rw [map_smul]
        _ = (↑(n + 1) : ℂ) • bc.ket (n + 1) := by rw [bc.aDagger_ket]


/-- If the next Fock state vanishes, then the previous one also vanishes. -/
theorem thm_ket_zero_descends_000003 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.ket (n + 1) = 0 → bc.ket n = 0 := by
  intro V _ _ bc n h
  have hs : 0 = ((↑(n + 1) : ℂ) • bc.ket n) := by
    calc
      0 = bc.a (bc.ket (n + 1)) := by
        simpa [h]
      _ = ((↑(n + 1) : ℂ) • bc.ket n) := bc.a_ket_succ n
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    have hnat : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
    exact_mod_cast hnat
  exact (smul_eq_zero.mp hs.symm).resolve_left hne


/-- In the polynomial model, the nth ket is X raised to n. -/
theorem thm_poly_bosoncore_ket_eq_x_pow_000004 : ∀ n : ℕ, BosonCore.polyBosonCore.ket n = Polynomial.X ^ n := by
  intro n
  simp [BosonCore.ket, BosonCore.polyBosonCore, BosonCore.polyMulX]


/-- The commutator of the number operator with the nth creation power is n times that power. -/
theorem thm_comm_number_adagger_pow_000001 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number * bc.aDagger ^ n - bc.aDagger ^ n * bc.number = (↑n : ℂ) • bc.aDagger ^ n := by
  intro V _ _ bc n
  cases n with
  | zero =>
      simp [BosonCore.number]
  | succ n =>
      rw [sub_eq_iff_eq_add]
      unfold BosonCore.number
      calc
        bc.aDagger * bc.a * bc.aDagger ^ (n + 1)
            = bc.aDagger * (bc.a * bc.aDagger ^ (n + 1)) := by
                rw [mul_assoc]
        _ = bc.aDagger * (bc.aDagger ^ (n + 1) * bc.a + (↑(n + 1) : ℂ) • bc.aDagger ^ n) := by
                rw [bc.a_mul_aDagger_pow_succ n]
        _ = bc.aDagger * (bc.aDagger ^ (n + 1) * bc.a) +
              bc.aDagger * ((↑(n + 1) : ℂ) • bc.aDagger ^ n) := by
                rw [mul_add]
        _ = (bc.aDagger * bc.aDagger ^ (n + 1)) * bc.a +
              bc.aDagger * ((↑(n + 1) : ℂ) • bc.aDagger ^ n) := by
                rw [← mul_assoc]
        _ = (bc.aDagger * bc.aDagger ^ (n + 1)) * bc.a +
              (↑(n + 1) : ℂ) • (bc.aDagger * bc.aDagger ^ n) := by
                rw [mul_smul_comm]
        _ = bc.aDagger ^ (n + 2) * bc.a + (↑(n + 1) : ℂ) • bc.aDagger ^ (n + 1) := by
                rw [← pow_succ', ← pow_succ']
        _ = (bc.aDagger ^ (n + 1) * bc.aDagger) * bc.a +
              (↑(n + 1) : ℂ) • bc.aDagger ^ (n + 1) := by
                rw [pow_succ]
        _ = bc.aDagger ^ (n + 1) * (bc.aDagger * bc.a) +
              (↑(n + 1) : ℂ) • bc.aDagger ^ (n + 1) := by
                rw [mul_assoc]
        _ = (↑(n + 1) : ℂ) • bc.aDagger ^ (n + 1) +
              bc.aDagger ^ (n + 1) * (bc.aDagger * bc.a) := by
                rw [add_comm]


/-- The annihilation operator lowers the n-th ket with scalar factor n. -/
theorem thm_annihilation_on_ket_000005 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.a (bc.ket n) = (↑n : ℂ) • bc.ket (n - 1) := by
  intro V _ _ bc n
  cases n with
  | zero =>
      simp [BosonCore.ket, bc.vacuum_annihilate]
  | succ k =>
      simpa [Nat.succ_sub_one] using bc.a_ket_succ k


/-- A Fock state vanishes exactly when the vacuum vanishes. -/
theorem thm_ket_zero_iff_vacuum_zero_000008 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.ket n = 0 ↔ bc.vacuum = 0 := by
  intro V _ _ bc n
  constructor
  · intro hk
    induction n with
    | zero =>
        simpa [BosonCore.ket] using hk
    | succ n ih =>
        apply ih
        have hs : 0 = ((↑(n + 1) : ℂ) • bc.ket n) := by
          calc
            0 = bc.a (bc.ket (n + 1)) := by
              simpa [hk]
            _ = ((↑(n + 1) : ℂ) • bc.ket n) := bc.a_ket_succ n
        have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        exact (smul_eq_zero.mp hs.symm).resolve_left hne
  · intro hvac
    rw [BosonCore.ket, hvac]
    simp


/-- A nonzero vacuum generates a genuine Fock tower: different occupation numbers give different ket states. -/
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


/-- Applying m creation operators raises the ket number eigenvalue by m. -/
theorem thm_number_adagger_pow_ket_eigenvalue_000006 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (m n : ℕ), bc.number ((bc.aDagger ^ m) (bc.ket n)) = (↑(m + n) : ℂ) • (bc.aDagger ^ m) (bc.ket n) := by
  intro V _ _ bc m n
  have hEq : (bc.aDagger ^ m) (bc.ket n) = bc.ket (m + n) := by
    simp [BosonCore.ket, pow_add]
  have hEig : ∀ k : ℕ, bc.number (bc.ket k) = (↑k : ℂ) • bc.ket k := by
    intro k
    cases k with
    | zero =>
        simpa [BosonCore.ket] using bc.number_vacuum
    | succ k =>
        calc
          bc.number (bc.ket (k + 1)) = bc.aDagger (bc.a (bc.ket (k + 1))) := by rfl
          _ = bc.aDagger ((↑(k + 1) : ℂ) • bc.ket k) := by rw [bc.a_ket_succ]
          _ = (↑(k + 1) : ℂ) • bc.aDagger (bc.ket k) := by rw [map_smul]
          _ = (↑(k + 1) : ℂ) • bc.ket (k + 1) := by rw [bc.aDagger_ket]
  simpa [hEq] using hEig (m + n)


/-- Distinct indices give distinct Fock states when the vacuum is nonzero. -/
theorem thm_ket_injective_of_vacuum_ne_zero_000009_is_false : ¬(∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (m n : ℕ), m ≠ n → bc.ket m ≠ bc.ket n) := by
  intro h
  let V0 := ULift ↥(⊥ : Submodule ℂ ℂ)
  let bc : BosonCore V0 :=
    { a := 0
      aDagger := 0
      vacuum := 0
      ccr := Subsingleton.elim _ _
      vacuum_annihilate := by simp }
  have hneq : (0 : ℕ) ≠ 1 := by decide
  have hcontra := h (bc := bc) (m := 0) (n := 1) hneq
  apply hcontra
  exact Subsingleton.elim _ _

end AutomatedTheoryConstruction
