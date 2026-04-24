/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AxiomaticThermoDynamics.LiebYngvason.Defs

/-!
# Theorem 2.1: The Cancellation Law

This file proves the cancellation law (Theorem 2.1 in Lieb–Yngvason):

> **Theorem 2.1 (Stability implies cancellation law).**
> Assume properties A1–A6, especially A6—the stability law. Then the
> cancellation law holds: if `(X, Z) ≺ (Y, Z)`, then `X ≺ Y`.

This is the first non-trivial consequence of the axioms. It says that a
"spectator" system `Z` cannot affect the set of states accessible from `X`.

## Proof outline (for single states)

The proof proceeds by an iterative argument. Starting from `(X, Z) ≺ (Y, Z)`,
we scale the hypothesis by `1/n` to get `(X/n, Z/n) ≺ (Y/n, Z/n)`.
Then we split `X` into `((1-1/n)X, X/n)` and use consistency (A3) to replace
one `1/n`-portion of `X` by `Y/n`. Repeating this `n` times converts all of `X`
to `Y`, yielding `(X, Z/n) ≺ (Y, Z/n)`. The stability axiom A6 then gives `X ≺ Y`.
-/

namespace LiebYngvason

variable {Γ : Type*} [LYAxioms Γ]

open LYAxioms

private theorem prec_append_left (t : CState Γ) {s₁ s₂ : CState Γ}
    (h : prec s₁ s₂) : prec (t ++ s₁) (t ++ s₂) := by
  simpa using consist (refl t) h

private theorem prec_append_right (t : CState Γ) {s₁ s₂ : CState Γ}
    (h : prec s₁ s₂) : prec (s₁ ++ t) (s₂ ++ t) := by
  simpa [List.append_assoc] using consist h (refl t)

private noncomputable def equalParts (n : Nat) (X : Γ) : CState Γ :=
  List.replicate (n + 1) (((1 : ℝ) / (n + 1 : ℝ)), X)

private theorem equalParts_coeff_step (n : Nat) :
    (1 - 1 / (n + 2 : ℝ)) * (1 / (n + 1 : ℝ)) = 1 / (n + 2 : ℝ) := by
  field_simp
  ring

private theorem equalParts_forward (X : Γ) :
    ∀ n : Nat, prec (single X) (equalParts n X) := by
  intro n
  induction n with
  | zero =>
      simpa [equalParts, single] using (refl (single X))
  | succ n ih =>
      let t : ℝ := 1 / (n + 2 : ℝ)
      have ht_pos : 0 < t := by
        dsimp [t]
        positivity
      have ht_lt_one : t < 1 := by
        dsimp [t]
        have hlt_nat : 1 < n + 2 := by
          omega
        have hlt : (1 : ℝ) < (n + 2 : ℝ) := by
          exact_mod_cast hlt_nat
        simpa [one_div] using inv_lt_one_of_one_lt₀ hlt
      have hsplit : prec (single X) [(t, X), (1 - t, X)] := by
        simpa [t] using split X t ht_pos ht_lt_one
      have hscaled :
          prec [(1 - t, X)] (scaleCState (1 - t) (equalParts n X)) := by
        have h :=
          scale_inv (1 - t) (sub_pos.mpr ht_lt_one) ih
        simpa [equalParts, scaleCState, single, t, equalParts_coeff_step n] using h
      have hcombine :
          prec [(t, X), (1 - t, X)] ((t, X) :: scaleCState (1 - t) (equalParts n X)) := by
        simpa using consist (refl [(t, X)]) hscaled
      have hcoeff : (1 - t) * (1 / (n + 1 : ℝ)) = t := by
        dsimp [t]
        simpa [one_div] using equalParts_coeff_step n
      have hcoeff_inv : (1 - t) * ((n + 1 : ℝ)⁻¹) = t := by
        simpa [one_div] using hcoeff
      have htarget :
          (t, X) :: scaleCState (1 - t) (equalParts n X) = equalParts (n + 1) X := by
        have hcast : (n + 2 : ℝ) = (n + 1 : ℝ) + 1 := by
          ring
        have hcoeff_succ : (1 - t) * ((n + 1 : ℝ)⁻¹) = ((n + 1 : ℝ) + 1)⁻¹ := by
          calc
            (1 - t) * ((n + 1 : ℝ)⁻¹) = (n + 2 : ℝ)⁻¹ := by simpa [t] using hcoeff_inv
            _ = ((n + 1 : ℝ) + 1)⁻¹ := by rw [hcast]
        rw [equalParts, List.replicate_succ]
        congr
        · norm_num [t, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
        · simp [scaleCState, List.replicate_succ, Nat.cast_add, Nat.cast_one,
            hcoeff_succ]
      exact LYAxioms.trans hsplit (by
        simpa [htarget] using hcombine)

private theorem equalParts_backward (X : Γ) :
    ∀ n : Nat, prec (equalParts n X) (single X) := by
  intro n
  induction n with
  | zero =>
      simpa [equalParts, single] using (refl (single X))
  | succ n ih =>
      let t : ℝ := 1 / (n + 2 : ℝ)
      have ht_pos : 0 < t := by
        dsimp [t]
        positivity
      have ht_lt_one : t < 1 := by
        dsimp [t]
        have hlt_nat : 1 < n + 2 := by
          omega
        have hlt : (1 : ℝ) < (n + 2 : ℝ) := by
          exact_mod_cast hlt_nat
        simpa [one_div] using inv_lt_one_of_one_lt₀ hlt
      have hscaled :
          prec (scaleCState (1 - t) (equalParts n X)) [(1 - t, X)] := by
        have h :=
          scale_inv (1 - t) (sub_pos.mpr ht_lt_one) ih
        simpa [equalParts, scaleCState, single, t, equalParts_coeff_step n] using h
      have hcombine :
          prec ((t, X) :: scaleCState (1 - t) (equalParts n X)) [(t, X), (1 - t, X)] := by
        simpa using consist (refl [(t, X)]) hscaled
      have hcoeff : (1 - t) * (1 / (n + 1 : ℝ)) = t := by
        dsimp [t]
        simpa [one_div] using equalParts_coeff_step n
      have hcoeff_inv : (1 - t) * ((n + 1 : ℝ)⁻¹) = t := by
        simpa [one_div] using hcoeff
      have hrecombine : prec [(t, X), (1 - t, X)] (single X) := by
        simpa [t] using recombine X t ht_pos ht_lt_one
      have hsource :
          (t, X) :: scaleCState (1 - t) (equalParts n X) = equalParts (n + 1) X := by
        have hcast : (n + 2 : ℝ) = (n + 1 : ℝ) + 1 := by
          ring
        have hcoeff_succ : (1 - t) * ((n + 1 : ℝ)⁻¹) = ((n + 1 : ℝ) + 1)⁻¹ := by
          calc
            (1 - t) * ((n + 1 : ℝ)⁻¹) = (n + 2 : ℝ)⁻¹ := by simpa [t] using hcoeff_inv
            _ = ((n + 1 : ℝ) + 1)⁻¹ := by rw [hcast]
        rw [equalParts, List.replicate_succ]
        congr
        · norm_num [t, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
        · simp [scaleCState, List.replicate_succ, Nat.cast_add, Nat.cast_one,
            hcoeff_succ]
      exact LYAxioms.trans (by
        simpa [hsource] using hcombine) hrecombine

private theorem equalParts_replace (X Y Z : Γ)
    (hXY : prec (single X ++ single Z) (single Y ++ single Z)) :
    ∀ n : Nat,
      prec (equalParts n X ++ [(((1 : ℝ) / (n + 1 : ℝ)), Z)])
        (equalParts n Y ++ [(((1 : ℝ) / (n + 1 : ℝ)), Z)]) := by
  intro n
  let a : ℝ := (1 : ℝ) / (n + 1 : ℝ)
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hscaled : prec [(a, X), (a, Z)] [(a, Y), (a, Z)] := by
    have h := scale_inv a ha_pos hXY
    simpa [a, scaleCState, single] using h
  let state : Nat → CState Γ :=
    fun k => List.replicate k (a, Y) ++ List.replicate (n + 1 - k) (a, X) ++ [(a, Z)]
  have hstep : ∀ k, k ≤ n →
      prec (state k) (state (k + 1)) := by
    intro k hk
    set pref := (List.replicate k (a, Y) ++ List.replicate (n - k) (a, X) : CState Γ)
      with hpref_eq
    have hstatek :
        state k = pref ++ [(a, X), (a, Z)] := by
      dsimp [state]
      have hrep :
          List.replicate (n + 1 - k) (a, X) = List.replicate (n - k) (a, X) ++ [(a, X)] := by
        rw [Nat.succ_sub hk, List.replicate_succ']
      simp [hpref_eq, hrep, List.append_assoc]
    have hstatek1 :
        state (k + 1) = (List.replicate k (a, Y) ++ [(a, Y)] ++ List.replicate (n - k) (a, X)) ++
            [(a, Z)] := by
      dsimp [state]
      have hsub : n + 1 - (k + 1) = n - k := by
        omega
      rw [hsub, List.replicate_succ', List.append_assoc]
    have hpref_prec :
        prec (pref ++ [(a, X), (a, Z)]) (pref ++ [(a, Y), (a, Z)]) := by
      exact prec_append_left pref hscaled
    have hperm :
        (pref ++ [(a, Y), (a, Z)]).Perm
          ((List.replicate k (a, Y) ++ [(a, Y)] ++ List.replicate (n - k) (a, X)) ++ [(a, Z)]) := by
      have hmid :
          (List.replicate (n - k) (a, X) ++ [(a, Y), (a, Z)]).Perm
            ([(a, Y)] ++ List.replicate (n - k) (a, X) ++ [(a, Z)]) := by
        simpa [List.append_assoc] using
          (show ([(a, Y)] ++ List.replicate (n - k) (a, X) ++ [(a, Z)]).Perm
              (List.replicate (n - k) (a, X) ++ [(a, Y)] ++ [(a, Z)]) from perm_middle).symm
      simpa [hpref_eq, List.append_assoc] using
        (hmid.append_left (List.replicate k (a, Y)))
    rw [hstatek, hstatek1]
    exact perm_right hperm hpref_prec
  have hchain : ∀ k, k ≤ n + 1 → prec (state 0) (state k) := by
    intro k hk
    induction k with
    | zero =>
        simpa [state] using (refl (state 0))
    | succ k ih =>
        have hk' : k ≤ n := by
          omega
        exact LYAxioms.trans (ih (Nat.le_of_succ_le hk)) (hstep k hk')
  simpa [a, state, equalParts] using hchain (n + 1) le_rfl

/-- **Theorem 2.1 (Cancellation Law).**
    If `(X, Z) ≺ (Y, Z)` for single states, then `X ≺ Y`.
    This is proved from axioms A1–A6 alone (no comparison hypothesis needed). -/
theorem cancellation_law (X Y Z : Γ) :
    prec (single X ++ single Z) (single Y ++ single Z) → precS X Y := by
  intro h
  apply stability (single X) (single Y) Z Z
  intro ε hε
  obtain ⟨n, hn_pos, hn_lt⟩ := Real.exists_nat_pos_inv_lt hε
  let m : Nat := n - 1
  let δ : ℝ := (n : ℝ)⁻¹
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact inv_pos.mpr (by positivity : (0 : ℝ) < n)
  have hδ_lt_ε : δ < ε := by
    simpa [δ] using hn_lt
  have hm : m + 1 = n := by
    dsimp [m]
    exact Nat.succ_pred_eq_of_pos hn_pos
  have hsmall :
      prec (single X ++ [(δ, Z)]) (single Y ++ [(δ, Z)]) := by
    have h₁ :
        prec (single X ++ [(δ, Z)]) (equalParts m X ++ [(δ, Z)]) := by
      simpa [δ, m, hm, equalParts] using
        prec_append_right [(δ, Z)] (equalParts_forward X m)
    have h₂ :
        prec (equalParts m X ++ [(δ, Z)]) (equalParts m Y ++ [(δ, Z)]) := by
      have hmR : (m : ℝ) + 1 = n := by
        exact_mod_cast hm
      have hmInv : ((m : ℝ) + 1)⁻¹ = (n : ℝ)⁻¹ := by rw [hmR]
      simpa [δ, Nat.cast_add, Nat.cast_one, hmInv] using equalParts_replace X Y Z h m
    have h₃ :
        prec (equalParts m Y ++ [(δ, Z)]) (single Y ++ [(δ, Z)]) := by
      simpa [δ, m, hm, equalParts] using
        prec_append_right [(δ, Z)] (equalParts_backward Y m)
    exact LYAxioms.trans h₁ (LYAxioms.trans h₂ h₃)
  have hsplitZ : prec [(ε, Z)] [(δ, Z), (ε - δ, Z)] := by
    have hpos : 0 < δ / ε := by
      exact div_pos hδ_pos hε
    have hlt : δ / ε < 1 := by
      simpa using (div_lt_iff₀ hε).2 (by simpa using hδ_lt_ε)
    have hδε : ε * (δ / ε) = δ := by
      field_simp [hε.ne']
    have hrest : ε * (1 - δ / ε) = ε - δ := by
      calc
        ε * (1 - δ / ε) = ε - ε * (δ / ε) := by ring
        _ = ε - δ := by rw [hδε]
    have h :=
      scale_inv ε hε (split Z (δ / ε) hpos hlt)
    simpa [scaleCState, single, hδε, hrest] using h
  have hjoinZ : prec [(δ, Z), (ε - δ, Z)] [(ε, Z)] := by
    have hpos : 0 < δ / ε := by
      exact div_pos hδ_pos hε
    have hlt : δ / ε < 1 := by
      simpa using (div_lt_iff₀ hε).2 (by simpa using hδ_lt_ε)
    have hδε : ε * (δ / ε) = δ := by
      field_simp [hε.ne']
    have hrest : ε * (1 - δ / ε) = ε - δ := by
      calc
        ε * (1 - δ / ε) = ε - ε * (δ / ε) := by ring
        _ = ε - δ := by rw [hδε]
    have h :=
      scale_inv ε hε (recombine Z (δ / ε) hpos hlt)
    simpa [scaleCState, single, hδε, hrest] using h
  have hwith_rest :
      prec (single X ++ [(δ, Z), (ε - δ, Z)]) (single Y ++ [(δ, Z), (ε - δ, Z)]) := by
    exact prec_append_right [(ε - δ, Z)] hsmall
  have hleft :
      prec (single X ++ [(ε, Z)]) (single X ++ [(δ, Z), (ε - δ, Z)]) := by
    exact prec_append_left (single X) hsplitZ
  have hright :
      prec (single Y ++ [(δ, Z), (ε - δ, Z)]) (single Y ++ [(ε, Z)]) := by
    exact prec_append_left (single Y) hjoinZ
  exact LYAxioms.trans hleft (LYAxioms.trans hwith_rest hright)

/-- Special case of the cancellation law for single states.
    If `(X, Z) ≺ (Y, Z)`, then `X ≺ Y`. -/
theorem cancellation_law_single (X Y Z : Γ) :
    prec (single X ++ single Z) (single Y ++ single Z) → precS X Y := by
  exact cancellation_law X Y Z

/-- The cancellation law implies: if `X ≺≺ Y` (strict), then
    `(X, Z) ≺≺ (Y, Z)` for all `Z`. This is the converse direction.
    (Requires comparability of `Y` and `Z`.) -/
theorem strict_prec_compound (X Y Z : Γ)
    (h : sprecS X Y) (_hcmp : comparable (single Y) (single Z)) :
    sprec (single X ++ single Z) (single Y ++ single Z) := by
  rcases h with ⟨hXY, hYX⟩
  constructor
  · simpa [precS] using consist hXY (refl (single Z))
  · intro hrev
    exact hYX (cancellation_law Y X Z hrev)

end LiebYngvason
