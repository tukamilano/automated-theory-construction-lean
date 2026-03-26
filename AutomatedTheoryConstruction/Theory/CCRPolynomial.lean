import AutomatedTheoryConstruction.Theory.Core
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative

/-!
# CCR Polynomial Model

A concrete polynomial realization of `BosonCore`.
-/

noncomputable section

open Polynomial LinearMap

namespace BosonCore

/-- Multiplication by `X` as a `ℂ`-linear endomorphism of `ℂ[X]`. -/
def polyMulX : Module.End ℂ (Polynomial ℂ) :=
  LinearMap.mulLeft ℂ Polynomial.X

/-- Differentiation as a `ℂ`-linear endomorphism of `ℂ[X]`. -/
def polyDeriv : Module.End ℂ (Polynomial ℂ) :=
  Polynomial.derivative

/-- The CCR for the polynomial model: `d/dx ∘ (X·) - (X·) ∘ d/dx = id`. -/
theorem poly_ccr : polyDeriv * polyMulX - polyMulX * polyDeriv = 1 := by
  ext p
  simp [polyDeriv, polyMulX]
  cases p <;> simp +decide [Polynomial.coeff_monomial]
  simp +decide [← Polynomial.C_mul_X_pow_eq_monomial]
  ring
  norm_num [← pow_succ', Polynomial.coeff_X]
  ring
  grind +ring

/-- Differentiation annihilates constants. -/
theorem poly_vacuum : polyDeriv (1 : Polynomial ℂ) = 0 :=
  Polynomial.derivative_one

/-- A concrete `BosonCore` instance on `ℂ[X]`. -/
def polyBosonCore : BosonCore (Polynomial ℂ) where
  a := polyDeriv
  aDagger := polyMulX
  vacuum := 1
  ccr := poly_ccr
  vacuum_annihilate := poly_vacuum

end BosonCore
