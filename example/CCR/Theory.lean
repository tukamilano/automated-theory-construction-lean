module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.CStarAlgebra.Classes
/-!
# CCR Formalization
This file formalizes a minimal axiom system around creation/annihilation operators
(canonical commutation relations, CCR) in quantum mechanics.
## Structure
1. **Bosonic Core**: Abstract CCR + vacuum axioms
2. **Derived Operators**: Number operator and Fock states
3. **Target Theorems**: Commutation relations, ladder relations
4. **Polynomial Model**: Concrete sanity model proving consistency
## Key Insight
The Fock structure is **not axiomatic** here. It is reconstructed from CCR and
the vacuum alone. Everything else (number operator, ladder structure) follows.
-/
noncomputable section
open Polynomial LinearMap
/-! ## Section 1: Bosonic Core (CCR + vacuum)
We model operators as endomorphisms `Module.End ℂ V` of a complex vector space `V`.
The ring structure on `Module.End ℂ V` gives multiplication = composition,
and `1 = LinearMap.id`.
-/
/-- A bosonic system consists of an annihilation operator `a` and a creation operator
`aDagger` acting on a complex vector space `V`, satisfying:
- **CCR**: `[a, a†] = 1`, i.e., `a * a† - a† * a = 1`
- **Vacuum axiom**: `a |0⟩ = 0` -/
structure BosonCore (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The annihilation operator -/
  a : Module.End ℂ V
  /-- The creation operator (adjoint of `a`) -/
  aDagger : Module.End ℂ V
  /-- The vacuum vector |0⟩ -/
  vacuum : V
  /-- CCR: `a * a† - a† * a = 1` -/
  ccr : a * aDagger - aDagger * a = 1
  /-- Vacuum axiom: `a |0⟩ = 0` -/
  vacuum_annihilate : a vacuum = 0
namespace BosonCore
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (bc : BosonCore V)
/-! ## Section 2: Derived Definitions -/
/-- The number operator `N = a† * a` (composition: a† ∘ a). -/
def number : Module.End ℂ V := bc.aDagger * bc.a
/-- The n-th Fock state `|n⟩ = (a†)^n |0⟩`. -/
def ket (n : ℕ) : V := (bc.aDagger ^ n) bc.vacuum
/-! ## Section 3: Basic CCR consequences -/
/-- The CCR applied pointwise: `a (a† v) - a† (a v) = v`. -/
theorem ccr_apply (v : V) : bc.a (bc.aDagger v) - bc.aDagger (bc.a v) = v := by
  simpa using congr_arg (fun f => f v) bc.ccr
/-- The CCR in the other form: `a * a† = a† * a + 1`. -/
theorem ccr' : bc.a * bc.aDagger = bc.aDagger * bc.a + 1 :=
  eq_add_of_sub_eq' bc.ccr
/-! ## Section 4: Commutation relations with the number operator -/
/-- `[N, a] = -a`, i.e., `N * a - a * N = -a`. -/
theorem comm_number_a : bc.number * bc.a - bc.a * bc.number = -bc.a := by
  refine LinearMap.ext ?_
  intro v
  unfold BosonCore.number
  simp
  have := bc.ccr_apply (bc.a v)
  simp_all +decide [sub_eq_iff_eq_add]
/-- `[N, a†] = a†`, i.e., `N * a† - a† * N = a†`. -/
theorem comm_number_aDagger :
    bc.number * bc.aDagger - bc.aDagger * bc.number = bc.aDagger := by
  convert congr_arg (fun x => bc.aDagger * x) bc.ccr using 1
  rw [mul_sub]; ac_rfl
/-! ## Section 5: Vacuum and number operator -/
/-- The vacuum is an eigenvector of the number operator with eigenvalue 0. -/
theorem number_vacuum : bc.number bc.vacuum = 0 := by
  show bc.aDagger (bc.a bc.vacuum) = 0
  rw [bc.vacuum_annihilate, map_zero]
/-- `|0⟩ = vacuum`. -/
theorem ket_zero : bc.ket 0 = bc.vacuum := by
  simp [BosonCore.ket]
/-! ## Section 6: Ladder relations -/
/-- Creation operator on ket: `a† |n⟩ = |n+1⟩`. -/
theorem aDagger_ket (n : ℕ) : bc.aDagger (bc.ket n) = bc.ket (n + 1) := by
  unfold BosonCore.ket
  simp +decide [pow_succ']
/-- Key commutation lemma (inductive):
`a * (a†)^(n+1) = (a†)^(n+1) * a + (↑(n+1)) • (a†)^n`
Proved by induction from the CCR. -/
theorem a_mul_aDagger_pow_succ (n : ℕ) :
    bc.a * bc.aDagger ^ (n + 1) =
      bc.aDagger ^ (n + 1) * bc.a + (↑(n + 1) : ℂ) • bc.aDagger ^ n := by
  induction n with
  | zero => simpa using bc.ccr'
  | succ n ih =>
    have h_step : bc.a * bc.aDagger ^ (n + 2) =
        (bc.aDagger * bc.a + 1) * bc.aDagger ^ (n + 1) := by
      rw [← ccr' bc, pow_succ, mul_assoc]
      rw [← pow_succ', ← pow_succ]
    simp_all +decide [mul_assoc, pow_succ', add_mul, mul_add, add_smul]
    abel1
/-- Ladder down: `a |n+1⟩ = (↑(n+1)) • |n⟩`.
The annihilation operator lowers the Fock state by one level,
producing a scalar factor of `n+1`. -/
theorem a_ket_succ (n : ℕ) :
    bc.a (bc.ket (n + 1)) = (↑(n + 1) : ℂ) • bc.ket n := by
  convert congr_arg (fun x => x bc.vacuum) (a_mul_aDagger_pow_succ bc n) using 1
  simp +decide [bc.vacuum_annihilate, BosonCore.ket]
/-! ## Section 7: Polynomial Sanity Model
We construct a concrete instance of `BosonCore` using polynomials:
- Space: `ℂ[X]`
- `a` = differentiation
- `a†` = multiplication by `X`
- `vacuum` = `1` (constant polynomial)
The CCR `[d/dx, x·] = 1` follows from the Leibniz rule.
-/
/-- Multiplication by `X` as a `ℂ`-linear endomorphism of `ℂ[X]`. -/
def polyMulX : Module.End ℂ (Polynomial ℂ) :=
  LinearMap.mulLeft ℂ Polynomial.X
/-- Differentiation as a `ℂ`-linear endomorphism of `ℂ[X]`. -/
def polyDeriv : Module.End ℂ (Polynomial ℂ) :=
  Polynomial.derivative
/-- The CCR for the polynomial model: `d/dx ∘ (X·) - (X·) ∘ d/dx = id`.
This follows from the Leibniz rule: `d/dx(X · p) = p + X · d/dx(p)`. -/
theorem poly_ccr : polyDeriv * polyMulX - polyMulX * polyDeriv = 1 := by
  ext p
  simp [polyDeriv, polyMulX]
  cases p <;> simp +decide [Polynomial.coeff_monomial]
  simp +decide [← Polynomial.C_mul_X_pow_eq_monomial]; ring
  norm_num [← pow_succ', Polynomial.coeff_X]; ring
  grind +ring
/-- Differentiation annihilates constants. -/
theorem poly_vacuum : polyDeriv (1 : Polynomial ℂ) = 0 :=
  Polynomial.derivative_one
/-- The polynomial model gives a concrete instance of `BosonCore`,
proving the axiom system is consistent. -/
def polyBosonCore : BosonCore (Polynomial ℂ) where
  a := polyDeriv
  aDagger := polyMulX
  vacuum := 1
  ccr := poly_ccr
  vacuum_annihilate := poly_vacuum
end BosonCore
