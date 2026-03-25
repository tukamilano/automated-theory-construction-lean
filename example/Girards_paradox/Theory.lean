/-
# Formalization of "A Simplification of Girard's Paradox"
This file formalizes the key mathematical content from the document describing
Hurkens' simplification of Girard's paradox, which shows the inconsistency of
the Pure Type System λU⁻.
## Overview
The document presents:
- **Section 2**: Pure Type Systems (PTS) λHOL, λU⁻, and λU, their typing rules,
  and the five levels of terms.
- **Section 3**: A concrete term of type ⊥ in λU⁻, using a universe
  `U ≡ ΠX:□. ((𝒫X → X) → 𝒫X)` with maps σ and τ.
- **Section 4**: Burali-Forti's paradox and its simplifications.
- **Section 5**: *Paradoxical universes* — the abstract framework that explains
  why the proof works — and the derivation of a contradiction.
The main formalized result is **Theorem 5.3**: any paradoxical universe leads
to `False`. Since Lean 4 is a consistent type theory, no paradoxical universe
can actually be constructed in Lean; the theorem shows that the *assumption*
of a paradoxical universe is contradictory.
## References
- Hurkens, A.J.C. "A Simplification of Girard's Paradox." TLCA 1995.
- Girard, J.-Y. "Interprétation fonctionnelle et élimination des coupures
  de l'arithmétique d'ordre supérieur." Thèse de doctorat d'état, 1972.
- Coquand, T. "An Analysis of Girard's Paradox." LICS 1986.
-/
import Mathlib.Data.Set.Image
/-!
## Section 5.1: Pushforward
Each function `f : S → T` induces a function `f_* : 𝒫S → 𝒫T` defined by
`f_*(X) = {f(x) | x ∈ X}`.
In Lean/Mathlib, this is `Set.image f`.
-/
section Pushforward
/-- The pushforward `f_*` of a function `f : α → β` maps subsets of `α` to subsets of `β`.
    This is just `Set.image f`, but we give it a name matching the paper's notation. -/
def pushforward {α β : Type*} (f : α → β) : Set α → Set β := Set.image f
@[simp]
theorem pushforward_eq_image {α β : Type*} (f : α → β) (X : Set α) :
    pushforward f X = f '' X := rfl
/-- Pushforward is functorial: `(g ∘ f)_* = g_* ∘ f_*` -/
theorem pushforward_comp {α β γ : Type*} (f : α → β) (g : β → γ) :
    pushforward (g ∘ f) = pushforward g ∘ pushforward f := by
  ext X x
  simp [pushforward]
end Pushforward
/-!
## Section 5: Paradoxical Universes
### Definition
A universe `U`, together with functions `σ : U → 𝒫U` and `τ : 𝒫U → U`,
is called **paradoxical** if for each `X` in `𝒫U`,
```
  σ(τ(X)) = {τ(σ(x)) | x ∈ X}
```
Equivalently, `σ ∘ τ = (τ ∘ σ)_*`.
-/
/-- A **paradoxical universe** consists of a type `U` with functions
    `σ : U → Set U` and `τ : Set U → U` satisfying the paradoxical condition:
    `σ(τ(X)) = (τ ∘ σ) '' X` for all `X : Set U`. -/
structure ParadoxicalUniverse where
  /-- The underlying type -/
  U : Type*
  /-- The map from elements to their set of predecessors -/
  σ : U → Set U
  /-- The map from subsets back to elements -/
  τ : Set U → U
  /-- The paradoxical condition: `σ ∘ τ = (τ ∘ σ)_*` -/
  paradox : ∀ X : Set U, σ (τ X) = (fun x => τ (σ x)) '' X
namespace ParadoxicalUniverse
variable (P : ParadoxicalUniverse)
/-!
### Basic Definitions
We introduce the composite map `f = τ ∘ σ : U → U`, the predecessor relation,
and the notions of inductive sets and well-founded elements.
-/
/-- The composite map `f = τ ∘ σ : U → U`.
    This plays the role of `x ↦ τ(σ(x))` in the paper. -/
def f (x : P.U) : P.U := P.τ (P.σ x)
/-- The predecessor relation: `y` is a predecessor of `x` if `y ∈ σ(x)`. -/
def Prec (y x : P.U) : Prop := y ∈ P.σ x
/-- The predecessors of `f(x) = τ(σ(x))` are exactly `f(y)` for `y ≺ x`.
    This is the paradoxical condition applied to `X = σ(x)`. -/
theorem sigma_f (x : P.U) : P.σ (P.f x) = P.f '' (P.σ x) :=
  P.paradox (P.σ x)
/-- `f` is order-preserving: if `y ≺ x` then `f(y) ≺ f(x)`.
    This follows from `sigma_f`. -/
theorem f_monotone {x y : P.U} (h : P.Prec y x) : P.Prec (P.f y) (P.f x) := by
  rw [Prec, P.sigma_f]
  exact ⟨y, h, rfl⟩
/-- A set `X` is **inductive** if whenever all predecessors of `x` are in `X`,
    then `x` itself is in `X`. This corresponds to the principle of proof by
    transfinite induction. -/
def Inductive (X : Set P.U) : Prop :=
  ∀ x : P.U, (∀ y : P.U, P.Prec y x → y ∈ X) → x ∈ X
/-- An element `x` is **well-founded** if `x` belongs to every inductive set.
    (This is an "accessible" style definition.) -/
def IsWF (x : P.U) : Prop :=
  ∀ X : Set P.U, P.Inductive X → x ∈ X
/-- The set `WF` of all well-founded elements. -/
def WF : Set P.U := {x | P.IsWF x}
/-- `Ω = τ(WF)`, the element corresponding to the set of all well-founded elements. -/
def Omega : P.U := P.τ P.WF
/-!
### The Predecessors of Ω
By the paradoxical condition, the predecessors of `Ω` are exactly `f(w)` for
well-founded `w`.
-/
/-- The predecessors of `Ω` are `{f(w) | w ∈ WF}`. -/
theorem sigma_Omega : P.σ P.Omega = P.f '' P.WF :=
  P.paradox P.WF
/-!
### Ω is well-founded
The key insight: given an inductive set `X`, the set `{y | f(y) ∈ X}` is also
inductive (using the fact that predecessors of `f(x)` are `f(y)` for `y ≺ x`).
Since each predecessor of `Ω` is `f(w)` for some well-founded `w`, and well-founded
elements belong to every inductive set, we get `f(w) ∈ X`, hence all predecessors
of `Ω` are in `X`, hence `Ω ∈ X`.
-/
/-- If `X` is inductive, then `{y | f(y) ∈ X}` is inductive.
    This is because predecessors of `f(x)` are `f(y)` for `y ≺ x`. -/
theorem inductive_preimage_f {X : Set P.U} (hX : P.Inductive X) :
    P.Inductive {y | P.f y ∈ X} := by
  intro x hx
  have hX_f : ∀ z ∈ P.σ (P.f x), z ∈ X := by
    rw [sigma_f] at *
    aesop
  exact hX _ hX_f
/-- **Theorem**: `Ω` is well-founded.
    Each predecessor of `Ω` is `f(w)` for some well-founded `w`.
    For any inductive `X`, `{y | f(y) ∈ X}` is inductive, so `w` belongs to it,
    giving `f(w) ∈ X`. -/
theorem Omega_isWF : P.IsWF P.Omega := by
  intro X hX
  have h_predecessors : ∀ z ∈ P.σ P.Omega, z ∈ X := by
    have h_sigma_Omega : P.σ P.Omega = P.f '' P.WF := sigma_Omega P
    rw [h_sigma_Omega] at *
    simp +zetaDelta at *
    exact fun x hx => hx _ (inductive_preimage_f P hX)
  exact hX _ h_predecessors
/-!
### f(Ω) is a predecessor of Ω
Since `Ω` is well-founded, `Ω ∈ WF`, so `f(Ω) ∈ f '' WF = σ(Ω)`.
-/
/-- `f(Ω)` is a predecessor of `Ω`. -/
theorem f_Omega_prec : P.Prec (P.f P.Omega) P.Omega := by
  have h : P.f P.Omega ∈ P.σ P.Omega := by
    rw [sigma_Omega]
    exact Set.mem_image_of_mem _ (Omega_isWF _)
  exact h
/-!
### The set `{y | ¬(f(y) ≺ y)}` is inductive
If for each predecessor `y` of `x`, `f(y) ⊀ y`, then `f(x) ⊀ x`.
Proof by contradiction: Suppose `f(x) ≺ x`. Then `f(x)` is a predecessor of `x`,
so by hypothesis, `f(f(x)) ⊀ f(x)`. But `f` is monotone and `f(x) ≺ x`
implies `f(f(x)) ≺ f(x)`. Contradiction.
-/
/-- The set `{y | ¬(f(y) ≺ y)}` is inductive. -/
theorem D_inductive : P.Inductive {y | ¬ P.Prec (P.f y) y} := by
  intro x hx
  by_contra h_contra
  have hpx : P.Prec (P.f x) x := by aesop
  exact hx _ hpx (P.f_monotone hpx)
/-!
### f(Ω) is NOT a predecessor of Ω
Since `Ω` is well-founded and `{y | f(y) ⊀ y}` is inductive, `Ω` belongs to
this set, i.e., `f(Ω) ⊀ Ω`.
-/
/-- `f(Ω)` is NOT a predecessor of `Ω`. -/
theorem not_f_Omega_prec : ¬ P.Prec (P.f P.Omega) P.Omega :=
  (Omega_isWF P) _ (D_inductive P)
/-!
### The Contradiction
We have both `f(Ω) ≺ Ω` and `f(Ω) ⊀ Ω`. This is a contradiction.
-/
/-- **Theorem 5.3**: A paradoxical universe leads to a contradiction. -/
theorem contradiction (P : ParadoxicalUniverse) : False :=
  (not_f_Omega_prec P) (f_Omega_prec P)
end ParadoxicalUniverse
/-- **Corollary**: No paradoxical universe can exist (in a consistent type theory). -/
theorem no_paradoxical_universe (P : ParadoxicalUniverse) : False :=
  P.contradiction
/-!
## Section 5.1: Paradoxical Universes Are Closed Under Pushforward
If `(U, σ, τ)` is paradoxical, then `(𝒫U, σ_*, τ_*)` is also paradoxical
(assuming extensionality).
Here `σ_* = Set.image σ : 𝒫U → 𝒫(𝒫U)` and `τ_* = Set.image τ : 𝒫(𝒫U) → 𝒫U`.
Note: Since we have already shown that any paradoxical universe leads to `False`,
this construction is vacuously valid.
-/
/-- Construct a new paradoxical universe on the power set.
    Since paradoxical universes are contradictory, this is vacuously true. -/
def ParadoxicalUniverse.powerset (P : ParadoxicalUniverse) : ParadoxicalUniverse where
  U := Set P.U
  σ := Set.image P.σ
  τ := Set.image P.τ
  paradox := False.elim P.contradiction
/-!
## Section 4: Burali-Forti's Paradox
Burali-Forti's paradox shows that the collection of all ordinals cannot form a set.
In Lean's Mathlib, this is captured by the theorem `Ordinal.not_small_ordinal`
(stated differently: the type of ordinals in universe `u` is not `Small.{u}`).
The key ingredients of the paradox, mirrored in our formalization above:
- A universe `U` (the collection of all ordinals)
- A relation `<` on `U` (the ordering of ordinals)
- An element `Ω` in `U` (the order type of all ordinals)
- The question of whether `Ω` is well-founded
## Section 3: The Concrete Construction in λU⁻
In the Pure Type System λU⁻, one can construct:
```
  U ≡ ΠX:□. ((𝒫X → X) → 𝒫X)
```
with maps `τ : 𝒫U → U` and `σ : U → 𝒫U` such that `(U, σ, τ)` is paradoxical.
This is possible because the rule `(Δ, □)` in λU⁻ allows forming the polymorphic
product `ΠX:□. T` at the level of sets (level 2).
The resulting term of type `⊥` has length 2039 when fully expanded.
Since Lean 4 is a consistent type theory (it does not include the problematic
rule `(Δ, □)` at the relevant universe level), we cannot reproduce this construction.
Instead, we have shown that the abstract framework of paradoxical universes
necessarily leads to a contradiction.
## Section 2: Pure Type Systems
The document describes Pure Type Systems (PTS) as typed λ-calculi specified by:
- A set of **sorts** (e.g., `*, □, Δ`)
- **Axioms** giving types to sorts (e.g., `* : □`, `□ : Δ`)
- **Rules** `(s₁, s₂)` controlling which products `Πx:A.B` can be formed
Key systems:
- `λHOL`: sorts `{*, □, Δ}`, axioms `{* : □, □ : Δ}`, rules `{(*, *), (□, □), (□, *)}`
- `λU⁻`: extends `λHOL` with rule `(Δ, □)` — **inconsistent** (Coquand 1994)
- `λU`: extends `λHOL` with rules `(Δ, □)` and `(Δ, *)` — **inconsistent** (Girard 1972)
We formalize PTS as a general framework below.
-/
/-- A specification of a Pure Type System, consisting of sorts, axioms, and rules. -/
structure PTSSpec where
  /-- The type of sorts -/
  Sorts : Type
  /-- The axiom relation: `ax s₁ s₂` means sort `s₁` has type `s₂` -/
  ax : Sorts → Sorts → Prop
  /-- The rule relation: `rule s₁ s₂ s₃` means that if `A : s₁` and `B : s₂`
      (possibly depending on `x : A`), then `Πx:A.B : s₃` -/
  rule : Sorts → Sorts → Sorts → Prop
/-- The sorts of λHOL / λU⁻ / λU -/
inductive HurkensSort : Type
  | star       -- * (propositions)
  | box        -- □ (types/sets)
  | triangle   -- Δ (kinds)
open HurkensSort in
/-- The PTS specification for λHOL (Higher Order Logic) -/
def lambdaHOL : PTSSpec where
  Sorts := HurkensSort
  ax := fun s₁ s₂ => (s₁ = star ∧ s₂ = box) ∨ (s₁ = box ∧ s₂ = triangle)
  rule := fun s₁ s₂ s₃ =>
    (s₁ = star ∧ s₂ = star ∧ s₃ = star) ∨   -- (*, *)
    (s₁ = box  ∧ s₂ = box  ∧ s₃ = box)  ∨   -- (□, □)
    (s₁ = box  ∧ s₂ = star ∧ s₃ = star)      -- (□, *)
open HurkensSort in
/-- The PTS specification for λU⁻: λHOL extended with the rule (Δ, □).
    This system is **inconsistent** — the main result of the document. -/
def lambdaUMinus : PTSSpec where
  Sorts := HurkensSort
  ax := fun s₁ s₂ => (s₁ = star ∧ s₂ = box) ∨ (s₁ = box ∧ s₂ = triangle)
  rule := fun s₁ s₂ s₃ =>
    (s₁ = star     ∧ s₂ = star ∧ s₃ = star) ∨   -- (*, *)
    (s₁ = box      ∧ s₂ = box  ∧ s₃ = box)  ∨   -- (□, □)
    (s₁ = box      ∧ s₂ = star ∧ s₃ = star)  ∨   -- (□, *)
    (s₁ = triangle ∧ s₂ = box  ∧ s₃ = box)       -- (Δ, □) — the problematic rule
open HurkensSort in
/-- The PTS specification for λU: λHOL extended with rules (Δ, □) and (Δ, *).
    This system is **inconsistent** (Girard 1972). -/
def lambdaU : PTSSpec where
  Sorts := HurkensSort
  ax := fun s₁ s₂ => (s₁ = star ∧ s₂ = box) ∨ (s₁ = box ∧ s₂ = triangle)
  rule := fun s₁ s₂ s₃ =>
    (s₁ = star     ∧ s₂ = star ∧ s₃ = star) ∨   -- (*, *)
    (s₁ = box      ∧ s₂ = box  ∧ s₃ = box)  ∨   -- (□, □)
    (s₁ = box      ∧ s₂ = star ∧ s₃ = star)  ∨   -- (□, *)
    (s₁ = triangle ∧ s₂ = box  ∧ s₃ = box)   ∨   -- (Δ, □)
    (s₁ = triangle ∧ s₂ = star ∧ s₃ = star)      -- (Δ, *)
/-- Terms of a Pure Type System. -/
inductive PTSTerm (S : Type) : Type
  | var : ℕ → PTSTerm S
  | sort : S → PTSTerm S
  | pi : PTSTerm S → PTSTerm S → PTSTerm S     -- Πx:A.B
  | lam : PTSTerm S → PTSTerm S → PTSTerm S    -- λx:A.B
  | app : PTSTerm S → PTSTerm S → PTSTerm S    -- (A B)
/-!
### Notation for propositions and connectives (Section 2.4)
In the PTS framework:
- `⊥ ≡ ∀p:*.p` (falsehood)
- `¬φ ≡ φ → ⊥` (negation)
- `φ → ψ ≡ Π0:φ.ψ` (implication, when 0 does not occur free in ψ)
- `∀x:S.φ ≡ Πx:S.φ` (universal quantification)
### The Five Levels of Terms in λU (Section 2.4)
| Level | Description | Examples |
|-------|------------|----------|
| 4     | Superkind  | Δ        |
| 3     | Kind       | □        |
| 2     | Sets/Universes | *, 𝒫S, (S → T), ΠX:□.T |
| 1     | Objects/Propositions | φ, X, ∀x:S.φ, ⊥ |
| 0     | Proofs     | proof terms |
Each term of level 1 is strongly normalizing.
Terms of level ≥ 2 are already in normal form (they contain no redexes).
-/
