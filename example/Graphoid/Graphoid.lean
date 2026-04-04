import Mathlib

/-!
# Graphoids and Semi-Graphoids

This file formalizes the graphoid and semi-graphoid axiom systems for conditional
independence, as introduced by Dawid (1979) and Pearl & Paz (1985).

A **semi-graphoid** is a ternary relation `Indep X Y Z` on sets (read as
"X is independent of Y given Z") satisfying:
- **Trivial independence**: `Indep X ∅ Z`
- **Symmetry**: `Indep X Y Z → Indep Y X Z`
- **Decomposition**: `Indep X (Y ∪ W) Z → Indep X Y Z`
- **Weak union**: `Indep X (Y ∪ W) Z → Indep X Y (Z ∪ W)`
- **Contraction**: `Indep X Y Z → Indep X W (Y ∪ Z) → Indep X (Y ∪ W) Z`

A **graphoid** is a semi-graphoid that additionally satisfies:
- **Intersection**: `Indep X Y (Z ∪ W) → Indep X W (Z ∪ Y) → Indep X (Y ∪ W) Z`

## Main definitions

- `SemiGraphoid α`: The structure of a semi-graphoid over sets of elements of type `α`.
- `Graphoid α`: The structure of a graphoid over sets of elements of type `α`.

## Main results

- `SemiGraphoid.weak_union_right`: Weak union on the right component.
- `SemiGraphoid.decomposition_left` / `decomposition_right`: Decomposition on each component.
- `SemiGraphoid.indep_union_iff`: The contraction-decomposition equivalence.
- `Graphoid.intersection_symm`: The intersection axiom with symmetry applied.
- `SemiGraphoid.universal`: A semi-graphoid where everything is independent.
- `SemiGraphoid.discrete`: A semi-graphoid where X ⊥ Y | Z iff X = ∅ or Y = ∅.

## References

- Dawid, A.P. (1979). *Conditional independence in statistical theory*.
- Pearl, J. and Paz, A. (1985). *Graphoids: A graph-based logic for reasoning about
  relevance relations*.
- Studený, M. (2005). *Probabilistic Conditional Independence Structures*.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {α : Type*}

/-- A **semi-graphoid** is a ternary independence relation on sets satisfying the axioms of
trivial independence, symmetry, decomposition, weak union, and contraction.

These axioms capture properties common to all probabilistic conditional independence
relations. -/
structure SemiGraphoid (α : Type*) where
  /-- The ternary independence relation: `Indep X Y Z` means "X is independent of Y given Z". -/
  Indep : Set α → Set α → Set α → Prop
  /-- Trivial independence: X is always independent of the empty set given any Z. -/
  trivial_indep : ∀ (X Z : Set α), Indep X ∅ Z
  /-- Symmetry: independence is symmetric in the first two arguments. -/
  symmetry : ∀ (X Y Z : Set α), Indep X Y Z → Indep Y X Z
  /-- Decomposition: if X ⊥ (Y ∪ W) | Z, then X ⊥ Y | Z. -/
  decomposition : ∀ (X Y W Z : Set α), Indep X (Y ∪ W) Z → Indep X Y Z
  /-- Weak union: if X ⊥ (Y ∪ W) | Z, then X ⊥ Y | (Z ∪ W). -/
  weak_union : ∀ (X Y W Z : Set α), Indep X (Y ∪ W) Z → Indep X Y (Z ∪ W)
  /-- Contraction: if X ⊥ Y | Z and X ⊥ W | (Y ∪ Z), then X ⊥ (Y ∪ W) | Z. -/
  contraction : ∀ (X Y W Z : Set α), Indep X Y Z → Indep X W (Y ∪ Z) → Indep X (Y ∪ W) Z

/-- A **graphoid** is a semi-graphoid that additionally satisfies the intersection axiom.

The intersection axiom holds for strictly positive probability distributions and
characterizes a stronger notion of conditional independence. -/
structure Graphoid (α : Type*) extends SemiGraphoid α where
  /-- Intersection: if X ⊥ Y | (Z ∪ W) and X ⊥ W | (Z ∪ Y), then X ⊥ (Y ∪ W) | Z. -/
  intersection : ∀ (X Y W Z : Set α), Indep X Y (Z ∪ W) → Indep X W (Z ∪ Y) → Indep X (Y ∪ W) Z

namespace SemiGraphoid

variable (G : SemiGraphoid α)

/-- Decomposition on the left component of the union. -/
theorem decomposition_left (X Y W Z : Set α) (h : G.Indep X (Y ∪ W) Z) : G.Indep X Y Z :=
  G.decomposition X Y W Z h

/-- Decomposition on the right component of the union. -/
theorem decomposition_right (X Y W Z : Set α) (h : G.Indep X (Y ∪ W) Z) : G.Indep X W Z := by
  have : G.Indep X (W ∪ Y) Z := by rwa [Set.union_comm] at h
  exact G.decomposition X W Y Z this

/-- Combining symmetry and decomposition: if (Y ∪ W) ⊥ X | Z, then Y ⊥ X | Z. -/
theorem symmetry_decomposition (X Y W Z : Set α) (h : G.Indep (Y ∪ W) X Z) : G.Indep Y X Z := by
  have h1 := G.symmetry _ _ _ h
  have h2 := G.decomposition X Y W Z h1
  exact G.symmetry _ _ _ h2

/-- Weak union on the right component: if X ⊥ (Y ∪ W) | Z, then X ⊥ W | (Z ∪ Y). -/
theorem weak_union_right (X Y W Z : Set α) (h : G.Indep X (Y ∪ W) Z) :
    G.Indep X W (Z ∪ Y) := by
  have : G.Indep X (W ∪ Y) Z := by rwa [Set.union_comm] at h
  exact G.weak_union X W Y Z this

/-- Trivial independence is symmetric: ∅ is always independent of X given Z. -/
theorem trivial_indep_symm (X Z : Set α) : G.Indep ∅ X Z :=
  G.symmetry X ∅ Z (G.trivial_indep X Z)

/-- The contraction-decomposition equivalence (forward direction):
    X ⊥ (Y ∪ W) | Z implies both X ⊥ Y | Z and X ⊥ W | (Y ∪ Z). -/
theorem decomposition_and_weak_union (X Y W Z : Set α) (h : G.Indep X (Y ∪ W) Z) :
    G.Indep X Y Z ∧ G.Indep X W (Y ∪ Z) :=
  ⟨G.decomposition X Y W Z h, Set.union_comm Y Z ▸ G.weak_union_right X Y W Z h⟩

/-- The contraction-decomposition equivalence:
    X ⊥ (Y ∪ W) | Z ↔ (X ⊥ Y | Z ∧ X ⊥ W | (Y ∪ Z)). -/
theorem indep_union_iff (X Y W Z : Set α) :
    G.Indep X (Y ∪ W) Z ↔ (G.Indep X Y Z ∧ G.Indep X W (Y ∪ Z)) :=
  ⟨G.decomposition_and_weak_union X Y W Z, fun ⟨h1, h2⟩ => G.contraction X Y W Z h1 h2⟩

end SemiGraphoid

namespace Graphoid

variable (G : Graphoid α)

/-- In a graphoid, the intersection axiom combined with symmetry gives:
    if Y ⊥ X | (Z ∪ W) and W ⊥ X | (Z ∪ Y), then (Y ∪ W) ⊥ X | Z. -/
theorem intersection_symm (X Y W Z : Set α)
    (h1 : G.Indep Y X (Z ∪ W)) (h2 : G.Indep W X (Z ∪ Y)) :
    G.Indep (Y ∪ W) X Z := by
  have h1' := G.symmetry _ _ _ h1
  have h2' := G.symmetry _ _ _ h2
  have := G.intersection X Y W Z h1' h2'
  exact G.symmetry _ _ _ this

end Graphoid

/-- The universal semi-graphoid where everything is independent of everything. -/
def SemiGraphoid.universal (α : Type*) : SemiGraphoid α where
  Indep := fun _ _ _ => True
  trivial_indep := fun _ _ => True.intro
  symmetry := fun _ _ _ _ => True.intro
  decomposition := fun _ _ _ _ _ => True.intro
  weak_union := fun _ _ _ _ _ => True.intro
  contraction := fun _ _ _ _ _ _ => True.intro

/-- The universal graphoid where everything is independent of everything. -/
def Graphoid.universal (α : Type*) : Graphoid α where
  toSemiGraphoid := SemiGraphoid.universal α
  intersection := fun _ _ _ _ _ _ => True.intro

/-- The discrete semi-graphoid where X ⊥ Y | Z iff X = ∅ or Y = ∅. -/
def SemiGraphoid.discrete (α : Type*) : SemiGraphoid α where
  Indep := fun X Y _ => X = ∅ ∨ Y = ∅
  trivial_indep := fun _ _ => Or.inr rfl
  symmetry := fun _ _ _ h => h.symm
  decomposition := fun _ Y W _ h => by
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Set.eq_empty_of_subset_empty (h ▸ Set.subset_union_left))
  weak_union := fun _ Y W _ h => by
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Set.eq_empty_of_subset_empty (h ▸ Set.subset_union_left))
  contraction := fun _ Y W _ h1 h2 => by
    rcases h1 with rfl | rfl
    · exact Or.inl rfl
    · rcases h2 with rfl | rfl
      · exact Or.inl rfl
      · simp at *

/-- The discrete semi-graphoid extends to a discrete graphoid. -/
def Graphoid.discrete (α : Type*) : Graphoid α where
  toSemiGraphoid := SemiGraphoid.discrete α
  intersection := fun _ Y W _ h1 h2 => by
    simp only [SemiGraphoid.discrete] at h1 h2 ⊢
    rcases h1 with rfl | rfl
    · exact Or.inl rfl
    · rcases h2 with rfl | rfl
      · exact Or.inl rfl
      · simp at *
