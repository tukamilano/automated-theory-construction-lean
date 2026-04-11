import Mathlib
import AutomatedTheoryConstruction.Theory

import AutomatedTheoryConstruction.Generated.Manifest

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


inductive Subformula : Tp → Tp → Prop where
  | refl (A : Tp) : Subformula A A
  | ldiv_left {A B C : Tp} : Subformula A B → Subformula A (B ⧹ C)
  | ldiv_right {A B C : Tp} : Subformula A C → Subformula A (B ⧹ C)
  | rdiv_left {A B C : Tp} : Subformula A B → Subformula A (B ⧸ C)
  | rdiv_right {A B C : Tp} : Subformula A C → Subformula A (B ⧸ C)

/-- Residual atomic states only use source subformulas and source atoms. -/
theorem thm_residual_state_subformula_occurs_000061 : ∀ {Γ Δ : List Tp} {A : Tp} {s : String},
  residualAtomicState Γ A = some (Δ, s) →
    (∀ B ∈ Δ, ∃ C ∈ Γ ++ [A], Subformula B C) ∧
    (∃ C ∈ Γ ++ [A], occurs_atom s C) := by
  intro Γ Δ A s hres
  induction A generalizing Γ Δ s with
  | atom t =>
      simp [residualAtomicState] at hres
      rcases hres with ⟨rfl, rfl⟩
      constructor
      · intro B hB
        exact ⟨B, by simp [hB], Subformula.refl B⟩
      · exact ⟨# t, by simp, by simp [occurs_atom]⟩
  | ldiv B C ihB ihC =>
      cases Γ with
      | nil =>
          simp [residualAtomicState] at hres
      | cons A Γ =>
          have hih := ihC (Γ := B :: A :: Γ) (Δ := Δ) (s := s) hres
          rcases hih with ⟨hsub, hocc⟩
          constructor
          · intro X hX
            rcases hsub X hX with ⟨Y, hYmem, hXY⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYeq | hYmem | hYeq
            · subst Y
              exact ⟨B ⧹ C, by simp, Subformula.ldiv_left hXY⟩
            · subst Y
              exact ⟨A, by simp, hXY⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hXY⟩
            · subst Y
              exact ⟨B ⧹ C, by simp, Subformula.ldiv_right hXY⟩
          · rcases hocc with ⟨Y, hYmem, hYs⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYeq | hYmem | hYeq
            · subst Y
              exact ⟨B ⧹ C, by simp, by simp [occurs_atom, hYs]⟩
            · subst Y
              exact ⟨A, by simp, hYs⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hYs⟩
            · subst Y
              exact ⟨B ⧹ C, by simp, by simp [occurs_atom, hYs]⟩
  | rdiv C B ihC ihB =>
      cases Γ with
      | nil =>
          simp [residualAtomicState] at hres
      | cons A Γ =>
          have hih := ihC (Γ := (A :: Γ) ++ [B]) (Δ := Δ) (s := s) hres
          rcases hih with ⟨hsub, hocc⟩
          constructor
          · intro X hX
            rcases hsub X hX with ⟨Y, hYmem, hXY⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYmem | hYeq | hYeq
            · subst Y
              exact ⟨A, by simp, hXY⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hXY⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, Subformula.rdiv_right hXY⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, Subformula.rdiv_left hXY⟩
          · rcases hocc with ⟨Y, hYmem, hYs⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYmem | hYeq | hYeq
            · subst Y
              exact ⟨A, by simp, hYs⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hYs⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, by simp [occurs_atom, hYs]⟩
            · subst Y
              exact ⟨C ⧸ B, by simp, by simp [occurs_atom, hYs]⟩


lemma subformula_trans {A B C : Tp} : Subformula A B → Subformula B C → Subformula A C := by
  intro hAB hBC
  induction hBC with
  | refl => exact hAB
  | ldiv_left h ih => exact Subformula.ldiv_left ih
  | ldiv_right h ih => exact Subformula.ldiv_right ih
  | rdiv_left h ih => exact Subformula.rdiv_left ih
  | rdiv_right h ih => exact Subformula.rdiv_right ih

/-- Reachable residual states keep the same atom and stay within source subformulas. -/
theorem thm_residual_reachable_subformula_invariant_000065 : ∀ (Γ Δ : List Tp) (A : Tp) (s : String) (q : AtomicResidualState),
  residualAtomicState Γ A = some (Δ, s) →
  Relation.ReflTransGen AtomicResidualGraphStep (Δ, s) q →
  q.2 = s ∧ ∀ B ∈ q.1, ∃ C ∈ Γ ++ [A], Subformula B C := by
  intro Γ Δ A s q hres hreach
  have hstart : ∀ B ∈ Δ, ∃ C ∈ Γ ++ [A], Subformula B C :=
    (thm_residual_state_subformula_occurs_000061 (Γ := Γ) (Δ := Δ) (A := A) (s := s) hres).1
  induction hreach with
  | refl =>
      constructor
      · rfl
      · simpa using hstart
  | tail hreach hstep ih =>
      rcases ih with ⟨hs, hsub⟩
      cases hstep with
      | rdiv Γ0 L Δ0 Λ A0 B0 s0 hc harg =>
          constructor
          · exact hs
          · intro X hX
            have hctx : Γ0 = L ++ [B0 ⧸ A0] ++ Δ0 ++ Λ :=
              cand_rdiv_context_eq (Γ := Γ0) (L := L) (Δ := Δ0) (Λ := Λ) (A := A0) (B := B0) hc
            have hcases : X ∈ L ∨ X = B0 ∨ X ∈ Λ := by
              simpa [List.mem_append, List.mem_singleton] using hX
            rcases hcases with hX | rfl | hX
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem
            · have hmem : Tp.rdiv X A0 ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append]
              rcases hsub (Tp.rdiv X A0) hmem with ⟨C, hC, hSC⟩
              exact ⟨C, hC, subformula_trans (Subformula.rdiv_left (Subformula.refl X)) hSC⟩
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem
      | ldiv Γ0 Γ1 Δ0 R A0 B0 s0 hc harg =>
          constructor
          · exact hs
          · intro X hX
            have hctx : Γ0 = Γ1 ++ Δ0 ++ [A0 ⧹ B0] ++ R := by
              symm
              simpa using (candidates_list_degree (Γ := Γ0) (c := Cand.ldiv Γ1 Δ0 A0 B0 R) hc)
            have hcases : X ∈ Γ1 ∨ X = B0 ∨ X ∈ R := by
              simpa [List.mem_append, List.mem_singleton] using hX
            rcases hcases with hX | rfl | hX
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem
            · have hmem : Tp.ldiv A0 X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append]
              rcases hsub (Tp.ldiv A0 X) hmem with ⟨C, hC, hSC⟩
              exact ⟨C, hC, subformula_trans (Subformula.ldiv_right (Subformula.refl X)) hSC⟩
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact hsub X hmem


/-- Residual graph steps preserve a source-subformula bound. -/
theorem thm_residual_step_subformula_closed_000068 : ∀ (src : List Tp) (p q : AtomicResidualState),
  (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) →
  AtomicResidualGraphStep p q →
  q.2 = p.2 ∧ ∀ B ∈ q.1, ∃ C ∈ src, Subformula B C := by
  intro src p q hsrc hstep
  cases hstep with
  | rdiv Γ L Δ Λ A B s hc harg =>
      constructor
      · rfl
      · intro X hX
        have hctx : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ :=
          cand_rdiv_context_eq (Γ := Γ) (L := L) (Δ := Δ) (Λ := Λ) (A := A) (B := B) hc
        have hcases : X ∈ L ∨ X = B ∨ X ∈ Λ := by
          simpa [List.mem_append, List.mem_singleton] using hX
        rcases hcases with hX | rfl | hX
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem
        · have hmem : Tp.rdiv X A ∈ Γ := by
            rw [hctx]
            simp [List.mem_append]
          rcases hsrc (Tp.rdiv X A) hmem with ⟨C, hC, hSC⟩
          exact ⟨C, hC, subformula_trans (Subformula.rdiv_left (Subformula.refl X)) hSC⟩
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem
  | ldiv Γ Γ₁ Δ R A B s hc harg =>
      constructor
      · rfl
      · intro X hX
        have hctx : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        have hcases : X ∈ Γ₁ ∨ X = B ∨ X ∈ R := by
          simpa [List.mem_append, List.mem_singleton] using hX
        rcases hcases with hX | rfl | hX
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem
        · have hmem : Tp.ldiv A X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append]
          rcases hsrc (Tp.ldiv A X) hmem with ⟨C, hC, hSC⟩
          exact ⟨C, hC, subformula_trans (Subformula.ldiv_right (Subformula.refl X)) hSC⟩
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact hsrc X hmem


lemma subformula_set_finite (C : Tp) : Set.Finite {B : Tp | Subformula B C} := by
  induction C with
  | atom s =>
      refine (Set.finite_singleton (Tp.atom s)).subset ?_
      intro B hB
      cases hB
      simp
  | ldiv A B ihA ihB =>
      refine ((ihA.union ihB).union (Set.finite_singleton (Tp.ldiv A B))).subset ?_
      intro X hX
      cases hX with
      | refl =>
          simp
      | ldiv_left h =>
          simp [h]
      | ldiv_right h =>
          simp [h]
  | rdiv A B ihA ihB =>
      refine ((ihA.union ihB).union (Set.finite_singleton (Tp.rdiv A B))).subset ?_
      intro X hX
      cases hX with
      | refl =>
          simp
      | rdiv_left h =>
          simp [h]
      | rdiv_right h =>
          simp [h]

lemma subformula_support_finite (src : List Tp) :
    Set.Finite {B : Tp | ∃ C ∈ src, Subformula B C} := by
  induction src with
  | nil =>
      simpa using (Set.finite_empty : Set.Finite (∅ : Set Tp))
  | cons C src ih =>
      rw [show ({B : Tp | ∃ D ∈ C :: src, Subformula B D} : Set Tp) =
          {B : Tp | Subformula B C} ∪ {B : Tp | ∃ D ∈ src, Subformula B D} by
        ext B
        simp]
      exact (subformula_set_finite C).union ih

lemma finite_lists_bounded_of_finite {α : Type*} {S : Set α} (hS : S.Finite) :
    ∀ N : Nat,
      Set.Finite {l : List α | l.length ≤ N ∧ ∀ a ∈ l, a ∈ S} := by
  intro N
  induction N with
  | zero =>
      refine (Set.finite_singleton ([] : List α)).subset ?_
      intro l hl
      cases l with
      | nil =>
          simp
      | cons a tl =>
          simp at hl
  | succ N ih =>
      let T : Set (List α) := {l | l.length ≤ N ∧ ∀ a ∈ l, a ∈ S}
      have hT : T.Finite := ih
      refine ((Set.finite_singleton ([] : List α)).union
        (Set.Finite.image (fun p : α × List α => p.1 :: p.2) (hS.prod hT))).subset ?_
      intro l hl
      cases l with
      | nil =>
          simp
      | cons a tl =>
          right
          refine ⟨(a, tl), ?_, rfl⟩
          constructor
          · exact hl.2 a (by simp)
          · change tl.length ≤ N ∧ ∀ b ∈ tl, b ∈ S
            constructor
            · simpa using hl.1
            · intro b hb
              exact hl.2 b (by simp [hb])

lemma list_length_le_list_degree : ∀ Γ : List Tp, Γ.length ≤ list_degree Γ
  | [] => by
      simp [list_degree]
  | A :: Γ => by
      have hA : 1 ≤ tp_degree A := by
        cases A <;> simp [tp_degree]
      have hΓ : Γ.length ≤ list_degree Γ := list_length_le_list_degree Γ
      calc
        (A :: Γ).length = Γ.length + 1 := by simp
        _ = 1 + Γ.length := by omega
        _ ≤ tp_degree A + list_degree Γ := Nat.add_le_add hA hΓ
        _ = list_degree (A :: Γ) := by simp [list_degree]

lemma atomicResidualGraphStep_degree_lt {p q : AtomicResidualState}
    (h : AtomicResidualGraphStep p q) :
    list_degree q.1 < list_degree p.1 := by
  cases h with
  | rdiv Γ L Δ Λ A B s hc harg =>
      have hΓ : Γ = L ++ [Tp.rdiv B A] ++ Δ ++ Λ := by
        symm
        simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
      rw [hΓ]
      simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
      omega
  | ldiv Γ Γ₁ Δ R A B s hc harg =>
      have hΓ : Γ = Γ₁ ++ Δ ++ [Tp.ldiv A B] ++ R := by
        symm
        simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
      rw [hΓ]
      simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
      omega

lemma residual_reachable_degree_le {p q : AtomicResidualState}
    (h : Relation.ReflTransGen AtomicResidualGraphStep p q) :
    list_degree q.1 ≤ list_degree p.1 := by
  induction h with
  | refl =>
      exact le_rfl
  | tail hreach hstep ih =>
      exact le_trans (atomicResidualGraphStep_degree_lt hstep).le ih

/-- Reachable residual states form a finite set. -/
theorem thm_residual_reachable_finite_000071 : ∀ (Γ Δ : List Tp) (A : Tp) (s : String), residualAtomicState Γ A = some (Δ, s) → Set.Finite { q : AtomicResidualState | Relation.ReflTransGen AtomicResidualGraphStep (Δ, s) q } := by
  intro Γ Δ A s hres
  have hsubsrc : Set.Finite {B : Tp | ∃ C ∈ Γ ++ [A], Subformula B C} :=
    subformula_support_finite (Γ ++ [A])
  have hctxfin :
      Set.Finite {ctx : List Tp |
        ctx.length ≤ list_degree Δ ∧
        ∀ B ∈ ctx, ∃ C ∈ Γ ++ [A], Subformula B C} :=
    finite_lists_bounded_of_finite
      (S := {B : Tp | ∃ C ∈ Γ ++ [A], Subformula B C})
      hsubsrc (list_degree Δ)
  refine (Set.Finite.image (fun ctx : List Tp => (ctx, s)) hctxfin).subset ?_
  intro q hq
  rcases thm_residual_reachable_subformula_invariant_000065 Γ Δ A s q hres hq with
    ⟨hs, hsub⟩
  have hdeg : list_degree q.1 ≤ list_degree Δ :=
    residual_reachable_degree_le hq
  refine ⟨q.1, ?_, ?_⟩
  · exact ⟨le_trans (list_length_le_list_degree q.1) hdeg, hsub⟩
  · cases q
    simpa using hs.symm


/-- Same-atom states supported by source subformulas are finite. -/
theorem thm_same_atom_subformula_states_finite_000075_is_false : ¬(∀ (src : List Tp) (s : String), Set.Finite { p : AtomicResidualState | p.2 = s ∧ ∀ B ∈ p.1, ∃ C ∈ src, Subformula B C }) := by
  intro h
  let S : Set AtomicResidualState :=
    { p : AtomicResidualState | p.2 = "a" ∧ ∀ B ∈ p.1, ∃ C ∈ [# "a"], Subformula B C }
  have hSfin : S.Finite := by
    simpa [S] using h [# "a"] "a"
  let f : ℕ → S := fun n =>
    ⟨(List.replicate n (# "a"), "a"), by
      constructor
      · rfl
      · intro B hB
        refine ⟨# "a", by simp, ?_⟩
        have hEq : B = # "a" := List.eq_of_mem_replicate hB
        simpa [hEq] using (Subformula.refl (# "a"))⟩
  letI : Fintype S := hSfin.fintype
  have hf : Function.Injective f := by
    intro m n hmn
    simpa [f] using congr_arg (fun x : S => x.1.1.length) hmn
  haveI : Finite ℕ := Finite.of_injective f hf
  exact not_finite ℕ


/-- Residual steps preserve source subformulas and strictly decrease degree. -/
theorem thm_residual_step_degree_subformula_000070 : ∀ (src : List Tp) (p q : AtomicResidualState), (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) → AtomicResidualGraphStep p q → q.2 = p.2 ∧ list_degree q.1 < list_degree p.1 ∧ (∀ B ∈ q.1, ∃ C ∈ src, Subformula B C) := by
  intro src p q hsrc hstep
  rcases thm_residual_step_subformula_closed_000068 src p q hsrc hstep with ⟨hs, hsub⟩
  exact ⟨hs, atomicResidualGraphStep_degree_lt hstep, hsub⟩


/-- A degree-bounded same-atom subformula state need not be reachable. -/
theorem thm_degree_bounded_slice_strict_000080 : ∃ (Γ : List Tp) (A : Tp) (Δ : List Tp) (s : String) (p : AtomicResidualState),
  residualAtomicState Γ A = some (Δ, s) ∧
  p.2 = s ∧
  list_degree p.1 ≤ list_degree Δ ∧
  (∀ B ∈ p.1, ∃ C ∈ Γ ++ [A], Subformula B C) ∧
  ¬ Relation.ReflTransGen AtomicResidualGraphStep (Δ, s) p := by
  refine ⟨[# "a"], # "a" ⧹ # "a", [# "a", # "a"], "a", ([# "a"], "a"), ?_⟩
  constructor
  · simp [residualAtomicState]
  constructor
  · rfl
  constructor
  · simp [list_degree, tp_degree]
  constructor
  · intro B hB
    simp at hB
    subst hB
    refine ⟨# "a", ?_, Subformula.refl (# "a")⟩
    simp
  · intro hreach
    suffices hstay : ∀ q, Relation.ReflTransGen AtomicResidualGraphStep ([# "a", # "a"], "a") q → q = ([# "a", # "a"], "a")
    · have hp : ([# "a"], "a") = ([# "a", # "a"], "a") := hstay ([# "a"], "a") hreach
      simp at hp
    · intro q h
      induction h with
      | refl => rfl
      | tail hreach hstep ih =>
          subst ih
          exfalso
          cases hstep with
          | rdiv Γ L Δ Λ A B s hc harg =>
              simp [candidates, picks] at hc
          | ldiv Γ Γ₁ Δ R A B s hc harg =>
              simp [candidates, picks] at hc


/-- Degree-bounded same-atom subformula residual states form a finite set. -/
theorem thm_degree_bounded_subformula_slice_finite_000072 : ∀ (src : List Tp) (s : String) (N : Nat),
  Set.Finite { q : AtomicResidualState |
    q.2 = s ∧
    list_degree q.1 ≤ N ∧
    (∀ B ∈ q.1, ∃ C ∈ src, Subformula B C) } := by
  intro src s N
  have hsubsrc : Set.Finite {B : Tp | ∃ C ∈ src, Subformula B C} :=
    subformula_support_finite src
  have hctxfin :
      Set.Finite {ctx : List Tp |
        ctx.length ≤ N ∧
        ∀ B ∈ ctx, ∃ C ∈ src, Subformula B C} :=
    finite_lists_bounded_of_finite
      (S := {B : Tp | ∃ C ∈ src, Subformula B C})
      hsubsrc N
  refine (Set.Finite.image (fun ctx : List Tp => (ctx, s)) hctxfin).subset ?_
  intro q hq
  refine ⟨q.1, ?_, ?_⟩
  · exact ⟨le_trans (list_length_le_list_degree q.1) hq.2.1, hq.2.2⟩
  · cases q
    simpa using hq.1.symm


/-- A same-atom subformula subset is finite iff its degrees are uniformly bounded. -/
theorem thm_same_atom_finite_iff_bounded_000084 : ∀ (src : List Tp) (s : String) (S : Set AtomicResidualState), S ⊆ { p : AtomicResidualState | p.2 = s ∧ (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) } → (S.Finite ↔ ∃ N : Nat, ∀ p ∈ S, list_degree p.1 ≤ N) := by
  intro src s S hSub
  constructor
  · intro hfin
    have hfinImg :
        Set.Finite ((fun p : AtomicResidualState => list_degree p.1) '' S) :=
      Set.Finite.image (fun p : AtomicResidualState => list_degree p.1) hfin
    rcases (Set.finite_iff_bddAbove.mp hfinImg) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro p hp
    exact hN ⟨p, hp, rfl⟩
  · rintro ⟨N, hN⟩
    refine (thm_degree_bounded_subformula_slice_finite_000072 src s N).subset ?_
    intro p hp
    have hp' := hSub hp
    exact ⟨hp'.1, hN p hp, hp'.2⟩


/-- Residual graph steps are well-founded. -/
theorem thm_atomic_residual_step_wellfounded_000078 : WellFounded (fun q p : AtomicResidualState => AtomicResidualGraphStep p q) := by
  refine Subrelation.wf ?_ (measure (fun p : AtomicResidualState => list_degree p.1)).wf
  intro q p hstep
  simpa using atomicResidualGraphStep_degree_lt hstep

end AutomatedTheoryConstruction
