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
        exact ⟨B, by exact List.mem_append_left [#t] hB, Subformula.refl B⟩
      · exact ⟨# t, by exact List.mem_concat_self, by simp [occurs_atom]⟩
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
              exact ⟨B ⧹ C, by exact List.mem_concat_self, Subformula.ldiv_left hXY⟩
            · subst Y
              exact ⟨A, by simp, hXY⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hXY⟩
            · subst Y
              exact ⟨B ⧹ C, by exact List.mem_concat_self, Subformula.ldiv_right hXY⟩
          · rcases hocc with ⟨Y, hYmem, hYs⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYeq | hYmem | hYeq
            · subst Y
              exact ⟨B ⧹ C, by exact List.mem_concat_self, by simp [occurs_atom, hYs]⟩
            · subst Y
              exact ⟨A, by simp, hYs⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hYs⟩
            · subst Y
              exact ⟨B ⧹ C, by exact List.mem_concat_self, by simp [occurs_atom, hYs]⟩
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
              exact ⟨C ⧸ B, by exact List.mem_concat_self, Subformula.rdiv_right hXY⟩
            · subst Y
              exact ⟨C ⧸ B, by exact List.mem_concat_self, Subformula.rdiv_left hXY⟩
          · rcases hocc with ⟨Y, hYmem, hYs⟩
            simp [List.mem_append] at hYmem
            rcases hYmem with hYeq | hYmem | hYeq | hYeq
            · subst Y
              exact ⟨A, by simp, hYs⟩
            · exact ⟨Y, by simp [List.mem_append, hYmem], hYs⟩
            · subst Y
              exact ⟨C ⧸ B, by exact List.mem_concat_self, by simp [occurs_atom, hYs]⟩
            · subst Y
              exact ⟨C ⧸ B, by exact List.mem_concat_self, by simp [occurs_atom, hYs]⟩


lemma subformula_trans {A B C : Tp} : Subformula A B → Subformula B C → Subformula A C := by
  intro hAB hBC
  induction hBC with
  | refl => exact ((fun a => hAB) ∘ fun a => A) A
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
      exact And.symm ⟨hstart, rfl⟩
  | tail hreach hstep ih =>
      rcases ih with ⟨hs, hsub⟩
      cases hstep with
      | rdiv Γ0 L Δ0 Λ A0 B0 s0 hc harg =>
          constructor
          · exact (String.append_left_inj s).mp (congrFun (congrArg HAppend.hAppend hs) s)
          · intro X hX
            have hctx : Γ0 = L ++ [B0 ⧸ A0] ++ Δ0 ++ Λ :=
              cand_rdiv_context_eq (Γ := Γ0) (L := L) (Δ := Δ0) (Λ := Λ) (A := A0) (B := B0) hc
            have hcases : X ∈ L ∨ X = B0 ∨ X ∈ Λ := by
              simpa [List.mem_append, List.mem_singleton] using hX
            rcases hcases with hX | rfl | hX
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append, hX]
              exact Exists.imp (fun a a_1 => a_1) (hsub X hmem)
            · have hmem : Tp.rdiv X A0 ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append]
              rcases hsub (Tp.rdiv X A0) hmem with ⟨C, hC, hSC⟩
              exact ⟨C, hC, subformula_trans (Subformula.rdiv_left (Subformula.refl X)) hSC⟩
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                exact List.mem_append_right (L ++ [B0 / A0] ++ Δ0) hX
              exact Exists.imp (fun a a_1 => a_1) (hsub X hmem)
      | ldiv Γ0 Γ1 Δ0 R A0 B0 s0 hc harg =>
          constructor
          · exact (String.append_left_inj s).mp (congrFun (congrArg HAppend.hAppend hs) s)
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
              exact Exists.imp (fun a a_1 => a_1) (hsub X hmem)
            · have hmem : Tp.ldiv A0 X ∈ Γ0 := by
                rw [hctx]
                simp [List.mem_append]
              rcases hsub (Tp.ldiv A0 X) hmem with ⟨C, hC, hSC⟩
              exact ⟨C, hC, subformula_trans (Subformula.ldiv_right (Subformula.refl X)) hSC⟩
            · have hmem : X ∈ Γ0 := by
                rw [hctx]
                exact List.mem_append_right (Γ1 ++ Δ0 ++ [A0 \ B0]) hX
              exact Exists.imp (fun a a_1 => a_1) (hsub X hmem)


/-- Residual graph steps preserve a source-subformula bound. -/
theorem thm_residual_step_subformula_closed_000068 : ∀ (src : List Tp) (p q : AtomicResidualState),
  (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) →
  AtomicResidualGraphStep p q →
  q.2 = p.2 ∧ ∀ B ∈ q.1, ∃ C ∈ src, Subformula B C := by
  intro src p q hsrc hstep
  cases hstep with
  | rdiv Γ L Δ Λ A B s hc harg =>
      constructor
      · exact (String.append_left_inj s).mp rfl
      · intro X hX
        have hctx : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ :=
          cand_rdiv_context_eq (Γ := Γ) (L := L) (Δ := Δ) (Λ := Λ) (A := A) (B := B) hc
        have hcases : X ∈ L ∨ X = B ∨ X ∈ Λ := by
          simpa [List.mem_append, List.mem_singleton] using hX
        rcases hcases with hX | rfl | hX
        · have hmem : X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append, hX]
          exact Exists.imp (fun a a_1 => a_1) (hsrc X hmem)
        · have hmem : Tp.rdiv X A ∈ Γ := by
            rw [hctx]
            simp [List.mem_append]
          rcases hsrc (Tp.rdiv X A) hmem with ⟨C, hC, hSC⟩
          exact ⟨C, hC, subformula_trans (Subformula.rdiv_left (Subformula.refl X)) hSC⟩
        · have hmem : X ∈ Γ := by
            rw [hctx]
            exact List.mem_append_right (L ++ [B / A] ++ Δ) hX
          exact Exists.imp (fun a a_1 => a_1) (hsrc X hmem)
  | ldiv Γ Γ₁ Δ R A B s hc harg =>
      constructor
      · exact (String.append_left_inj s).mp rfl
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
          exact Exists.imp (fun a a_1 => a_1) (hsrc X hmem)
        · have hmem : Tp.ldiv A X ∈ Γ := by
            rw [hctx]
            simp [List.mem_append]
          rcases hsrc (Tp.ldiv A X) hmem with ⟨C, hC, hSC⟩
          exact ⟨C, hC, subformula_trans (Subformula.ldiv_right (Subformula.refl X)) hSC⟩
        · have hmem : X ∈ Γ := by
            rw [hctx]
            exact List.mem_append_right (Γ₁ ++ Δ ++ [A \ B]) hX
          exact Exists.imp (fun a a_1 => a_1) (hsrc X hmem)


lemma subformula_set_finite (C : Tp) : Set.Finite {B : Tp | Subformula B C} := by
  induction C with
  | atom s =>
      refine (Set.finite_singleton (Tp.atom s)).subset ?_
      intro B hB
      cases hB
      exact Set.mem_singleton (#s)
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
          exact Set.mem_singleton []
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
          · exact hl.2 a (by exact List.mem_cons_self)
          · change tl.length ≤ N ∧ ∀ b ∈ tl, b ∈ S
            constructor
            · simpa using hl.1
            · intro b hb
              exact hl.2 b (by exact List.mem_cons_of_mem a hb)

lemma list_length_le_list_degree : ∀ Γ : List Tp, Γ.length ≤ list_degree Γ
  | [] => by
      simp [list_degree]
  | A :: Γ => by
      have hA : 1 ≤ tp_degree A := by
        cases A <;> simp [tp_degree]
      have hΓ : Γ.length ≤ list_degree Γ := list_length_le_list_degree Γ
      calc
        (A :: Γ).length = Γ.length + 1 := by exact List.length_cons
        _ = 1 + Γ.length := by exact Nat.add_comm Γ.length 1
        _ ≤ tp_degree A + list_degree Γ := Nat.add_le_add hA hΓ
        _ = list_degree (A :: Γ) := by simp [list_degree]

lemma atomicResidualGraphStep_degree_lt {p q : AtomicResidualState}
    (h : AtomicResidualGraphStep p q) :
    list_degree q.1 < list_degree p.1 := by
  cases h with
  | rdiv Γ L Δ Λ A B s hc harg =>
      have hΓ : Γ = L ++ [Tp.rdiv B A] ++ Δ ++ Λ := by
        exact cand_rdiv_context_eq hc
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
      exact Nat.le_refl (list_degree p.1)
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
    exact Prod.mk_right_inj.mpr (id (Eq.symm hs))


/-- Same-atom states supported by source subformulas are finite. -/
theorem thm_same_atom_subformula_states_finite_000075_is_false : ¬(∀ (src : List Tp) (s : String), Set.Finite { p : AtomicResidualState | p.2 = s ∧ ∀ B ∈ p.1, ∃ C ∈ src, Subformula B C }) := by
  intro h
  let S : Set AtomicResidualState :=
    { p : AtomicResidualState | p.2 = "a" ∧ ∀ B ∈ p.1, ∃ C ∈ [# "a"], Subformula B C }
  have hSfin : S.Finite := by
    exact (Set.finite_iff_finite_of_encard_eq_encard rfl).mp (h [#"a"] "a")
  let f : ℕ → S := fun n =>
    ⟨(List.replicate n (# "a"), "a"), by
      constructor
      · exact String.toByteArray_inj.mp rfl
      · intro B hB
        refine ⟨# "a", by exact List.mem_singleton.mpr rfl, ?_⟩
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
  · exact String.toByteArray_inj.mp rfl
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
      | refl => exact Prod.mk_right_inj.mpr rfl
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


/-- Residual rejection iff the state is nonbase and all successors reject. -/
theorem thm_residual_rejects_local_iff_000094 : ∀ p : AtomicResidualState, ¬ AtomicResidualGraphAccepts p ↔ (p ≠ ([# (p.2)], p.2) ∧ ∀ q : AtomicResidualState, AtomicResidualGraphStep p q → ¬ AtomicResidualGraphAccepts q) := by
  rintro ⟨Γ, s⟩
  change ¬ AtomicResidualGraphAccepts (Γ, s) ↔
    ((Γ, s) ≠ ([# s], s) ∧ ∀ q : AtomicResidualState, AtomicResidualGraphStep (Γ, s) q → ¬ AtomicResidualGraphAccepts q)
  constructor
  · intro hp
    constructor
    · intro hbase
      apply hp
      cases hbase
      exact AtomicResidualGraphAccepts.base s
    · intro q hstep hq
      apply hp
      exact AtomicResidualGraphAccepts.step hstep hq
  · rintro ⟨hbase, hsucc⟩ hacc
    cases hacc with
    | base t =>
        exact false_of_ne hbase
    | step hstep hacc =>
        (expose_names; exact (iff_false_intro (hsucc q hstep)).mp hacc)


/-- Bounded residual-slice acceptance has a finite recursive characterization. -/
theorem thm_bounded_slice_acceptance_recursion_000085 : ∀ (src : List Tp) (s : String) (N : Nat),
  ∃ S : Finset AtomicResidualState,
    (∀ p : AtomicResidualState,
      p ∈ S ↔
        p.2 = s ∧
        list_degree p.1 ≤ N ∧
        (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C)) ∧
    ∃ good : AtomicResidualState → Prop,
      (∀ p : AtomicResidualState, p ∈ S →
        (AtomicResidualGraphAccepts p ↔ good p)) ∧
      ∀ p : AtomicResidualState, p ∈ S →
        (good p ↔
          p = ([# s], s) ∨
            ∃ q : AtomicResidualState,
              q ∈ S ∧
              list_degree q.1 < list_degree p.1 ∧
              AtomicResidualGraphStep p q ∧
              good q) := by
  intro src s N
  classical
  let T : Set AtomicResidualState :=
    { p : AtomicResidualState |
        p.2 = s ∧
        list_degree p.1 ≤ N ∧
        (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) }
  have hfin : T.Finite := by
    exact thm_degree_bounded_subformula_slice_finite_000072 src s N
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro p
    simpa [T] using (Set.Finite.mem_toFinset hfin (a := p))
  · refine ⟨AtomicResidualGraphAccepts, ?_, ?_⟩
    · exact fun p a => Eq.to_iff rfl
    · intro p hp
      constructor
      · intro hacc
        cases hacc with
        | base t =>
            left
            have hs' : t = s := by
              simpa [T] using (((Set.Finite.mem_toFinset hfin (a := ([# t], t))).mp hp).1)
            simpa [hs']
        | step hstep hq =>
            right
            have hpT : p.2 = s ∧ list_degree p.1 ≤ N ∧ (∀ B ∈ p.1, ∃ C ∈ src, Subformula B C) := by
              simpa [T] using ((Set.Finite.mem_toFinset hfin (a := p)).mp hp)
            have hqdata := thm_residual_step_degree_subformula_000070 src p _ hpT.2.2 hstep
            refine ⟨_, ?_, hqdata.2.1, hstep, hq⟩
            apply (Set.Finite.mem_toFinset hfin).mpr
            refine ⟨hqdata.1.trans hpT.1, le_trans (Nat.le_of_lt hqdata.2.1) hpT.2.1, hqdata.2.2⟩
      · intro h
        rcases h with rfl | ⟨q, hqS, hlt, hstep, hgood⟩
        · exact AtomicResidualGraphAccepts.base s
        · exact AtomicResidualGraphAccepts.step hstep hgood


/-- Acceptance is equivalent to the base state or one accepting step. -/
theorem thm_residual_accepts_base_or_step_000097 : ∀ p : AtomicResidualState, AtomicResidualGraphAccepts p ↔ (p = ([# (p.2)], p.2) ∨ ∃ q : AtomicResidualState, AtomicResidualGraphStep p q ∧ AtomicResidualGraphAccepts q) := by
  rintro ⟨Γ, s⟩
  change AtomicResidualGraphAccepts (Γ, s) ↔
    ((Γ, s) = ([# s], s) ∨ ∃ q : AtomicResidualState, AtomicResidualGraphStep (Γ, s) q ∧ AtomicResidualGraphAccepts q)
  constructor
  · intro hacc
    cases hacc with
    | base t =>
        exact Or.symm (Or.inr rfl)
    | step hstep hacc =>
        right
        exact ⟨_, hstep, hacc⟩
  · intro h
    rcases h with h | ⟨q, hstep, hacc⟩
    · cases h
      exact AtomicResidualGraphAccepts.base s
    · exact AtomicResidualGraphAccepts.step hstep hacc


/-- Acceptance iff the residual state reaches its atomic base state. -/
theorem thm_accepts_iff_reaches_base_000099 : ∀ p : AtomicResidualState, AtomicResidualGraphAccepts p ↔ Relation.ReflTransGen AtomicResidualGraphStep p ([# (p.2)], p.2) := by
  intro p
  constructor
  · intro hacc
    induction hacc with
    | base s =>
        exact Relation.ReflTransGen.refl
    | step hstep hacc ih =>
        cases hstep with
        | rdiv Γ L Δ Λ A B s hc harg =>
            simpa using
              (Relation.ReflTransGen.head
                (AtomicResidualGraphStep.rdiv Γ L Δ Λ A B s hc harg) ih)
        | ldiv Γ Γ₁ Δ R A B s hc harg =>
            simpa using
              (Relation.ReflTransGen.head
                (AtomicResidualGraphStep.ldiv Γ Γ₁ Δ R A B s hc harg) ih)
  · intro hreach
    cases p with
    | mk Γ s =>
        exact Relation.ReflTransGen.head_induction_on
          (r := AtomicResidualGraphStep)
          (b := ([# s], s))
          (motive := fun a _ => AtomicResidualGraphAccepts a)
          hreach
          (AtomicResidualGraphAccepts.base s)
          (fun hstep _ hacc => AtomicResidualGraphAccepts.step hstep hacc)


/-- Reachable states are finite and acceptance is the least predecessor-closed reachable set. -/
theorem thm_reachable_accepts_least_set_000103 : ∀ p : AtomicResidualState,
  Set.Finite { q : AtomicResidualState | Relation.ReflTransGen AtomicResidualGraphStep p q } ∧
    ∀ q : AtomicResidualState,
      Relation.ReflTransGen AtomicResidualGraphStep p q →
        (AtomicResidualGraphAccepts q ↔
          ∀ S : Set AtomicResidualState,
            ([# (p.2)], p.2) ∈ S →
            (∀ a b : AtomicResidualState,
              Relation.ReflTransGen AtomicResidualGraphStep p a →
              Relation.ReflTransGen AtomicResidualGraphStep p b →
              AtomicResidualGraphStep a b →
              b ∈ S →
              a ∈ S) →
            q ∈ S) := by
  intro p
  have hp_sub : ∀ B ∈ p.1, ∃ C ∈ p.1, Subformula B C := by
    intro B hB
    exact ⟨B, hB, Subformula.refl B⟩
  have hreach_inv :
      ∀ q : AtomicResidualState,
        Relation.ReflTransGen AtomicResidualGraphStep p q →
          q.2 = p.2 ∧
            list_degree q.1 ≤ list_degree p.1 ∧
            (∀ B ∈ q.1, ∃ C ∈ p.1, Subformula B C) := by
    intro q hq
    induction hq with
    | refl =>
        exact ⟨rfl, le_rfl, hp_sub⟩
    | tail hreach hstep ih =>
        rcases thm_residual_step_degree_subformula_000070 p.1 _ _ ih.2.2 hstep with
          ⟨hs, hlt, hsub⟩
        exact ⟨hs.trans ih.1, le_trans (Nat.le_of_lt hlt) ih.2.1, hsub⟩
  have hacc_to_reaches_base :
      ∀ r : AtomicResidualState,
        AtomicResidualGraphAccepts r →
          Relation.ReflTransGen AtomicResidualGraphStep r ([# (r.2)], r.2) := by
    exact fun r a => (fun p => (thm_accepts_iff_reaches_base_000099 p).mp) r a
  have hreaches_base_to_acc :
      ∀ r : AtomicResidualState,
        Relation.ReflTransGen AtomicResidualGraphStep r ([# (r.2)], r.2) →
          AtomicResidualGraphAccepts r := by
    exact fun r a => (fun p => (thm_accepts_iff_reaches_base_000099 p).mpr) r a
  constructor
  · refine (thm_degree_bounded_subformula_slice_finite_000072 p.1 p.2 (list_degree p.1)).subset ?_
    exact Set.setOf_subset_setOf_of_imp hreach_inv
  · intro q hq
    constructor
    · intro hacc
      intro S hbase hpred
      have hs : q.2 = p.2 := (hreach_inv q hq).1
      have hqbase : Relation.ReflTransGen AtomicResidualGraphStep q ([# (p.2)], p.2) := by
        simpa [hs] using hacc_to_reaches_base q hacc
      have hleast_of_path :
          ∀ {a : AtomicResidualState},
            Relation.ReflTransGen AtomicResidualGraphStep a ([# (p.2)], p.2) →
            Relation.ReflTransGen AtomicResidualGraphStep p a →
            a ∈ S := by
        intro a habase
        induction habase using Relation.ReflTransGen.head_induction_on with
        | refl =>
            exact fun a => Set.mem_of_eq_of_mem rfl hbase
        | head hstep hrest ih =>
            intro hpa
            exact hpred _ _ hpa (Relation.ReflTransGen.tail hpa hstep) hstep
              (ih (Relation.ReflTransGen.tail hpa hstep))
      exact Set.mem_of_eq_of_mem rfl (hleast_of_path hqbase hq)
    · intro hleast
      let S : Set AtomicResidualState :=
        {r : AtomicResidualState |
          r = ([# (p.2)], p.2) ∨
            (Relation.ReflTransGen AtomicResidualGraphStep p r ∧ AtomicResidualGraphAccepts r)}
      have hbase : ([# (p.2)], p.2) ∈ S := by
        left
        exact Prod.mk_right_inj.mpr rfl
      have hclosed :
          ∀ a b : AtomicResidualState,
            Relation.ReflTransGen AtomicResidualGraphStep p a →
            Relation.ReflTransGen AtomicResidualGraphStep p b →
            AtomicResidualGraphStep a b →
            b ∈ S →
            a ∈ S := by
        intro a b ha hb hstep hbS
        rcases hbS with rfl | ⟨_, hbacc⟩
        · right
          exact ⟨ha, AtomicResidualGraphAccepts.step hstep (AtomicResidualGraphAccepts.base (p.2))⟩
        · right
          exact ⟨ha, AtomicResidualGraphAccepts.step hstep hbacc⟩
      have hqS : q ∈ S := hleast S hbase hclosed
      rcases hqS with rfl | ⟨_, hacc⟩
      · exact AtomicResidualGraphAccepts.base (p.2)
      · exact hacc


/-- Reachable residual states admit an exact finite Boolean acceptance labeling. -/
theorem thm_reachable_residual_bool_labeling_000101 : ∀ (Γ : List Tp) (A : Tp) (p : AtomicResidualState),
  residualAtomicState Γ A = some p →
    ∃ R : Finset AtomicResidualState,
      (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) ∧
      ∃ good : AtomicResidualState → Bool,
        (∀ q : AtomicResidualState, q ∈ R → (good q = true ↔ AtomicResidualGraphAccepts q)) ∧
        ∀ q : AtomicResidualState, q ∈ R →
          (good q = true ↔
            q = ([# (p.2)], p.2) ∨
              ∃ r : AtomicResidualState,
                r ∈ R ∧
                list_degree r.1 < list_degree q.1 ∧
                AtomicResidualGraphStep q r ∧
                good r = true) := by
  intro Γ A p hres
  classical
  rcases p with ⟨Δ, s⟩
  have hfin :
      Set.Finite {q : AtomicResidualState |
        Relation.ReflTransGen AtomicResidualGraphStep (Δ, s) q} :=
    thm_residual_reachable_finite_000071 Γ Δ A s hres
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro q
    simpa using (Set.Finite.mem_toFinset hfin (a := q))
  · let good : AtomicResidualState → Bool := fun q => decide (AtomicResidualGraphAccepts q)
    refine ⟨good, ?_, ?_⟩
    · intro q hq
      simp [good]
    · intro q hq
      have hreach : Relation.ReflTransGen AtomicResidualGraphStep (Δ, s) q := by
        simpa using ((Set.Finite.mem_toFinset hfin (a := q)).mp hq)
      constructor
      · intro hgood
        have hacc : AtomicResidualGraphAccepts q := by
          simpa [good] using hgood
        rcases (thm_residual_accepts_base_or_step_000097 q).mp hacc with hbase | ⟨r, hstep, hracc⟩
        · left
          have hs : q.2 = s :=
            (thm_residual_reachable_subformula_invariant_000065 Γ Δ A s q hres hreach).1
          simpa [hs] using hbase
        · right
          refine ⟨r, ?_, atomicResidualGraphStep_degree_lt hstep, hstep, ?_⟩
          · exact (Set.Finite.mem_toFinset hfin).mpr (Relation.ReflTransGen.tail hreach hstep)
          · simpa [good] using hracc
      · intro h
        rcases h with hbase | ⟨r, hr, _, hstep, hgoodr⟩
        · have hacc : AtomicResidualGraphAccepts q := by
            simpa [hbase] using (AtomicResidualGraphAccepts.base s)
          simpa [good] using hacc
        · have hracc : AtomicResidualGraphAccepts r := by
            simpa [good] using hgoodr
          have hacc : AtomicResidualGraphAccepts q := AtomicResidualGraphAccepts.step hstep hracc
          simpa [good] using hacc


/-- Unique Boolean labeling of the reachable residual region. -/
theorem thm_unique_reachable_bool_labeling_000106 : ∀ p : AtomicResidualState,
  ∃ R : Finset AtomicResidualState,
    (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) ∧
    ∃! good : {q // q ∈ R} → Bool,
      (∀ q : {q // q ∈ R},
        good q = true ↔
          q.1 = ([# (p.2)], p.2) ∨
            ∃ r : {r // r ∈ R},
              AtomicResidualGraphStep q.1 r.1 ∧
              good r = true) ∧
      ∀ q : {q // q ∈ R},
        (AtomicResidualGraphAccepts q.1 ↔ good q = true) := by
  intro p
  classical
  rcases thm_reachable_accepts_least_set_000103 p with ⟨hfin, _⟩
  let R : Finset AtomicResidualState := hfin.toFinset
  have hR : ∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q := by
    intro q
    simpa [R] using (Set.Finite.mem_toFinset hfin (a := q))
  have hp_sub : ∀ B ∈ p.1, ∃ C ∈ p.1, Subformula B C := by
    intro B hB
    exact ⟨B, hB, Subformula.refl B⟩
  have hreach_inv :
      ∀ q : AtomicResidualState,
        Relation.ReflTransGen AtomicResidualGraphStep p q →
          q.2 = p.2 ∧
            (∀ B ∈ q.1, ∃ C ∈ p.1, Subformula B C) := by
    intro q hq
    induction hq with
    | refl =>
        exact And.symm ⟨hp_sub, rfl⟩
    | tail hreach hstep ih =>
        rcases thm_residual_step_subformula_closed_000068 p.1 _ _ ih.2 hstep with
          ⟨hs, hsub⟩
        exact ⟨hs.trans ih.1, hsub⟩
  refine ⟨R, hR, ?_⟩
  let good : {q // q ∈ R} → Bool := fun q => decide (AtomicResidualGraphAccepts q.1)
  have hgood_acc : ∀ q : {q // q ∈ R}, AtomicResidualGraphAccepts q.1 ↔ good q = true := by
    intro q
    simp [good]
  refine ⟨good, ?_, ?_⟩
  · constructor
    · intro q
      have hreach : Relation.ReflTransGen AtomicResidualGraphStep p q.1 := (hR q.1).mp q.2
      constructor
      · intro hgood
        have hacc : AtomicResidualGraphAccepts q.1 := (hgood_acc q).mpr hgood
        rcases (thm_residual_accepts_base_or_step_000097 q.1).mp hacc with hbase | ⟨r, hstep, hracc⟩
        · left
          have hs : q.1.2 = p.2 := (hreach_inv q.1 hreach).1
          simpa [hs] using hbase
        · right
          let r' : {r // r ∈ R} := ⟨r, (hR r).2 (Relation.ReflTransGen.tail hreach hstep)⟩
          refine ⟨r', ?_, ?_⟩
          · exact bif good q then hstep else hstep
          · exact (hgood_acc r').mp hracc
      · intro h
        rcases h with hbase | ⟨r, hstep, hgood⟩
        · have hacc : AtomicResidualGraphAccepts q.1 := by
            simpa [hbase] using (AtomicResidualGraphAccepts.base (p.2))
          exact (hgood_acc q).mp hacc
        · have hracc : AtomicResidualGraphAccepts r.1 := (hgood_acc r).mpr hgood
          have hacc : AtomicResidualGraphAccepts q.1 := AtomicResidualGraphAccepts.step hstep hracc
          exact (hgood_acc q).mp hacc
    · exact hgood_acc
  · intro g hg
    rcases hg with ⟨_, hg_acc⟩
    funext q
    have hiff : g q = true ↔ good q = true := by
      constructor
      · intro hgtrue
        exact (hgood_acc q).mp ((hg_acc q).mpr hgtrue)
      · intro hgoodtrue
        exact (hg_acc q).mp ((hgood_acc q).mpr hgoodtrue)
    exact Bool.coe_iff_coe.mp hiff <;> simp [hgq, hgoodq] at hiff ⊢


/-- Reverse reachable-region Boolean labeling is unique and matches acceptance. -/
theorem thm_residual_reverse_sweep_unique_000110 : ∀ (Γ : List Tp) (A : Tp) (p : AtomicResidualState),
  residualAtomicState Γ A = some p →
    ∃ R : Finset AtomicResidualState,
      (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) ∧
      ∃! good : {q // q ∈ R} → Bool,
        (∀ q : {q // q ∈ R},
          good q = true ↔
            q.1 = ([# (p.2)], p.2) ∨
              ∃ r : {r // r ∈ R},
                AtomicResidualGraphStep q.1 r.1 ∧
                good r = true) ∧
        ∀ q : {q // q ∈ R},
          (AtomicResidualGraphAccepts q.1 ↔ good q = true) := by
  exact fun Γ A p a => thm_unique_reachable_bool_labeling_000106 p


/-- A residual state has no outgoing step exactly when all formulas in its context are atoms. -/
theorem thm_residual_no_step_iff_atoms_000096_is_false : ¬(∀ (Γ : List Mathling.Lambek.ProductFree.Tp) (s : String), (¬ ∃ q : AutomatedTheoryConstruction.AtomicResidualState, AutomatedTheoryConstruction.AtomicResidualGraphStep (Γ, s) q) ↔ ∀ B ∈ Γ, Mathling.Lambek.ProductFree.is_atom B) := by
  intro h
  let X : Mathling.Lambek.ProductFree.Tp :=
    Mathling.Lambek.ProductFree.Tp.ldiv
      (Mathling.Lambek.ProductFree.Tp.atom "a")
      (Mathling.Lambek.ProductFree.Tp.atom "b")
  have hiff := h [X] "a"
  have hnostep : ¬ ∃ q : AutomatedTheoryConstruction.AtomicResidualState,
      AutomatedTheoryConstruction.AtomicResidualGraphStep ([X], "a") q := by
    intro hs
    rcases hs with ⟨q, hq⟩
    cases hq with
    | rdiv Γ L Δ Λ A B s hc harg =>
        simp [X, Mathling.Lambek.ProductFree.candidates,
          Mathling.Lambek.ProductFree.picks, Mathling.Lambek.ProductFree.splits] at hc
    | ldiv Γ Γ₁ Δ R A B s hc harg =>
        simp [X, Mathling.Lambek.ProductFree.candidates,
          Mathling.Lambek.ProductFree.picks, Mathling.Lambek.ProductFree.splits] at hc
        rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩
        exact (Mathling.Lambek.ProductFree.nonempty_premises harg) rfl
  have hatom : Mathling.Lambek.ProductFree.is_atom X := (hiff.mp hnostep) _ (by exact List.mem_singleton.mpr rfl)
  simp [X, Mathling.Lambek.ProductFree.is_atom] at hatom


/-- Degree-sorted reachable states give a reverse topological order. -/
theorem thm_degree_sorted_reverse_topology_000115 : ∀ p : AtomicResidualState, ∀ R : Finset AtomicResidualState, (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) → ∀ q r : AtomicResidualState, q ∈ R → r ∈ R → AtomicResidualGraphStep q r → (R.toList.mergeSort (fun a b => list_degree a.1 ≤ list_degree b.1)).idxOf r < (R.toList.mergeSort (fun a b => list_degree a.1 ≤ list_degree b.1)).idxOf q := by
  intro p R hR q r hqR hrR hstep
  classical
  let L := R.toList.mergeSort (fun a b => list_degree a.1 ≤ list_degree b.1)
  have hqL : q ∈ L := by
    dsimp [L]
    rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
    exact Finset.mem_toList.mpr hqR
  have hrL : r ∈ L := by
    dsimp [L]
    rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
    exact Finset.mem_toList.mpr hrR
  have hpair : L.Pairwise (fun a b => list_degree a.1 ≤ list_degree b.1) := by
    simpa [L] using
      (R.toList).pairwise_mergeSort
        (le := fun a b => decide (list_degree a.1 ≤ list_degree b.1))
        (fun a b c => by
          simpa using
            (Nat.le_trans :
              list_degree a.1 ≤ list_degree b.1 →
              list_degree b.1 ≤ list_degree c.1 →
              list_degree a.1 ≤ list_degree c.1))
        (by
          intro a b
          simpa using (Nat.le_total (list_degree a.1) (list_degree b.1)))
  have hdeg : list_degree r.1 < list_degree q.1 :=
    atomicResidualGraphStep_degree_lt hstep
  have hqr_ne : q ≠ r := by
    intro hEq
    simp [hEq] at hdeg
  have hiq : L.idxOf q < L.length := List.idxOf_lt_length_of_mem hqL
  have hir : L.idxOf r < L.length := List.idxOf_lt_length_of_mem hrL
  by_contra hnot
  have hidx_ne : L.idxOf q ≠ L.idxOf r := by
    intro hidx
    exact hqr_ne ((List.idxOf_inj (l := L) (x := q) (y := r) hqL).mp hidx)
  have hlt_qr : L.idxOf q < L.idxOf r :=
    lt_of_le_of_ne (Nat.le_of_not_gt hnot) hidx_ne
  have hle_deg : list_degree q.1 ≤ list_degree r.1 := by
    have h := List.Pairwise.rel_get_of_lt hpair
      (a := ⟨L.idxOf q, hiq⟩) (b := ⟨L.idxOf r, hir⟩) hlt_qr
    simpa using h
  exact (not_le_of_gt hdeg) hle_deg


/-- Reverse sweeps on reachable topological orders are canonical. -/
theorem thm_topological_reverse_sweep_canonical_000112 : ∀ p : AtomicResidualState,
  ∀ R : Finset AtomicResidualState,
    (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) →
    ∀ L : List AtomicResidualState,
      L.Nodup →
      (∀ q : AtomicResidualState, q ∈ L ↔ q ∈ R) →
      (∀ q r : AtomicResidualState,
        q ∈ L →
        r ∈ L →
        AtomicResidualGraphStep q r →
        L.idxOf q < L.idxOf r) →
      ∃! good : {q // q ∈ R} → Bool,
        (∀ q : {q // q ∈ R},
          good q = true ↔
            q.1 = ([# (p.2)], p.2) ∨
              ∃ r : {r // r ∈ R},
                AtomicResidualGraphStep q.1 r.1 ∧
                good r = true) ∧
        ∀ q : {q // q ∈ R},
          AtomicResidualGraphAccepts q.1 ↔ good q = true := by
  intro p R hR L hLnodup hL htop
  rcases thm_unique_reachable_bool_labeling_000106 p with ⟨R₀, hR₀, huniq⟩
  have hEq : R = R₀ := by
    apply Finset.ext
    intro q
    rw [hR q, hR₀ q]
  subst R
  exact huniq


/-- A rejecting reachable state reaches a terminal rejecting state. -/
theorem thm_reject_reaches_terminal_reject_000113 : ∀ p q : AtomicResidualState,
  Relation.ReflTransGen AtomicResidualGraphStep p q →
  ¬ AtomicResidualGraphAccepts q →
  ∃ r : AtomicResidualState,
    Relation.ReflTransGen AtomicResidualGraphStep q r ∧
    (¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep r s) ∧
    ¬ AtomicResidualGraphAccepts r := by
  intro p q hpq hqrej
  let S : Set AtomicResidualState :=
    {r : AtomicResidualState |
      Relation.ReflTransGen AtomicResidualGraphStep q r ∧
        ¬ AtomicResidualGraphAccepts r}
  have hqS : q ∈ S := by
    exact ⟨Relation.ReflTransGen.refl, hqrej⟩
  obtain ⟨r, hrS, hmin⟩ :=
    thm_atomic_residual_step_wellfounded_000078.has_min S ⟨q, hqS⟩
  rcases hrS with ⟨hqr, hrrej⟩
  refine ⟨r, hqr, ?_, hrrej⟩
  intro hsucc
  rcases hsucc with ⟨s, hrs⟩
  have hlocal :
      r ≠ ([# (r.2)], r.2) ∧
        ∀ t : AtomicResidualState, AtomicResidualGraphStep r t → ¬ AtomicResidualGraphAccepts t :=
    (thm_residual_rejects_local_iff_000094 r).mp hrrej
  have hsS : s ∈ S := by
    exact ⟨Relation.ReflTransGen.tail hqr hrs, hlocal.2 s hrs⟩
  exact (iff_false_intro (hmin s hsS)).mp hrs


/-- No residual step iff every candidate has underivable argument context. -/
theorem thm_no_step_iff_candidates_blocked_000118 : ∀ (Γ : List Tp) (s : String),
  (¬ ∃ q : AtomicResidualState, AtomicResidualGraphStep (Γ, s) q) ↔
    ((∀ (L Δ Λ : List Tp) (A B : Tp),
        Cand.rdiv L B A Δ Λ ∈ candidates Γ → ¬ (Δ ⇒ A)) ∧
     ∀ (Γ₁ Δ R : List Tp) (A B : Tp),
        Cand.ldiv Γ₁ Δ A B R ∈ candidates Γ → ¬ (Δ ⇒ A)) := by
  intro Γ s
  constructor
  · intro hnostep
    constructor
    · intro L Δ Λ A B hc harg
      exact hnostep ⟨(L ++ [B] ++ Λ, s), AtomicResidualGraphStep.rdiv Γ L Δ Λ A B s hc harg⟩
    · intro Γ₁ Δ R A B hc harg
      exact hnostep ⟨(Γ₁ ++ [B] ++ R, s), AtomicResidualGraphStep.ldiv Γ Γ₁ Δ R A B s hc harg⟩
  · rintro ⟨hrdiv, hldiv⟩ ⟨q, hstep⟩
    cases hstep with
    | rdiv _ L Δ Λ A B _ hc harg =>
        exact (iff_false_intro (hrdiv L Δ Λ A B hc)).mp harg
    | ldiv _ Γ₁ Δ R A B _ hc harg =>
        exact (iff_false_intro (hldiv Γ₁ Δ R A B hc)).mp harg


/-- Rejecting exactly when all reachable terminal states reject. -/
theorem thm_reject_iff_terminal_frontier_rejects_000122 : ∀ q : AtomicResidualState, ¬ AtomicResidualGraphAccepts q ↔ ∀ r : AtomicResidualState, Relation.ReflTransGen AtomicResidualGraphStep q r → (¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep r s) → ¬ AtomicResidualGraphAccepts r := by
  intro q
  constructor
  · intro hq r hqr _ hracc
    apply hq
    exact Relation.ReflTransGen.head_induction_on hqr hracc
      (fun hstep _ hacc => AtomicResidualGraphAccepts.step hstep hacc)
  · intro hterm hqacc
    have hqbase : Relation.ReflTransGen AtomicResidualGraphStep q ([# (q.2)], q.2) :=
      (thm_accepts_iff_reaches_base_000099 q).1 hqacc
    have hbaseTerminal : ¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep ([# (q.2)], q.2) s := by
      rintro ⟨s, hstep⟩
      cases hstep with
      | rdiv Γ L Δ Λ A B t hc harg =>
          simp [candidates, picks] at hc
      | ldiv Γ Γ₁ Δ R A B t hc harg =>
          simp [candidates, picks] at hc
    have hbaseReject : ¬ AtomicResidualGraphAccepts ([# (q.2)], q.2) :=
      hterm ([# (q.2)], q.2) hqbase hbaseTerminal
    exact hbaseReject (AtomicResidualGraphAccepts.base (q.2))


/-- An accepting residual state can reach a terminal rejecting state. -/
theorem thm_accepting_reaches_terminal_reject_000124 : ∃ q : AtomicResidualState, ∃ r : AtomicResidualState, AtomicResidualGraphAccepts q ∧ Relation.ReflTransGen AtomicResidualGraphStep q r ∧ (¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep r s) ∧ ¬ AtomicResidualGraphAccepts r := by
  let A : Tp := # "a" ⧹ # "a"
  let q : AtomicResidualState := ([A, A, A ⧹ # "a"], "a")
  let r : AtomicResidualState := ([A, # "a"], "a")
  have hA : [A] ⇒ A := by
    exact Sequent.ax
  have hAA : [A, A] ⇒ A := by
    have h1 : [# "a", A] ⇒ # "a" := by
      exact Sequent.ldiv_l
        (Δ := [# "a"]) (A := # "a") (Γ := []) (B := # "a") (Λ := [])
        Sequent.ax Sequent.ax
    have h3 : [# "a", A, A] ⇒ # "a" := by
      simpa [List.append_assoc] using
        (Sequent.ldiv_l
          (Δ := [# "a"]) (A := # "a") (Γ := []) (B := # "a") (Λ := [A])
          Sequent.ax h1)
    exact Sequent.ldiv_r (Γ := [A, A]) (A := # "a") (B := # "a") (by exact List.cons_ne_nil A [A]) h3
  have hstep_qr : AtomicResidualGraphStep q r := by
    dsimp [q, r]
    refine AtomicResidualGraphStep.ldiv [A, A, A ⧹ # "a"] [A] [A] [] A (# "a") "a" ?_ ?_
    · simpa [A] using candidates_ldiv_mem [A] [A] ([] : List Tp) A (# "a")
    · exact Sequent.ax
  have hstep_qbase : AtomicResidualGraphStep q ([# "a"], "a") := by
    dsimp [q]
    refine AtomicResidualGraphStep.ldiv [A, A, A ⧹ # "a"] [] [A, A] [] A (# "a") "a" ?_ ?_
    · simpa [A] using candidates_ldiv_mem ([] : List Tp) [A, A] ([] : List Tp) A (# "a")
    · simpa using hAA
  have hqacc : AtomicResidualGraphAccepts q := by
    exact AtomicResidualGraphAccepts.step hstep_qbase (AtomicResidualGraphAccepts.base "a")
  have hnostep_r : ¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep r s := by
    intro hs
    rcases hs with ⟨s, hstep⟩
    dsimp [r, A] at hstep
    cases hstep with
    | rdiv Γ L Δ Λ A' B' t hc harg =>
        simp [candidates, picks, splits] at hc
    | ldiv Γ Γ₁ Δ R A' B' t hc harg =>
        simp [candidates, picks, splits] at hc
        rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩
        exact (nonempty_premises harg) rfl
  have hrrej : ¬ AtomicResidualGraphAccepts r := by
    refine (thm_residual_rejects_local_iff_000094 r).2 ?_
    constructor
    · dsimp [r, A]
      intro h
      cases h
    · intro s hstep
      exact False.elim (hnostep_r ⟨s, hstep⟩)
  refine ⟨q, r, hqacc, ?_, hnostep_r, hrrej⟩
  exact Relation.ReflTransGen.single hstep_qr


/-- Unique degree-sorted reachable-region Boolean labeling. -/
theorem thm_degree_sorted_unique_labeling_000130 : ∀ p : AtomicResidualState, ∀ R : Finset AtomicResidualState,
  (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) →
    let L := R.toList.mergeSort (fun a b => list_degree a.1 ≤ list_degree b.1)
    ∃! good : AtomicResidualState → Bool,
      (∀ q : AtomicResidualState, q ∉ R → good q = false) ∧
      (∀ q : AtomicResidualState,
        q ∈ R →
          (good q = true ↔
            q = ([# (p.2)], p.2) ∨
              ∃ r : AtomicResidualState,
                r ∈ R ∧
                AtomicResidualGraphStep q r ∧
                List.idxOf r L < List.idxOf q L ∧
                good r = true)) ∧
      (∀ q : AtomicResidualState,
        q ∈ R → (good q = true ↔ AtomicResidualGraphAccepts q)) := by
  intro p R hR
  classical
  dsimp
  have hsame :
      ∀ {q : AtomicResidualState},
        Relation.ReflTransGen AtomicResidualGraphStep p q → q.2 = p.2
  · intro q hq
    induction hq with
    | refl =>
        exact String.toByteArray_inj.mp rfl
    | tail hreach hstep ih =>
        cases hstep <;> simpa using ih
  let good : AtomicResidualState → Bool := fun q =>
    if q ∈ R then decide (AtomicResidualGraphAccepts q) else false
  have hgood_out : ∀ q : AtomicResidualState, q ∉ R → good q = false
  · exact fun q a => if_neg a
  have hgood_acc :
      ∀ q : AtomicResidualState, q ∈ R → (good q = true ↔ AtomicResidualGraphAccepts q)
  · intro q hq
    simp [good, hq]
  have hgood_rec :
      ∀ q : AtomicResidualState,
        q ∈ R →
          (good q = true ↔
            q = ([# (p.2)], p.2) ∨
              ∃ r : AtomicResidualState,
                r ∈ R ∧
                AtomicResidualGraphStep q r ∧
                List.idxOf r (R.toList.mergeSort (fun a b => list_degree a.1 ≤ list_degree b.1)) <
                  List.idxOf q (R.toList.mergeSort (fun a b => list_degree a.1 ≤ list_degree b.1)) ∧
                good r = true)
  · intro q hqR
    constructor
    · intro hgoodq
      have hacc : AtomicResidualGraphAccepts q := (hgood_acc q hqR).mp hgoodq
      rcases (thm_residual_accepts_base_or_step_000097 q).mp hacc with hbase | ⟨r, hstep, hracc⟩
      · left
        have hs : q.2 = p.2 := hsame ((hR q).mp hqR)
        simpa [hs] using hbase
      · right
        have hreachq : Relation.ReflTransGen AtomicResidualGraphStep p q := (hR q).mp hqR
        have hrR : r ∈ R := (hR r).mpr (Relation.ReflTransGen.tail hreachq hstep)
        refine ⟨r, hrR, hstep, ?_, (hgood_acc r hrR).mpr hracc⟩
        exact thm_degree_sorted_reverse_topology_000115 p R hR q r hqR hrR hstep
    · intro h
      rcases h with hbase | ⟨r, hrR, hstep, _, hgoodr⟩
      · have hacc : AtomicResidualGraphAccepts q
        · simpa [hbase] using (AtomicResidualGraphAccepts.base (p.2))
        exact (hgood_acc q hqR).mpr hacc
      · have hracc : AtomicResidualGraphAccepts r := (hgood_acc r hrR).mp hgoodr
        have hacc : AtomicResidualGraphAccepts q := AtomicResidualGraphAccepts.step hstep hracc
        exact (hgood_acc q hqR).mpr hacc
  refine ⟨good, ⟨hgood_out, hgood_rec, hgood_acc⟩, ?_⟩
  intro g hg
  rcases hg with ⟨hg_out, hg_rec, hg_acc⟩
  funext q
  by_cases hqR : q ∈ R
  · have hiff : g q = true ↔ good q = true
    · constructor
      · intro hgtrue
        exact (hgood_acc q hqR).mpr ((hg_acc q hqR).mp hgtrue)
      · intro hgoodtrue
        exact (hg_acc q hqR).mpr ((hgood_acc q hqR).mp hgoodtrue)
    exact Bool.coe_iff_coe.mp hiff <;> simp [hgq, hgoodq] at hiff ⊢
  · have hgfalse : g q = false := hg_out q hqR
    have hgoodfalse : good q = false := hgood_out q hqR
    rw [hgfalse, hgoodfalse]


/-- Terminal residual states accept exactly at the singleton atom state. -/
theorem thm_terminal_accepts_singleton_atom_000133 : ∀ r : AtomicResidualState, (¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep r s) → (AtomicResidualGraphAccepts r ↔ r = ([# (r.2)], r.2)) := by
  rintro ⟨Γ, t⟩ hterminal
  constructor
  · intro hacc
    rcases (thm_residual_accepts_base_or_step_000097 (Γ, t)).1 hacc with hbase | ⟨q, hstep, _⟩
    · exact Prod.ext (congrArg Prod.fst hbase) rfl
    · exact False.elim (hterminal ⟨q, hstep⟩)
  · intro hbase
    simpa [hbase] using (AtomicResidualGraphAccepts.base t)


/-- Degree-sorted reverse sweep computes the reachable residual labeling. -/
theorem thm_degree_sorted_reverse_sweep_labeling_000135 : ∀ p : AtomicResidualState, ∀ R : Finset AtomicResidualState,
  (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) →
    let L := R.toList.mergeSort (fun a b => list_degree a.1 ≤ list_degree b.1)
    ∃! good : AtomicResidualState → Bool,
      (∀ q : AtomicResidualState, q ∉ R → good q = false) ∧
      (∀ q : AtomicResidualState,
        q ∈ R →
          (good q = true ↔
            q = ([# (p.2)], p.2) ∨
              ∃ r : AtomicResidualState,
                r ∈ R ∧
                AtomicResidualGraphStep q r ∧
                List.idxOf r L < List.idxOf q L ∧
                good r = true)) ∧
      (∀ q : AtomicResidualState,
        q ∈ R → (good q = true ↔ AtomicResidualGraphAccepts q)) := by
  exact fun p R a =>
      let L := R.toList.mergeSort fun a b => decide (list_degree a.1 ≤ list_degree b.1);
      thm_degree_sorted_unique_labeling_000130 p R a


/-- Acceptance is equivalent to reaching an accepting terminal state. -/
theorem thm_accepts_reaches_accepting_terminal_000131 : ∀ p : AtomicResidualState, AtomicResidualGraphAccepts p ↔ ∃ r : AtomicResidualState, Relation.ReflTransGen AtomicResidualGraphStep p r ∧ (¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep r s) ∧ AtomicResidualGraphAccepts r := by
  intro p
  constructor
  · intro hp
    refine ⟨([# (p.2)], p.2), (thm_accepts_iff_reaches_base_000099 p).1 hp, ?_, AtomicResidualGraphAccepts.base (p.2)⟩
    rintro ⟨s, hstep⟩
    cases hstep with
    | rdiv Γ L Δ Λ A B t hc harg =>
        simp [candidates, picks] at hc
    | ldiv Γ Γ₁ Δ R A B t hc harg =>
        simp [candidates, picks] at hc
  · rintro ⟨r, hpr, hterminal, hracc⟩
    have hsame :
        ∀ {q : AtomicResidualState},
          Relation.ReflTransGen AtomicResidualGraphStep p q → q.2 = p.2 := by
      intro q hq
      induction hq with
      | refl =>
          exact String.toByteArray_inj.mp rfl
      | tail hreach hstep ih =>
          cases hstep <;> simpa using ih
    have hs : r.2 = p.2 := hsame hpr
    have hrbase : r = ([# (r.2)], r.2) :=
      (thm_terminal_accepts_singleton_atom_000133 r hterminal).1 hracc
    have hpbase' : Relation.ReflTransGen AtomicResidualGraphStep p ([# (r.2)], r.2) := by
      rw [hrbase] at hpr
      exact Relation.ReflTransGen.mono (fun a b a_1 => a_1) hpr
    have hpbase : Relation.ReflTransGen AtomicResidualGraphStep p ([# (p.2)], p.2) := by
      simpa [hs] using hpbase'
    exact (thm_accepts_iff_reaches_base_000099 p).mpr hpbase


/-- Topological reverse sweep agrees with residual acceptance. -/
theorem thm_topological_terminal_sweep_accepts_000137 : ∀ p : AtomicResidualState, ∀ L : List AtomicResidualState, L.Nodup → (∀ q : AtomicResidualState, q ∈ L ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) → (∀ q r : AtomicResidualState, q ∈ L → r ∈ L → AtomicResidualGraphStep q r → List.idxOf q L < List.idxOf r L) → ∃ good : AtomicResidualState → Bool, (∀ q : AtomicResidualState, q ∈ L → ((¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep q s) → (good q = true ↔ q = ([# (q.2)], q.2))) ∧ ((∃ s : AtomicResidualState, AtomicResidualGraphStep q s) → (good q = true ↔ ∃ r : AtomicResidualState, r ∈ L ∧ AtomicResidualGraphStep q r ∧ List.idxOf q L < List.idxOf r L ∧ good r = true))) ∧ (∀ q : AtomicResidualState, q ∈ L → (good q = true ↔ AtomicResidualGraphAccepts q)) := by
  intro p L hLnodup hmem htop
  classical
  have hsame :
      ∀ {q : AtomicResidualState},
        Relation.ReflTransGen AtomicResidualGraphStep p q → q.2 = p.2 := by
    intro q hq
    induction hq with
    | refl =>
        exact String.toByteArray_inj.mp rfl
    | tail hreach hstep ih =>
        cases hstep <;> simpa using ih
  have hbase_terminal :
      ∀ s : String, ¬ ∃ q : AtomicResidualState, AtomicResidualGraphStep ([# s], s) q := by
    intro s
    rintro ⟨q, hstep⟩
    cases hstep with
    | rdiv Γ L Δ Λ A B t hc harg =>
        simp [candidates, picks] at hc
    | ldiv Γ Γ₁ Δ R A B t hc harg =>
        simp [candidates, picks] at hc
  rcases thm_unique_reachable_bool_labeling_000106 p with ⟨R, hR, ⟨good0, hgood0, _⟩⟩
  rcases hgood0 with ⟨hgood0_rec, hgood0_acc⟩
  have hLR : ∀ q : AtomicResidualState, q ∈ L ↔ q ∈ R := by
    intro q
    rw [hmem q, hR q]
  let good : AtomicResidualState → Bool := fun q =>
    if hqL : q ∈ L then good0 ⟨q, (hLR q).mp hqL⟩ else false
  refine ⟨good, ?_, ?_⟩
  · intro q hqL
    have hqR : q ∈ R := (hLR q).mp hqL
    have hreachq : Relation.ReflTransGen AtomicResidualGraphStep p q := (hmem q).mp hqL
    let qR : {q // q ∈ R} := ⟨q, hqR⟩
    refine ⟨?_, ?_⟩
    · intro hterminal
      constructor
      · intro hgoodq
        have hgood0q : good0 qR = true := by
          simpa [good, hqL, qR] using hgoodq
        rcases (hgood0_rec qR).mp hgood0q with hbase | ⟨r, hstep, _⟩
        · simpa [hsame hreachq] using hbase
        · exact False.elim (hterminal ⟨r.1, hstep⟩)
      · intro hbase
        have hbase' : q = ([# (p.2)], p.2) := by
          simpa [hsame hreachq] using hbase
        have hgood0q : good0 qR = true := (hgood0_rec qR).mpr (Or.inl hbase')
        simpa [good, hqL, qR] using hgood0q
    · intro hsucc
      constructor
      · intro hgoodq
        have hgood0q : good0 qR = true := by
          simpa [good, hqL, qR] using hgoodq
        rcases (hgood0_rec qR).mp hgood0q with hbase | ⟨r, hstep, hgood0r⟩
        · cases hbase
          exact False.elim (hbase_terminal (p.2) hsucc)
        · refine ⟨r.1, (hLR r.1).mpr r.2, hstep, htop q r.1 hqL ((hLR r.1).mpr r.2) hstep, ?_⟩
          simpa [good, (hLR r.1).mpr r.2] using hgood0r
      · rintro ⟨r, hrL, hstep, _, hgoodr⟩
        have hrR : r ∈ R := (hLR r).mp hrL
        have hgood0r : good0 ⟨r, hrR⟩ = true := by
          simpa [good, hrL] using hgoodr
        have hgood0q : good0 qR = true := by
          exact (hgood0_rec qR).mpr (Or.inr ⟨⟨r, hrR⟩, hstep, hgood0r⟩)
        simpa [good, hqL, qR] using hgood0q
  · intro q hqL
    have hqR : q ∈ R := (hLR q).mp hqL
    let qR : {q // q ∈ R} := ⟨q, hqR⟩
    constructor
    · intro hgoodq
      have hgood0q : good0 qR = true := by
        simpa [good, hqL, qR] using hgoodq
      exact (hgood0_acc qR).mpr hgood0q
    · intro hacc
      have hgood0q : good0 qR = true := (hgood0_acc qR).mp hacc
      simpa [good, hqL, qR] using hgood0q


/-- Acceptance is the least backward-closed subset of a reachable finset. -/
theorem thm_accepts_least_reachable_subset_000143 : ∀ p : AtomicResidualState, ∀ R : Finset AtomicResidualState,
  (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) →
    let A : Set AtomicResidualState := {q : AtomicResidualState | q ∈ R ∧ AtomicResidualGraphAccepts q}
    A ⊆ (↑R : Set AtomicResidualState) ∧
      ((([# (p.2)], p.2) ∈ R) → ([# (p.2)], p.2) ∈ A) ∧
      (∀ q : AtomicResidualState,
        q ∈ R →
          (∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ A) →
            q ∈ A) ∧
      ∀ S : Set AtomicResidualState,
        S ⊆ (↑R : Set AtomicResidualState) →
        ((([# (p.2)], p.2) ∈ R) → ([# (p.2)], p.2) ∈ S) →
        (∀ q : AtomicResidualState,
          q ∈ R →
            (∃ r : AtomicResidualState, AtomicResidualGraphStep q r ∧ r ∈ S) →
              q ∈ S) →
        A ⊆ S := by
  intro p R hR
  dsimp
  constructor
  · intro q hqA
    exact hqA.1
  constructor
  · intro hpR
    exact ⟨hpR, AtomicResidualGraphAccepts.base (p.2)⟩
  constructor
  · intro q hqR hsucc
    rcases hsucc with ⟨r, hstep, hrA⟩
    exact ⟨hqR, AtomicResidualGraphAccepts.step hstep hrA.2⟩
  · intro S _ hSbase hSstep q hqA
    rcases hqA with ⟨hqR, hqacc⟩
    have hreachq : Relation.ReflTransGen AtomicResidualGraphStep p q := (hR q).mp hqR
    rcases thm_reachable_accepts_least_set_000103 p with ⟨_, hleast⟩
    let T : Set AtomicResidualState := {x : AtomicResidualState | x ∈ S ∨ x ∉ (↑R : Set AtomicResidualState)}
    have hTbase : ([# (p.2)], p.2) ∈ T := by
      by_cases hpR : ([# (p.2)], p.2) ∈ R
      · left
        exact Set.mem_of_eq_of_mem rfl (hSbase hpR)
      · right
        simpa [T] using hpR
    have hTstep :
        ∀ a b : AtomicResidualState,
          Relation.ReflTransGen AtomicResidualGraphStep p a →
          Relation.ReflTransGen AtomicResidualGraphStep p b →
          AtomicResidualGraphStep a b →
          b ∈ T →
          a ∈ T := by
      intro a b ha hb hab hbT
      have haR : a ∈ R := (hR a).2 ha
      have hbR : b ∈ R := (hR b).2 hb
      rcases hbT with hbS | hbnotR
      · left
        exact hSstep a haR ⟨b, hab, hbS⟩
      · exact False.elim (hbnotR (by exact Finset.mem_coe.mpr hbR))
    have hqT : q ∈ T := (hleast q hreachq).1 hqacc T hTbase hTstep
    rcases hqT with hqS | hqnotR
    · exact Set.mem_of_eq_of_mem rfl hqS
    · exact False.elim (hqnotR (by exact Finset.mem_coe.mpr hqR))

end AutomatedTheoryConstruction
