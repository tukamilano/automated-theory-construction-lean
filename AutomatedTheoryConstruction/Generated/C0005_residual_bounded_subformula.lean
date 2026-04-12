import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0004_residual_subformula_finite

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

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
        exact hbase rfl
    | step hstep hacc =>
        exact hsucc _ hstep hacc

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
    simpa [T] using thm_degree_bounded_subformula_slice_finite_000072 src s N
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro p
    simpa [T] using (Set.Finite.mem_toFinset hfin (a := p))
  · refine ⟨AtomicResidualGraphAccepts, ?_, ?_⟩
    · intro p hp
      rfl
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
        left
        rfl
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
        simpa using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen AtomicResidualGraphStep ([# s], s) ([# s], s))
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
  constructor
  · refine (thm_degree_bounded_subformula_slice_finite_000072 p.1 p.2 (list_degree p.1)).subset ?_
    intro q hq
    exact hreach_inv q hq
  · intro q hq
    constructor
    · intro hacc
      intro S hbase hpred
      have hs : q.2 = p.2 := (hreach_inv q hq).1
      have hqbase : Relation.ReflTransGen AtomicResidualGraphStep q ([# (p.2)], p.2) := by
        simpa [hs] using (thm_accepts_iff_reaches_base_000099 q).mp hacc
      have hleast_of_path :
          ∀ {a : AtomicResidualState},
            Relation.ReflTransGen AtomicResidualGraphStep a ([# (p.2)], p.2) →
            Relation.ReflTransGen AtomicResidualGraphStep p a →
            a ∈ S := by
        intro a habase
        induction habase using Relation.ReflTransGen.head_induction_on with
        | refl =>
            intro _
            exact hbase
        | head hstep hrest ih =>
            intro hpa
            exact hpred _ _ hpa (Relation.ReflTransGen.tail hpa hstep) hstep
              (ih (Relation.ReflTransGen.tail hpa hstep))
      exact hleast_of_path hqbase hq
    · intro hleast
      let S : Set AtomicResidualState :=
        {r : AtomicResidualState |
          r = ([# (p.2)], p.2) ∨
            (Relation.ReflTransGen AtomicResidualGraphStep p r ∧ AtomicResidualGraphAccepts r)}
      have hbase : ([# (p.2)], p.2) ∈ S := by
        left
        rfl
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
        exact ⟨rfl, hp_sub⟩
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
          · simpa [r'] using hstep
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
    cases hgq : g q <;> cases hgoodq : good q <;> simp [hgq, hgoodq] at hiff ⊢

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
  intro Γ A p hp
  exact thm_unique_reachable_bool_labeling_000106 p

end AutomatedTheoryConstruction
