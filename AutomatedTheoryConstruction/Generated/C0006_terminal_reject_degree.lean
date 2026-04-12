import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0005_residual_bounded_subformula

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

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
  have hatom : Mathling.Lambek.ProductFree.is_atom X := (hiff.mp hnostep) _ (by simp [X])
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
  exact hmin s hsS hrs

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
        exact hrdiv L Δ Λ A B hc harg
    | ldiv _ Γ₁ Δ R A B _ hc harg =>
        exact hldiv Γ₁ Δ R A B hc harg

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
    exact Sequent.ldiv_r (Γ := [A, A]) (A := # "a") (B := # "a") (by simp) h3
  have hstep_qr : AtomicResidualGraphStep q r := by
    dsimp [q, r]
    refine AtomicResidualGraphStep.ldiv [A, A, A ⧹ # "a"] [A] [A] [] A (# "a") "a" ?_ ?_
    · simpa [A] using candidates_ldiv_mem [A] [A] ([] : List Tp) A (# "a")
    · simpa using hA
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
  exact Relation.ReflTransGen.head hstep_qr Relation.ReflTransGen.refl

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
        rfl
    | tail hreach hstep ih =>
        cases hstep <;> simpa using ih
  let good : AtomicResidualState → Bool := fun q =>
    if q ∈ R then decide (AtomicResidualGraphAccepts q) else false
  have hgood_out : ∀ q : AtomicResidualState, q ∉ R → good q = false
  · intro q hq
    simp [good, hq]
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
        simpa using (thm_degree_sorted_reverse_topology_000115 p R hR q r hqR hrR hstep)
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
    cases hgq : g q <;> cases hgoodq : good q <;> simp [hgq, hgoodq] at hiff ⊢
  · have hgfalse : g q = false := hg_out q hqR
    have hgoodfalse : good q = false := hgood_out q hqR
    rw [hgfalse, hgoodfalse]

/-- Terminal residual states accept exactly at the singleton atom state. -/
theorem thm_terminal_accepts_singleton_atom_000133 : ∀ r : AtomicResidualState, (¬ ∃ s : AtomicResidualState, AtomicResidualGraphStep r s) → (AtomicResidualGraphAccepts r ↔ r = ([# (r.2)], r.2)) := by
  rintro ⟨Γ, t⟩ hterminal
  constructor
  · intro hacc
    rcases (thm_residual_accepts_base_or_step_000097 (Γ, t)).1 hacc with hbase | ⟨q, hstep, _⟩
    · exact hbase
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
  intro p R hR
  simpa using AutomatedTheoryConstruction.thm_degree_sorted_unique_labeling_000130 p R hR

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
          rfl
      | tail hreach hstep ih =>
          cases hstep <;> simpa using ih
    have hs : r.2 = p.2 := hsame hpr
    have hrbase : r = ([# (r.2)], r.2) :=
      (thm_terminal_accepts_singleton_atom_000133 r hterminal).1 hracc
    have hpbase' : Relation.ReflTransGen AtomicResidualGraphStep p ([# (r.2)], r.2) := by
      rw [hrbase] at hpr
      exact hpr
    have hpbase : Relation.ReflTransGen AtomicResidualGraphStep p ([# (p.2)], p.2) := by
      simpa [hs] using hpbase'
    exact (thm_accepts_iff_reaches_base_000099 p).2 hpbase

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
        rfl
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
        exact hSbase hpR
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
      · exact False.elim (hbnotR (by simpa using hbR))
    have hqT : q ∈ T := (hleast q hreachq).1 hqacc T hTbase hTstep
    rcases hqT with hqS | hqnotR
    · exact hqS
    · exact False.elim (hqnotR (by simpa using hqR))

end AutomatedTheoryConstruction
