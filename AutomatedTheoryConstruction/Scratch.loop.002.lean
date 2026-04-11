import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_foldr_reverse_sweep_accepts_000142 : ∀ p : AtomicResidualState, ∀ R : Finset AtomicResidualState,
  (∀ q : AtomicResidualState, q ∈ R ↔ Relation.ReflTransGen AtomicResidualGraphStep p q) →
  ∀ L : List AtomicResidualState,
    L.Nodup →
    (∀ q : AtomicResidualState, q ∈ L ↔ q ∈ R) →
    (∀ q r : AtomicResidualState,
      q ∈ L →
      r ∈ L →
      AtomicResidualGraphStep q r →
      List.idxOf q L < List.idxOf r L) →
    ∀ q : AtomicResidualState,
      q ∈ R →
        (atomicResidualReverseSweep p L q = true ↔ AtomicResidualGraphAccepts q) := by
  intro p R hR L hLnodup hEnum hTop q hqR
  classical
  have hReach :
      ∀ q : AtomicResidualState,
        q ∈ L ↔ Relation.ReflTransGen AtomicResidualGraphStep p q
  · intro q
    rw [hEnum q, hR q]
  have hsame :
      ∀ {q : AtomicResidualState},
        Relation.ReflTransGen AtomicResidualGraphStep p q → q.2 = p.2
  · intro q hq
    induction hq with
    | refl =>
        rfl
    | tail hreach hstep ih =>
        cases hstep <;> simpa using ih
  have hclosed :
      ∀ q r : AtomicResidualState,
        q ∈ L →
        AtomicResidualGraphStep q r →
        r ∈ L
  · intro q r hqL hstep
    exact (hReach r).mpr (Relation.ReflTransGen.tail ((hReach q).mp hqL) hstep)
  have hscan :
      ∀ L : List AtomicResidualState,
        L.Nodup →
        (∀ q : AtomicResidualState,
          q ∈ L →
          Relation.ReflTransGen AtomicResidualGraphStep p q) →
        (∀ q r : AtomicResidualState,
          q ∈ L →
          AtomicResidualGraphStep q r →
          r ∈ L) →
        (∀ q r : AtomicResidualState,
          q ∈ L →
          r ∈ L →
          AtomicResidualGraphStep q r →
          List.idxOf q L < List.idxOf r L) →
        ∀ q : AtomicResidualState,
          q ∈ L →
          atomicResidualReverseSweep p L q = true ↔ AtomicResidualGraphAccepts q
  · intro L
    induction L with
    | nil =>
        intro hnodup hmem hclosed htop q hq
        cases hq
    | cons a t ih =>
        intro hnodup hmem hclosed htop q hq
        have hcons : (a ∉ t) ∧ t.Nodup := List.nodup_cons.mp hnodup
        have hnotin : a ∉ t := hcons.1
        have hnodup_t : t.Nodup := hcons.2
        have hreacha : Relation.ReflTransGen AtomicResidualGraphStep p a :=
          hmem a (List.mem_cons_self a t)
        have hs : a.2 = p.2 := hsame hreacha
        have hmem_t :
            ∀ q : AtomicResidualState,
              q ∈ t → Relation.ReflTransGen AtomicResidualGraphStep p q
        · intro q hq
          exact hmem q (List.mem_cons_of_mem a hq)
        have hclosed_t :
            ∀ q r : AtomicResidualState,
              q ∈ t →
              AtomicResidualGraphStep q r →
              r ∈ t
        · intro q r hq hr
          have hr_mem : r ∈ a :: t := hclosed q r (List.mem_cons_of_mem a hq) hr
          rcases hr_mem with rfl | hr_mem
          · have hqa : q ≠ a
            · intro hqa
              exact hnotin (hqa ▸ hq)
            have hlt : List.idxOf q (a :: t) < List.idxOf a (a :: t) :=
              htop q a (List.mem_cons_of_mem a hq) (List.mem_cons_self a t) hr
            have : False
            · rw [List.idxOf_cons_ne _ hqa.symm] at hlt
              simpa using hlt
            exact False.elim this
          · exact hr_mem
        have htop_t :
            ∀ q r : AtomicResidualState,
              q ∈ t →
              r ∈ t →
              AtomicResidualGraphStep q r →
              List.idxOf q t < List.idxOf r t
        · intro q r hq hr hstep
          have hqa : q ≠ a
          · intro hqa
            exact hnotin (hqa ▸ hq)
          have hra : r ≠ a
          · intro hra
            exact hnotin (hra ▸ hr)
          have hlt : List.idxOf q (a :: t) < List.idxOf r (a :: t) :=
            htop q r (List.mem_cons_of_mem a hq) (List.mem_cons_of_mem a hr) hstep
          rw [List.idxOf_cons_ne _ hqa.symm, List.idxOf_cons_ne _ hra.symm] at hlt
          omega
        rcases List.mem_cons.mp hq with rfl | hq
        · rw [(thm_residual_accepts_base_or_step_000097 a).symm]
          constructor
          · intro hscan_a
            have hscan_a' :
                a = ([# (p.2)], p.2) ∨
                  ∃ r : AtomicResidualState,
                    AtomicResidualGraphStep a r ∧
                    atomicResidualReverseSweep p t r = true
            · simpa [atomicResidualReverseSweep] using hscan_a
            rcases hscan_a' with hbase | ⟨r, hstep, hrscan⟩
            · left
              simpa [hs] using hbase
            · have hr_mem : r ∈ a :: t := hclosed a r (List.mem_cons_self a t) hstep
              rcases hr_mem with rfl | hr_mem
              · have hlt : List.idxOf a (a :: t) < List.idxOf a (a :: t) :=
                  htop a a (List.mem_cons_self a t) (List.mem_cons_self a t) hstep
                have : False
                · simpa using hlt
                exact False.elim this
              · right
                exact ⟨r, hstep, (ih hnodup_t hmem_t hclosed_t htop_t r hr_mem).mp hrscan⟩
          · intro hacc
            rcases hacc with hbase | ⟨r, hstep, hracc⟩
            · have hbase' : a = ([# (p.2)], p.2)
              · simpa [hs] using hbase
              have hscan_a' :
                  a = ([# (p.2)], p.2) ∨
                    ∃ r : AtomicResidualState,
                      AtomicResidualGraphStep a r ∧
                      atomicResidualReverseSweep p t r = true :=
                Or.inl hbase'
              simpa [atomicResidualReverseSweep] using hscan_a'
            · have hr_mem : r ∈ a :: t := hclosed a r (List.mem_cons_self a t) hstep
              rcases hr_mem with rfl | hr_mem
              · have hlt : List.idxOf a (a :: t) < List.idxOf a (a :: t) :=
                  htop a a (List.mem_cons_self a t) (List.mem_cons_self a t) hstep
                have : False
                · simpa using hlt
                exact False.elim this
              · have hscan_a' :
                  a = ([# (p.2)], p.2) ∨
                    ∃ r : AtomicResidualState,
                      AtomicResidualGraphStep a r ∧
                      atomicResidualReverseSweep p t r = true
                · right
                  exact ⟨r, hstep, (ih hnodup_t hmem_t hclosed_t htop_t r hr_mem).mpr hracc⟩
                simpa [atomicResidualReverseSweep] using hscan_a'
        · have hqa : q ≠ a
          · intro hqa
            exact hnotin (hqa ▸ hq)
          have htail_eq :
              atomicResidualReverseSweep p (a :: t) q = atomicResidualReverseSweep p t q
          · simp [atomicResidualReverseSweep, hqa]
          rw [htail_eq]
          exact ih hnodup_t hmem_t hclosed_t htop_t q hq
  have hqL : q ∈ L := (hEnum q).mpr hqR
  exact hscan L hLnodup (fun q hq => (hReach q).mp hq) hclosed hTop q hqL

end AutomatedTheoryConstruction
