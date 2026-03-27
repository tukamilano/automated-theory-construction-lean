import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


/-- Each Fock ket is an eigenvector of the number operator with eigenvalue n. -/
theorem thm_number_ket_eigenvalue_000001 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number (bc.ket n) = (n : ℂ) • bc.ket n := by
  intro V _ _ bc n
  cases n with
  | zero =>
      rw [bc.ket_zero, bc.number_vacuum]
      simp
  | succ n =>
      calc
        bc.number (bc.ket (n + 1))
            = bc.aDagger (bc.a (bc.ket (n + 1))) := rfl
        _ = bc.aDagger ((↑(n + 1) : ℂ) • bc.ket n) := by
          rw [bc.a_ket_succ]
        _ = (↑(n + 1) : ℂ) • bc.aDagger (bc.ket n) := by
          rw [map_smul]
        _ = (↑(n + 1) : ℂ) • bc.ket (n + 1) := by
          rw [bc.aDagger_ket]


/-- The number operator commutes with powers of the annihilation operator by a scalar factor. -/
theorem thm_comm_number_a_pow_000003 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number * bc.a ^ n - bc.a ^ n * bc.number = (-(n : ℂ)) • bc.a ^ n := by
  intro V _ _ bc n
  induction n with
  | zero =>
      simp [BosonCore.number]
  | succ n ih =>
      calc
        bc.number * bc.a ^ (n + 1) - bc.a ^ (n + 1) * bc.number
            = (bc.number * bc.a ^ n - bc.a ^ n * bc.number) * bc.a
                + bc.a ^ n * (bc.number * bc.a - bc.a * bc.number) := by
                  simp [pow_succ, sub_eq_add_neg, mul_add, add_mul, mul_assoc]
        _ = ((-(n : ℂ)) • bc.a ^ n) * bc.a + bc.a ^ n * (-bc.a) := by
              rw [ih, bc.comm_number_a]
        _ = (-(n : ℂ)) • (bc.a ^ n * bc.a) + (-1 : ℂ) • (bc.a ^ n * bc.a) := by
              simp
        _ = ((-(n : ℂ)) + (-1 : ℂ)) • (bc.a ^ n * bc.a) := by
              rw [← add_smul]
        _ = (-((n + 1 : ℕ) : ℂ)) • (bc.a ^ n * bc.a) := by
              congr 1
              rw [Nat.cast_add, Nat.cast_one]
              ring
        _ = (-((n + 1 : ℕ) : ℂ)) • bc.a ^ (n + 1) := by
              simp [pow_succ]


/-- Nonzero vacuum implies the bosonic ket family is linearly independent. -/
theorem thm_ket_linear_independent_of_vacuum_ne_zero_000006 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), bc.vacuum ≠ 0 → LinearIndependent ℂ (fun n : ℕ => bc.ket n) := by
  intro V _ _ bc hvac
  have hket_ne : ∀ n : ℕ, bc.ket n ≠ 0 := by
    intro n
    induction n with
    | zero =>
        simpa [bc.ket_zero] using hvac
    | succ n ih =>
        intro hsucc
        have hdown : (↑(n + 1) : ℂ) • bc.ket n = 0 := by
          simpa [hsucc] using (bc.a_ket_succ n).symm
        have hscalar : (↑(n + 1) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        rcases smul_eq_zero.mp hdown with hzero | hzero
        · exact hscalar hzero
        · exact ih hzero
  have hμ : Function.Injective (fun n : ℕ => (n : ℂ)) := by
    intro m n hmn
    exact Nat.cast_injective (R := ℂ) hmn
  have h_eigenvec : ∀ n : ℕ, bc.number.HasEigenvector (n : ℂ) (bc.ket n) := by
    intro n
    refine ⟨?_, hket_ne n⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using AutomatedTheoryConstruction.thm_number_ket_eigenvalue_000001 bc n
  simpa using
    Module.End.eigenvectors_linearIndependent' bc.number (fun n : ℕ => (n : ℂ)) hμ
      (fun n : ℕ => bc.ket n) h_eigenvec


/-- The number operator commutator with a creation power equals n times that power. -/
theorem thm_comm_number_a_dagger_pow_000002 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number * bc.aDagger ^ n - bc.aDagger ^ n * bc.number = (n : ℂ) • bc.aDagger ^ n := by
  intro V _ _ bc n
  induction n with
  | zero =>
      simp [BosonCore.number]
  | succ n ih =>
      rw [pow_succ]
      calc
        bc.number * (bc.aDagger ^ n * bc.aDagger) - (bc.aDagger ^ n * bc.aDagger) * bc.number
            = (bc.number * bc.aDagger ^ n - bc.aDagger ^ n * bc.number) * bc.aDagger
              + bc.aDagger ^ n * (bc.number * bc.aDagger - bc.aDagger * bc.number) := by
                simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
        _ = ((n : ℂ) • bc.aDagger ^ n) * bc.aDagger + bc.aDagger ^ n * bc.aDagger := by
              rw [ih, bc.comm_number_aDagger]
        _ = ((n : ℂ) + 1) • (bc.aDagger ^ n * bc.aDagger) := by
              rw [smul_mul_assoc]
              nth_rewrite 2 [← one_smul ℂ (bc.aDagger ^ n * bc.aDagger)]
              rw [← add_smul]
        _ = ((n + 1 : ℕ) : ℂ) • bc.aDagger ^ (n + 1) := by
              simp [pow_succ, Nat.cast_add]


/-- Applying a creation power shifts a number eigenvalue by n. -/
theorem thm_a_dagger_pow_shifts_eigenvalue_000005 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) {v : V} {μ : ℂ} (n : ℕ), bc.number v = μ • v → bc.number ((bc.aDagger ^ n) v) = (μ + (n : ℂ)) • ((bc.aDagger ^ n) v) := by
  intro V _ _ bc v μ n hv
  induction n with
  | zero =>
      simpa using hv
  | succ n ih =>
      have hcomm :
          bc.number (bc.aDagger ((bc.aDagger ^ n) v)) =
            bc.aDagger (bc.number ((bc.aDagger ^ n) v)) + bc.aDagger ((bc.aDagger ^ n) v) := by
        simpa [sub_eq_iff_eq_add, add_comm] using
          congrArg (fun f => f ((bc.aDagger ^ n) v)) (BosonCore.comm_number_aDagger (bc := bc))
      rw [ih, map_smul] at hcomm
      simpa [pow_succ', Nat.cast_add, add_assoc, add_left_comm, add_comm, add_smul, one_smul] using hcomm


/-- Expands the commutator of the number operator with a successor creation power. -/
theorem thm_comm_number_a_dagger_pow_succ_step_000007 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), bc.number * bc.aDagger ^ (n + 1) - bc.aDagger ^ (n + 1) * bc.number = (bc.number * bc.aDagger ^ n - bc.aDagger ^ n * bc.number) * bc.aDagger + bc.aDagger ^ n * (bc.number * bc.aDagger - bc.aDagger * bc.number) := by
  intro V _ _ bc n
  rw [pow_succ]
  simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]


/-- A nontrivial finite-dimensional complex vector space admits no bosonic core. -/
theorem thm_finite_dimensional_no_boson_core_000013 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V], ¬ Nonempty (BosonCore V) := by
  intro V _ _ _ _
  rintro ⟨bc⟩
  have htrace : (0 : ℂ) = (Module.finrank ℂ V : ℂ) := by
    calc
      (0 : ℂ) = LinearMap.trace ℂ V (bc.a * bc.aDagger - bc.aDagger * bc.a) := by
        rw [map_sub, LinearMap.trace_mul_comm, sub_self]
      _ = LinearMap.trace ℂ V (1 : Module.End ℂ V) := by
        rw [bc.ccr]
      _ = (Module.finrank ℂ V : ℂ) := by
        rw [LinearMap.trace_one]
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos_iff.mpr inferInstance
  have hfin : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  exact hfin htrace.symm


/-- Repeated creation on a nonvanishing number eigenvector yields a linearly independent family. -/
theorem thm_iterated_creation_linear_independent_000014 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (v : V) (μ : ℂ), bc.vacuum ≠ 0 → bc.number v = μ • v → (∀ n : ℕ, (bc.aDagger ^ n) v ≠ 0) → LinearIndependent ℂ (fun n : ℕ => (bc.aDagger ^ n) v) := by
  intro V _ _ bc v μ _ hEigen hnonzero
  have hμ : Function.Injective (fun n : ℕ => μ + (n : ℂ)) := by
    intro m n hmn
    apply Nat.cast_injective (R := ℂ)
    simpa using add_left_cancel hmn
  have h_eigenvec : ∀ n : ℕ, bc.number.HasEigenvector (μ + (n : ℂ)) ((bc.aDagger ^ n) v) := by
    intro n
    refine ⟨?_, hnonzero n⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using thm_a_dagger_pow_shifts_eigenvalue_000005 (bc := bc) (v := v) (μ := μ) n hEigen
  simpa using
    Module.End.eigenvectors_linearIndependent' bc.number (fun n : ℕ => μ + (n : ℂ)) hμ
      (fun n : ℕ => (bc.aDagger ^ n) v) h_eigenvec


/-- Repeated annihilation lowers a number eigenvalue by n. -/
theorem thm_a_pow_shifts_eigenvalue_down_000008 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) {v : V} {μ : ℂ} (n : ℕ), bc.number v = μ • v → bc.number ((bc.a ^ n) v) = (μ - (n : ℂ)) • ((bc.a ^ n) v) := by
  intro V _ _ bc v μ n hv
  have hsub :
      bc.number ((bc.a ^ n) v) - (bc.a ^ n) (bc.number v) = (-(n : ℂ)) • ((bc.a ^ n) v) := by
    simpa using congrArg (fun f => f v) (thm_comm_number_a_pow_000003 (bc := bc) n)
  rw [hv, map_smul] at hsub
  have hadd :
      bc.number ((bc.a ^ n) v) = (-(n : ℂ)) • ((bc.a ^ n) v) + μ • ((bc.a ^ n) v) := by
    exact sub_eq_iff_eq_add.mp hsub
  calc
    bc.number ((bc.a ^ n) v)
        = (-(n : ℂ)) • ((bc.a ^ n) v) + μ • ((bc.a ^ n) v) := hadd
    _ = (μ - (n : ℂ)) • ((bc.a ^ n) v) := by
      rw [← add_smul, sub_eq_add_neg, add_comm]


/-- The span of the Fock kets is invariant under both ladder operators. -/
theorem thm_fock_span_invariant_under_ladder_000010 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) {v : V}, v ∈ Submodule.span ℂ (Set.range bc.ket) → bc.a v ∈ Submodule.span ℂ (Set.range bc.ket) ∧ bc.aDagger v ∈ Submodule.span ℂ (Set.range bc.ket) := by
  intro V _ _ bc v hv
  let S : Submodule ℂ V := Submodule.span ℂ (Set.range bc.ket)
  have hvS : v ∈ S := by
    simpa [S] using hv
  have haS : bc.a v ∈ S := by
    refine Submodule.span_induction (p := fun x _ => bc.a x ∈ S) ?_ ?_ ?_ ?_ hvS
    · intro x hx
      rcases hx with ⟨n, rfl⟩
      cases n with
      | zero =>
          simpa [bc.ket_zero, bc.vacuum_annihilate] using (Submodule.zero_mem S : (0 : V) ∈ S)
      | succ n =>
          simpa [bc.a_ket_succ] using
            (Submodule.smul_mem S (↑(n + 1) : ℂ) (Submodule.subset_span ⟨n, rfl⟩))
    · simpa [map_zero] using (Submodule.zero_mem S : (0 : V) ∈ S)
    · intro x y hx hy hxS hyS
      simpa [map_add] using (Submodule.add_mem S hxS hyS)
    · intro c x hx hxS
      simpa [map_smul] using (Submodule.smul_mem S c hxS)
  have haDaggerS : bc.aDagger v ∈ S := by
    refine Submodule.span_induction (p := fun x _ => bc.aDagger x ∈ S) ?_ ?_ ?_ ?_ hvS
    · intro x hx
      rcases hx with ⟨n, rfl⟩
      simpa [bc.aDagger_ket] using (Submodule.subset_span (s := Set.range bc.ket) ⟨n + 1, rfl⟩ : bc.ket (n + 1) ∈ S)
    · simpa [map_zero] using (Submodule.zero_mem S : (0 : V) ∈ S)
    · intro x y hx hy hxS hyS
      simpa [map_add] using (Submodule.add_mem S hxS hyS)
    · intro c x hx hxS
      simpa [map_smul] using (Submodule.smul_mem S c hxS)
  constructor
  · simpa [S] using haS
  · simpa [S] using haDaggerS


/-- An invariant submodule containing a nonzero vacuum is not finite-dimensional. -/
theorem thm_invariant_submodule_not_finite_dimensional_000023 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (W : Submodule ℂ V), bc.vacuum ≠ 0 → bc.vacuum ∈ W → (∀ v : V, v ∈ W → bc.a v ∈ W) → (∀ v : V, v ∈ W → bc.aDagger v ∈ W) → ¬ FiniteDimensional ℂ W := by
  intro V _ _ bc W hvac hvac_mem ha haDagger hfd
  let aW : Module.End ℂ W :=
    { toFun := fun w => ⟨bc.a w, ha w w.property⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  let aDaggerW : Module.End ℂ W :=
    { toFun := fun w => ⟨bc.aDagger w, haDagger w w.property⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  let vacuumW : W := ⟨bc.vacuum, hvac_mem⟩
  let bcW : BosonCore W :=
    { a := aW
      aDagger := aDaggerW
      vacuum := vacuumW
      ccr := by
        ext w
        simpa [aW, aDaggerW] using bc.ccr_apply (w : V)
      vacuum_annihilate := by
        ext
        simpa [aW, vacuumW] using bc.vacuum_annihilate }
  letI : FiniteDimensional ℂ W := hfd
  letI : Nontrivial W := by
    refine ⟨⟨vacuumW, 0, ?_⟩⟩
    intro h
    apply hvac
    simpa [vacuumW] using congrArg Subtype.val h
  have htrace : (0 : ℂ) = (Module.finrank ℂ W : ℂ) := by
    calc
      (0 : ℂ) = LinearMap.trace ℂ W (aW * aDaggerW - aDaggerW * aW) := by
        rw [map_sub, LinearMap.trace_mul_comm, sub_self]
      _ = LinearMap.trace ℂ W (1 : Module.End ℂ W) := by
        rw [bcW.ccr]
      _ = (Module.finrank ℂ W : ℂ) := by
        rw [LinearMap.trace_one]
  have hpos : 0 < Module.finrank ℂ W := Module.finrank_pos_iff.mpr inferInstance
  have hfin : (Module.finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  exact hfin htrace.symm


/-- The number operator gives weight m minus n on mixed creation-annihilation monomials. -/
theorem thm_comm_number_mixed_monomial_000035 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (m n : ℕ), bc.number * (bc.aDagger ^ m * bc.a ^ n) - (bc.aDagger ^ m * bc.a ^ n) * bc.number = ((m : ℂ) - (n : ℂ)) • (bc.aDagger ^ m * bc.a ^ n) := by
  intro V _ _ bc m n
  calc
    bc.number * (bc.aDagger ^ m * bc.a ^ n) - (bc.aDagger ^ m * bc.a ^ n) * bc.number
        = (bc.number * bc.aDagger ^ m - bc.aDagger ^ m * bc.number) * bc.a ^ n
            + bc.aDagger ^ m * (bc.number * bc.a ^ n - bc.a ^ n * bc.number) := by
              rw [sub_mul, mul_sub]
              simp [sub_eq_add_neg, mul_assoc]
    _ = ((m : ℂ) • bc.aDagger ^ m) * bc.a ^ n + bc.aDagger ^ m * ((-(n : ℂ)) • bc.a ^ n) := by
          rw [thm_comm_number_a_dagger_pow_000002 (bc := bc) m, thm_comm_number_a_pow_000003 (bc := bc) n]
    _ = ((m : ℂ) - (n : ℂ)) • (bc.aDagger ^ m * bc.a ^ n) := by
          simp [sub_eq_add_neg, add_smul]


/-- A vacuum-containing creation-stable submodule contains the Fock span. -/
theorem thm_fock_span_le_of_vacuum_creation_stable_000039 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (W : Submodule ℂ V), bc.vacuum ∈ W → (∀ v : V, v ∈ W → bc.aDagger v ∈ W) → Submodule.span ℂ (Set.range bc.ket) ≤ W := by
  intro V _ _ bc W hvac hstable
  have hket_mem : ∀ n : ℕ, bc.ket n ∈ W := by
    intro n
    induction n with
    | zero =>
        simpa [bc.ket_zero] using hvac
    | succ n ih =>
        simpa [Nat.succ_eq_add_one, bc.aDagger_ket] using hstable (bc.ket n) ih
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, rfl⟩
  exact hket_mem n


/-- An invariant submodule containing the vacuum inherits a bosonic core. -/
theorem thm_invariant_submodule_inherits_boson_core_000051 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (W : Submodule ℂ V) (hvac : bc.vacuum ∈ W) (ha : ∀ v : V, v ∈ W → bc.a v ∈ W) (haDagger : ∀ v : V, v ∈ W → bc.aDagger v ∈ W), ∃ bcW : BosonCore W, (bcW.vacuum : V) = bc.vacuum ∧ (∀ w : W, (bcW.a w : V) = bc.a (w : V)) ∧ (∀ w : W, (bcW.aDagger w : V) = bc.aDagger (w : V)) := by
  intro V _ _ bc W hvac ha haDagger
  let aW : Module.End ℂ W :=
    { toFun := fun w => ⟨bc.a w, ha w w.property⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  let aDaggerW : Module.End ℂ W :=
    { toFun := fun w => ⟨bc.aDagger w, haDagger w w.property⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  let vacuumW : W := ⟨bc.vacuum, hvac⟩
  let bcW : BosonCore W :=
    { a := aW
      aDagger := aDaggerW
      vacuum := vacuumW
      ccr := by
        ext w
        simpa [aW, aDaggerW] using bc.ccr_apply (w : V)
      vacuum_annihilate := by
        ext
        simpa [aW, vacuumW] using bc.vacuum_annihilate }
  refine ⟨bcW, rfl, ?_, ?_⟩
  · intro w
    rfl
  · intro w
    rfl


/-- The Fock ket span is the least creation-stable submodule containing the vacuum. -/
theorem thm_ket_span_eq_vacuum_creator_hull_000058 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), Submodule.span ℂ (Set.range bc.ket) = sInf {W : Submodule ℂ V | bc.vacuum ∈ W ∧ ∀ v : V, v ∈ W → bc.aDagger v ∈ W} := by
  intro V _ _ bc
  refine le_antisymm (le_sInf ?_) (sInf_le ?_)
  · intro W hW
    exact AutomatedTheoryConstruction.thm_fock_span_le_of_vacuum_creation_stable_000039 (bc := bc) W hW.1 hW.2
  · show bc.vacuum ∈ Submodule.span ℂ (Set.range bc.ket) ∧
      ∀ v : V, v ∈ Submodule.span ℂ (Set.range bc.ket) →
        bc.aDagger v ∈ Submodule.span ℂ (Set.range bc.ket)
    constructor
    · simpa [bc.ket_zero] using
        (Submodule.subset_span (s := Set.range bc.ket) ⟨0, rfl⟩ :
          bc.ket 0 ∈ Submodule.span ℂ (Set.range bc.ket))
    · intro v hv
      exact (AutomatedTheoryConstruction.thm_fock_span_invariant_under_ladder_000010 (bc := bc) hv).2


/-- Polynomial creation-operator evaluation on the vacuum equals the corresponding ket support sum. -/
theorem thm_aeval_a_dagger_vacuum_support_sum_000060 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (p : Polynomial ℂ), (Polynomial.aeval bc.aDagger p) bc.vacuum = p.sum (fun n z => z • bc.ket n) := by
  intro V _ _ bc p
  simpa [BosonCore.ket] using (Polynomial.aeval_endomorphism bc.aDagger bc.vacuum p)


/-- The ket span admits a bosonic core initial among vacuum-containing invariant submodules. -/
theorem thm_fock_span_initial_invariant_core_000065 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), let S : Submodule ℂ V := Submodule.span ℂ (Set.range bc.ket); ∃ bcS : BosonCore S, ∀ (W : Submodule ℂ V), bc.vacuum ∈ W → (∀ v : V, v ∈ W → bc.a v ∈ W) → (∀ v : V, v ∈ W → bc.aDagger v ∈ W) → ∃ (hSW : S ≤ W) (bcW : BosonCore W), (Submodule.inclusion hSW) bcS.vacuum = bcW.vacuum ∧ (∀ s : S, (Submodule.inclusion hSW) (bcS.a s) = bcW.a ((Submodule.inclusion hSW) s)) ∧ (∀ s : S, (Submodule.inclusion hSW) (bcS.aDagger s) = bcW.aDagger ((Submodule.inclusion hSW) s)) := by
  intro V _ _ bc
  let S : Submodule ℂ V := Submodule.span ℂ (Set.range bc.ket)
  change ∃ bcS : BosonCore S, ∀ (W : Submodule ℂ V), bc.vacuum ∈ W → (∀ v : V, v ∈ W → bc.a v ∈ W) → (∀ v : V, v ∈ W → bc.aDagger v ∈ W) → ∃ (hSW : S ≤ W) (bcW : BosonCore W), (Submodule.inclusion hSW) bcS.vacuum = bcW.vacuum ∧ (∀ s : S, (Submodule.inclusion hSW) (bcS.a s) = bcW.a ((Submodule.inclusion hSW) s)) ∧ (∀ s : S, (Submodule.inclusion hSW) (bcS.aDagger s) = bcW.aDagger ((Submodule.inclusion hSW) s))
  have hvacS : bc.vacuum ∈ S := by
    simpa [S, bc.ket_zero] using
      (Submodule.subset_span (s := Set.range bc.ket) ⟨0, rfl⟩ :
        bc.ket 0 ∈ Submodule.span ℂ (Set.range bc.ket))
  have haS : ∀ v : V, v ∈ S → bc.a v ∈ S := by
    intro v hv
    exact (AutomatedTheoryConstruction.thm_fock_span_invariant_under_ladder_000010 (bc := bc) hv).1
  have haDaggerS : ∀ v : V, v ∈ S → bc.aDagger v ∈ S := by
    intro v hv
    exact (AutomatedTheoryConstruction.thm_fock_span_invariant_under_ladder_000010 (bc := bc) hv).2
  rcases AutomatedTheoryConstruction.thm_invariant_submodule_inherits_boson_core_000051
      (bc := bc) S hvacS haS haDaggerS with ⟨bcS, hbcS_vac, hbcS_a, hbcS_aDagger⟩
  refine ⟨bcS, ?_⟩
  intro W hvacW haW haDaggerW
  have hSW : S ≤ W :=
    AutomatedTheoryConstruction.thm_fock_span_le_of_vacuum_creation_stable_000039 (bc := bc) W hvacW haDaggerW
  rcases AutomatedTheoryConstruction.thm_invariant_submodule_inherits_boson_core_000051
      (bc := bc) W hvacW haW haDaggerW with ⟨bcW, hbcW_vac, hbcW_a, hbcW_aDagger⟩
  refine ⟨hSW, bcW, ?_, ?_, ?_⟩
  · apply Subtype.ext
    calc
      (((Submodule.inclusion hSW) bcS.vacuum : W) : V) = (bcS.vacuum : V) := rfl
      _ = bc.vacuum := hbcS_vac
      _ = (bcW.vacuum : V) := hbcW_vac.symm
  · intro s
    apply Subtype.ext
    calc
      (((Submodule.inclusion hSW) (bcS.a s) : W) : V) = (bcS.a s : V) := rfl
      _ = bc.a (s : V) := hbcS_a s
      _ = bc.a (((Submodule.inclusion hSW) s : W) : V) := rfl
      _ = (bcW.a ((Submodule.inclusion hSW) s) : V) := (hbcW_a ((Submodule.inclusion hSW) s)).symm
  · intro s
    apply Subtype.ext
    calc
      (((Submodule.inclusion hSW) (bcS.aDagger s) : W) : V) = (bcS.aDagger s : V) := rfl
      _ = bc.aDagger (s : V) := hbcS_aDagger s
      _ = bc.aDagger (((Submodule.inclusion hSW) s : W) : V) := rfl
      _ = (bcW.aDagger ((Submodule.inclusion hSW) s) : V) := (hbcW_aDagger ((Submodule.inclusion hSW) s)).symm


/-- The span of bosonic ket states is linearly equivalent to finitely supported complex sequences. -/
theorem thm_ket_span_linear_equiv_finsupp_000067 : ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), bc.vacuum ≠ 0 → ∃ Φ : Submodule.span ℂ (Set.range bc.ket) ≃ₗ[ℂ] (ℕ →₀ ℂ), ∀ n : ℕ, Φ ⟨bc.ket n, Submodule.subset_span (Set.mem_range_self n)⟩ = Finsupp.single n (1 : ℂ) := by
  intro V _ _ bc hvac
  have hli : LinearIndependent ℂ (fun n : ℕ => bc.ket n) :=
    AutomatedTheoryConstruction.thm_ket_linear_independent_of_vacuum_ne_zero_000006 (bc := bc) hvac
  refine ⟨hli.linearCombinationEquiv.symm, ?_⟩
  intro n
  simpa [LinearIndependent.repr] using
    hli.repr_eq_single n ⟨bc.ket n, Submodule.subset_span (Set.mem_range_self n)⟩ rfl


/-- Nonzero vacuum makes polynomial creation evaluation on the vacuum injective. -/
theorem thm_aeval_vacuum_injective_of_vacuum_ne_zero_000017 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), bc.vacuum ≠ 0 → Function.Injective (fun p : Polynomial ℂ => (Polynomial.aeval bc.aDagger p) bc.vacuum) := by
  intro V _ _ bc hvac p q hpq
  have hli : LinearIndependent ℂ (fun n : ℕ => bc.ket n) :=
    AutomatedTheoryConstruction.thm_ket_linear_independent_of_vacuum_ne_zero_000006 (bc := bc) hvac
  have hp' :
      (Polynomial.aeval bc.aDagger p) bc.vacuum =
        Finsupp.linearCombination ℂ (fun n : ℕ => bc.ket n) p.toFinsupp := by
    simpa [Polynomial.sum_def, Finsupp.linearCombination_apply, Finsupp.sum,
      Polynomial.support_toFinsupp, Polynomial.toFinsupp_apply] using
      AutomatedTheoryConstruction.thm_aeval_a_dagger_vacuum_support_sum_000060 (bc := bc) p
  have hq' :
      (Polynomial.aeval bc.aDagger q) bc.vacuum =
        Finsupp.linearCombination ℂ (fun n : ℕ => bc.ket n) q.toFinsupp := by
    simpa [Polynomial.sum_def, Finsupp.linearCombination_apply, Finsupp.sum,
      Polynomial.support_toFinsupp, Polynomial.toFinsupp_apply] using
      AutomatedTheoryConstruction.thm_aeval_a_dagger_vacuum_support_sum_000060 (bc := bc) q
  have hto : p.toFinsupp = q.toFinsupp := by
    apply hli.finsuppLinearCombination_injective
    calc
      Finsupp.linearCombination ℂ (fun n : ℕ => bc.ket n) p.toFinsupp
          = (Polynomial.aeval bc.aDagger p) bc.vacuum := hp'.symm
      _ = (Polynomial.aeval bc.aDagger q) bc.vacuum := hpq
      _ = Finsupp.linearCombination ℂ (fun n : ℕ => bc.ket n) q.toFinsupp := hq'
  exact Polynomial.toFinsupp_injective hto


/-- A vector is in the ket span exactly when it is a polynomial vacuum state. -/
theorem thm_mem_ket_span_iff_exists_aeval_000075 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (v : V), v ∈ Submodule.span ℂ (Set.range bc.ket) ↔ ∃ p : Polynomial ℂ, v = (Polynomial.aeval bc.aDagger p) bc.vacuum := by
  intro V _ _ bc v
  constructor
  · intro hv
    rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hv with ⟨c, rfl⟩
    refine ⟨Polynomial.ofFinsupp c, ?_⟩
    simpa [Polynomial.sum_def, Polynomial.support_ofFinsupp, Polynomial.coeff_ofFinsupp,
      Finsupp.sum] using
      (AutomatedTheoryConstruction.thm_aeval_a_dagger_vacuum_support_sum_000060
        (bc := bc) (Polynomial.ofFinsupp c)).symm
  · rintro ⟨p, rfl⟩
    rw [AutomatedTheoryConstruction.thm_aeval_a_dagger_vacuum_support_sum_000060 (bc := bc) p]
    refine Submodule.sum_mem _ ?_
    intro n hn
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self n))


/-- The polynomial quotient by the vacuum-state kernel is linearly equivalent to the ket span. -/
theorem thm_polynomial_quotient_equiv_ket_span_000081 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), let Phi : Polynomial ℂ →ₗ[ℂ] V := (LinearMap.applyₗ (R := ℂ) bc.vacuum).comp (Polynomial.aeval bc.aDagger).toLinearMap; Nonempty ((Polynomial ℂ ⧸ LinearMap.ker Phi) ≃ₗ[ℂ] Submodule.span ℂ (Set.range bc.ket)) := by
  intro V _ _ bc
  classical
  let Phi : Polynomial ℂ →ₗ[ℂ] V :=
    (LinearMap.applyₗ (R := ℂ) bc.vacuum).comp (Polynomial.aeval bc.aDagger).toLinearMap
  change Nonempty ((Polynomial ℂ ⧸ LinearMap.ker Phi) ≃ₗ[ℂ] Submodule.span ℂ (Set.range bc.ket))
  refine ⟨(LinearMap.quotKerEquivRange Phi).trans <| LinearEquiv.ofEq _ _ ?_⟩
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change (Polynomial.aeval bc.aDagger p) bc.vacuum ∈ Submodule.span ℂ (Set.range bc.ket)
    rw [Polynomial.aeval_endomorphism, Polynomial.sum_def]
    refine Submodule.sum_mem _ ?_
    intro n hn
    simpa [BosonCore.ket] using
      Submodule.smul_mem (Submodule.span ℂ (Set.range bc.ket)) (p.coeff n)
        (Submodule.subset_span (Set.mem_range_self n))
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Polynomial.X ^ n, ?_⟩
    simp [Phi, BosonCore.ket]


/-- Commuting a past aDagger times T yields T plus aDagger times the commutator with T. -/
theorem thm_comm_a_a_dagger_mul_000027 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (T : Module.End ℂ V), bc.a * (bc.aDagger * T) - (bc.aDagger * T) * bc.a = T + bc.aDagger * (bc.a * T - T * bc.a) := by
  intro V _ _ bc T
  calc
    bc.a * (bc.aDagger * T) - (bc.aDagger * T) * bc.a
        = (bc.a * bc.aDagger) * T - bc.aDagger * (T * bc.a) := by
            simp [mul_assoc]
    _ = (bc.aDagger * bc.a + 1) * T - bc.aDagger * (T * bc.a) := by
            rw [bc.ccr']
    _ = bc.aDagger * (bc.a * T) + T - bc.aDagger * (T * bc.a) := by
            simp [add_mul, mul_assoc]
    _ = T + (bc.aDagger * (bc.a * T) - bc.aDagger * (T * bc.a)) := by
            abel_nf
    _ = T + bc.aDagger * (bc.a * T - T * bc.a) := by
            rw [mul_sub]


/-- A number eigenvalue equals the exact annihilation nilpotence length. -/
theorem thm_eigenvalue_from_annihilation_length_000034 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) {v : V} {μ : ℂ} (n : ℕ), bc.number v = μ • v → (bc.a ^ (n + 1)) v = 0 → (bc.a ^ n) v ≠ 0 → μ = (n : ℂ) := by
  intro V _ _ bc v μ n hμ hnil hnon
  have ha : bc.a ((bc.a ^ n) v) = 0 := by
    simpa [pow_succ'] using hnil
  have hnum_zero : bc.number ((bc.a ^ n) v) = 0 := by
    unfold BosonCore.number
    change bc.aDagger (bc.a ((bc.a ^ n) v)) = 0
    rw [ha, map_zero]
  have hdown :
      bc.number ((bc.a ^ n) v) = (μ - (n : ℂ)) • ((bc.a ^ n) v) := by
    simpa using thm_a_pow_shifts_eigenvalue_down_000008 (bc := bc) (v := v) (μ := μ) n hμ
  have hsmul : (μ - (n : ℂ)) • ((bc.a ^ n) v) = 0 := by
    rw [← hdown]
    exact hnum_zero
  have hsub : μ - (n : ℂ) = 0 := by
    exact (smul_eq_zero.mp hsmul).resolve_right hnon
  exact sub_eq_zero.mp hsub


/-- Applying a n times to ket n yields n factorial times the vacuum. -/
theorem thm_a_pow_ket_self_factorial_000037 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (n : ℕ), (bc.a ^ n) (bc.ket n) = ((n.factorial : ℕ) : ℂ) • bc.vacuum := by
  intro V _ _ bc n
  induction n with
  | zero =>
      simp [BosonCore.ket]
  | succ n ih =>
      calc
        (bc.a ^ (n + 1)) (bc.ket (n + 1))
            = (bc.a ^ n) (bc.a (bc.ket (n + 1))) := by
                rw [pow_succ]
                rfl
        _ = (bc.a ^ n) (((↑(n + 1) : ℂ)) • bc.ket n) := by
                rw [bc.a_ket_succ]
        _ = ((↑(n + 1) : ℂ)) • (bc.a ^ n) (bc.ket n) := by
                rw [map_smul]
        _ = ((↑(n + 1) : ℂ)) • ((((n.factorial : ℕ) : ℂ)) • bc.vacuum) := by
                rw [ih]
        _ = ((((n + 1) * n.factorial : ℕ) : ℂ)) • bc.vacuum := by
                rw [smul_smul, ← Nat.cast_mul]
        _ = (((n + 1).factorial : ℕ) : ℂ) • bc.vacuum := by
                rw [Nat.factorial_succ]


/-- Applying more annihilations than the ket level gives zero. -/
theorem thm_a_pow_ket_eq_zero_of_lt_000043 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (m n : ℕ), n < m → (bc.a ^ m) (bc.ket n) = 0 := by
  intro V _ _ bc m n hnm
  have hkill : ∀ n : ℕ, (bc.a ^ (n + 1)) (bc.ket n) = 0 := by
    intro n
    induction n with
    | zero =>
        simpa [BosonCore.ket] using bc.vacuum_annihilate
    | succ n ih =>
        calc
          (bc.a ^ ((n + 1) + 1)) (bc.ket (n + 1))
              = (bc.a ^ (n + 1)) (bc.a (bc.ket (n + 1))) := by
                  rw [pow_succ]
                  rfl
          _ = (bc.a ^ (n + 1)) ((↑(n + 1) : ℂ) • bc.ket n) := by
                  rw [bc.a_ket_succ]
          _ = (↑(n + 1) : ℂ) • (bc.a ^ (n + 1)) (bc.ket n) := by
                  rw [map_smul]
          _ = 0 := by
                  rw [ih, smul_zero]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
  calc
    (bc.a ^ (n + k + 1)) (bc.ket n)
        = (bc.a ^ (k + (n + 1))) (bc.ket n) := by
            rw [show n + k + 1 = k + (n + 1) by omega]
    _ = (bc.a ^ k) ((bc.a ^ (n + 1)) (bc.ket n)) := by
            simpa [Module.End.mul_apply] using
              congrArg (fun f => f (bc.ket n)) (pow_add bc.a k (n + 1))
    _ = 0 := by
            rw [hkill n, map_zero]


/-- An invariant submodule containing the vacuum inherits a unique bosonic core structure. -/
theorem thm_unique_boson_core_on_invariant_submodule_000083 : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V) (W : Submodule ℂ V), bc.vacuum ∈ W → (∀ v : V, v ∈ W → bc.a v ∈ W) → (∀ v : V, v ∈ W → bc.aDagger v ∈ W) → ∃! bcW : BosonCore W, (bcW.vacuum : V) = bc.vacuum ∧ (∀ w : W, (bcW.a w : V) = bc.a (w : V)) ∧ (∀ w : W, (bcW.aDagger w : V) = bc.aDagger (w : V)) := by
  intro V _ _ bc W hvac ha haDagger
  rcases AutomatedTheoryConstruction.thm_invariant_submodule_inherits_boson_core_000051
      (bc := bc) (W := W) hvac ha haDagger with
    ⟨bcW, hVac, hA, hADagger⟩
  refine ⟨bcW, ?_, ?_⟩
  · exact ⟨hVac, hA, hADagger⟩
  · intro bcW'
    rintro ⟨hVac', hA', hADagger'⟩
    have hVacW : bcW'.vacuum = bcW.vacuum := by
      apply Subtype.ext
      calc
        (bcW'.vacuum : V) = bc.vacuum := hVac'
        _ = (bcW.vacuum : V) := hVac.symm
    have hAW : bcW'.a = bcW.a := by
      ext w
      exact (hA' w).trans ((hA w).symm)
    have hADaggerW : bcW'.aDagger = bcW.aDagger := by
      ext w
      exact (hADagger' w).trans ((hADagger w).symm)
    cases bcW with
    | mk a aDagger vacuum ccr vacuum_annihilate =>
        cases bcW' with
        | mk a' aDagger' vacuum' ccr' vacuum_annihilate' =>
            cases hAW
            cases hADaggerW
            cases hVacW
            have hccr : ccr' = ccr := Subsingleton.elim _ _
            have hvacuum_annihilate : vacuum_annihilate' = vacuum_annihilate :=
              Subsingleton.elim _ _
            cases hccr
            cases hvacuum_annihilate
            rfl


/-- The Fock span is canonically linearly equivalent to the polynomial representation via creation-operator evaluation on the vacuum. -/
theorem main_thm_fock_span_linear_equiv_polynomial : ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (bc : BosonCore V), bc.vacuum ≠ 0 → ∃ Φ : Polynomial ℂ ≃ₗ[ℂ] Submodule.span ℂ (Set.range bc.ket), ∀ p : Polynomial ℂ, (Φ p : V) = (Polynomial.aeval bc.aDagger p) bc.vacuum := by
  intro V _ _ bc hvac
  have hnum : ∀ n : ℕ, bc.number (bc.ket n) = (n : ℂ) • bc.ket n := by
    intro n
    cases n with
    | zero =>
        rw [bc.ket_zero, bc.number_vacuum]
        simp
    | succ n =>
        calc
          bc.number (bc.ket (n + 1)) = bc.aDagger (bc.a (bc.ket (n + 1))) := rfl
          _ = bc.aDagger ((↑(n + 1) : ℂ) • bc.ket n) := by rw [bc.a_ket_succ]
          _ = (↑(n + 1) : ℂ) • bc.aDagger (bc.ket n) := by rw [map_smul]
          _ = (↑(n + 1) : ℂ) • bc.ket (n + 1) := by rw [bc.aDagger_ket]
  have hket_ne : ∀ n : ℕ, bc.ket n ≠ 0 := by
    intro n
    induction n with
    | zero =>
        simpa [bc.ket_zero] using hvac
    | succ n ih =>
        intro hsucc
        have hdown : (↑(n + 1) : ℂ) • bc.ket n = 0 := by
          simpa [hsucc] using (bc.a_ket_succ n).symm
        have hscalar : (↑(n + 1) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        rcases smul_eq_zero.mp hdown with hzero | hzero
        · exact hscalar hzero
        · exact ih hzero
  have hμ : Function.Injective (fun n : ℕ => (n : ℂ)) := by
    intro m n hmn
    exact Nat.cast_injective (R := ℂ) hmn
  have h_eigenvec : ∀ n : ℕ, bc.number.HasEigenvector (n : ℂ) (bc.ket n) := by
    intro n
    refine ⟨?_, hket_ne n⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hnum n
  have hli : LinearIndependent ℂ (fun n : ℕ => bc.ket n) := by
    simpa using Module.End.eigenvectors_linearIndependent' bc.number (fun n : ℕ => (n : ℂ)) hμ (fun n : ℕ => bc.ket n) h_eigenvec
  refine ⟨(Polynomial.toFinsuppIsoLinear ℂ).trans hli.linearCombinationEquiv, ?_⟩
  intro p
  change (Finsupp.linearCombination ℂ (fun n : ℕ => bc.ket n) (Polynomial.toFinsupp p) : V) =
    (Polynomial.aeval bc.aDagger p) bc.vacuum
  rw [Finsupp.linearCombination_apply]
  simpa [Polynomial.sum_def, Polynomial.support_toFinsupp, Polynomial.toFinsupp_apply, BosonCore.ket] using
    (Polynomial.aeval_endomorphism bc.aDagger bc.vacuum p).symm

end AutomatedTheoryConstruction
