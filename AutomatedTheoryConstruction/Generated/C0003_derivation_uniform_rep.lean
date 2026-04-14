import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0002_left_right_only

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

abbrev HasLeftOrientedDerivation (Γ : List Tp) (A : Tp) : Prop :=
  LeftRep Γ A

abbrev HasRightOrientedDerivation (Γ : List Tp) (A : Tp) : Prop :=
  RightRep Γ A

/-- One-sided representability iff there is a uniformly oriented derivation. -/
theorem thm_uniform_derivation_rep_000046 : ∀ (Γ : List Tp) (A : Tp), (HasLeftOrientedDerivation Γ A ∨ HasRightOrientedDerivation Γ A) ↔ (LeftRep Γ A ∨ RightRep Γ A) := by
  exact fun Γ A => Eq.to_iff rfl

/-- A derivable uniformly oriented sequent already belongs to the matching pure fragment. -/
theorem thm_uniform_orientation_yields_fragment_000047 : ∀ (Γ : List Tp) (A : Tp), Γ ⇒ A → (((∀ x ∈ A :: Γ, LeftDivisionOnly x) → LeftRep Γ A) ∧ ((∀ x ∈ A :: Γ, RightDivisionOnly x) → RightRep Γ A)) := by
  intro Γ A hder
  constructor
  · intro hLeft
    have hA : LeftDivisionOnly A := hLeft A (by exact List.mem_cons_self)
    have hΓ : ∀ x ∈ Γ, LeftDivisionOnly x := by
      exact fun x a => List.forall_mem_of_forall_mem_cons hLeft x a
    rcases exists_left_ctx_of_left_only Γ hΓ with ⟨Γ', hΓ'⟩
    rcases exists_left_tp_of_left_only hA with ⟨A', hA'⟩
    refine ⟨Γ', A', hΓ', hA', ?_⟩
    simpa [Left.Sequent, hΓ', hA'] using hder
  · intro hRight
    have hA : RightDivisionOnly A := hRight A (by exact List.mem_cons_self)
    have hΓ : ∀ x ∈ Γ, RightDivisionOnly x := by
      exact fun x a => List.forall_mem_of_forall_mem_cons hRight x a
    rcases exists_right_ctx_of_right_only Γ hΓ with ⟨Γ', hΓ'⟩
    rcases exists_right_tp_of_right_only hA with ⟨A', hA'⟩
    refine ⟨Γ', A', hΓ', hA', ?_⟩
    simpa [Right.Sequent, hΓ', hA'] using hder

/-- Uniformly oriented sequents admit oriented derivations. -/
theorem thm_one_sided_derivation_normalization_000049_is_false : ¬(∀ (Γ : List Tp) (A : Tp), ((∀ x ∈ A :: Γ, LeftDivisionOnly x) → HasLeftOrientedDerivation Γ A) ∧ ((∀ x ∈ A :: Γ, RightDivisionOnly x) → HasRightOrientedDerivation Γ A)) := by
  intro h
  have hAllLeft : ∀ x ∈ (Tp.atom "q") :: [Tp.atom "p"], LeftDivisionOnly x := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> simp [LeftDivisionOnly]
  have hNoLeft : ¬ HasLeftOrientedDerivation [Tp.atom "p"] (Tp.atom "q") := by
    intro hLeft
    change LeftRep [Tp.atom "p"] (Tp.atom "q") at hLeft
    rcases hLeft with ⟨Γ', A', hΓ', hA', hseq'⟩
    have hseq : [Tp.atom "p"] ⇒ Tp.atom "q" := by
      simpa [Left.Sequent, hΓ', hA'] using hseq'
    have hEq : Tp.atom "p" = Tp.atom "q" :=
      (thm_singleton_atom_iff_eq_000008 (A := Tp.atom "p") (s := "q")).mp hseq
    simp at hEq
  exact hNoLeft ((h [Tp.atom "p"] (Tp.atom "q")).1 hAllLeft)

/-- Uniform orientation plus derivability yields a matching oriented derivation. -/
theorem thm_uniform_orientation_implies_oriented_derivation_000055 : ∀ (Γ : List Tp) (A : Tp), (((∀ x ∈ A :: Γ, LeftDivisionOnly x) ∧ Γ ⇒ A) → HasLeftOrientedDerivation Γ A) ∧ (((∀ x ∈ A :: Γ, RightDivisionOnly x) ∧ Γ ⇒ A) → HasRightOrientedDerivation Γ A) := by
  intro Γ A
  constructor
  · intro h
    simpa [HasLeftOrientedDerivation] using
      (thm_uniform_orientation_yields_fragment_000047 Γ A h.2).1 h.1
  · intro h
    simpa [HasRightOrientedDerivation] using
      (thm_uniform_orientation_yields_fragment_000047 Γ A h.2).2 h.1

/-- Left and right representability coincide exactly on atomic derivable sequents. -/
theorem thm_left_right_rep_atomic_iff_000052 : ∀ (Γ : List Tp) (A : Tp), (LeftRep Γ A ∧ RightRep Γ A) ↔ (Γ ⇒ A ∧ AtomicCtx (A :: Γ)) := by
  intro Γ A
  constructor
  · rintro ⟨hLeft, hRight⟩
    rcases hLeft with ⟨ΓL, AL, hΓL, hAL, hseqL⟩
    rcases hRight with ⟨ΓR, AR, hΓR, hAR, _⟩
    refine ⟨?_, ?_⟩
    · simpa [Left.Sequent, hΓL, hAL] using hseqL
    · intro x hx
      have hLeftOnly : LeftDivisionOnly x := by
        rcases List.mem_cons.mp hx with rfl | hx'
        · simpa [hAL] using left_only_of_left_tp AL
        · rw [← hΓL] at hx'
          rcases List.mem_map.mp hx' with ⟨y, hy, rfl⟩
          exact left_only_of_left_tp y
      have hRightOnly : RightDivisionOnly x := by
        rcases List.mem_cons.mp hx with rfl | hx'
        · simpa [hAR] using right_only_of_right_tp AR
        · rw [← hΓR] at hx'
          rcases List.mem_map.mp hx' with ⟨y, hy, rfl⟩
          exact right_only_of_right_tp y
      cases x with
      | atom s =>
          simp [is_atom]
      | ldiv B C =>
          simpa [is_atom, RightDivisionOnly] using hRightOnly
      | rdiv B C =>
          simpa [is_atom, LeftDivisionOnly] using hLeftOnly
  · rintro ⟨hseq, hAtomic⟩
    have hLeftOnly : ∀ x ∈ A :: Γ, LeftDivisionOnly x := by
      intro x hx
      have hxAtom : is_atom x := hAtomic x hx
      cases x with
      | atom s =>
          simp [LeftDivisionOnly]
      | ldiv B C =>
          cases hxAtom
      | rdiv B C =>
          cases hxAtom
    have hRightOnly : ∀ x ∈ A :: Γ, RightDivisionOnly x := by
      intro x hx
      have hxAtom : is_atom x := hAtomic x hx
      cases x with
      | atom s =>
          simp [RightDivisionOnly]
      | ldiv B C =>
          cases hxAtom
      | rdiv B C =>
          cases hxAtom
    exact ⟨
      (thm_uniform_orientation_yields_fragment_000047 Γ A hseq).1 hLeftOnly,
      (thm_uniform_orientation_yields_fragment_000047 Γ A hseq).2 hRightOnly
    ⟩

/-- Left-oriented derivations are exactly the derivable uniformly left-oriented sequents. -/
theorem thm_left_oriented_derivation_exact_000058 : ∀ (Γ : List Tp) (A : Tp), HasLeftOrientedDerivation Γ A ↔ ((∀ x ∈ A :: Γ, LeftDivisionOnly x) ∧ Γ ⇒ A) := by
  intro Γ A
  constructor
  · intro h
    change LeftRep Γ A at h
    rcases h with ⟨Γ', A', hΓ', hA', hseq'⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa [hA'] using left_only_of_left_tp A'
      · rw [← hΓ'] at hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact left_only_of_left_tp y
    · simpa [Left.Sequent, hΓ', hA'] using hseq'
  · intro h
    exact (thm_uniform_orientation_implies_oriented_derivation_000055 Γ A).1 h

/-- Right-oriented derivations are exactly derivable right-only sequents. -/
theorem thm_right_oriented_derivation_exact_000059 : ∀ (Γ : List Tp) (A : Tp), HasRightOrientedDerivation Γ A ↔ ((∀ x ∈ A :: Γ, RightDivisionOnly x) ∧ Γ ⇒ A) := by
  intro Γ A
  constructor
  · intro h
    change RightRep Γ A at h
    rcases h with ⟨Γ', A', hΓ', hA', hseq'⟩
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa [hA'] using right_only_of_right_tp A'
      · rw [← hΓ'] at hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact right_only_of_right_tp y
    · simpa [Right.Sequent, hΓ', hA'] using hseq'
  · intro h
    exact (thm_uniform_orientation_implies_oriented_derivation_000055 Γ A).2 h

/-- One-sided representability is preserved by cut composition. -/
theorem thm_one_sided_rep_cut_closed_000050 : ∀ (Γ Δ Λ : List Tp) (A B : Tp), ((LeftRep Γ A ∧ LeftRep (Δ ++ [A] ++ Λ) B) → LeftRep (Δ ++ Γ ++ Λ) B) ∧ ((RightRep Γ A ∧ RightRep (Δ ++ [A] ++ Λ) B) → RightRep (Δ ++ Γ ++ Λ) B) := by
  intro Γ Δ Λ A B
  constructor
  · intro h
    rcases h with ⟨hΓA, hΔAΛB⟩
    have hLeft1 := (thm_left_oriented_derivation_exact_000058 Γ A).mp hΓA
    have hLeft2 := (thm_left_oriented_derivation_exact_000058 (Δ ++ [A] ++ Λ) B).mp hΔAΛB
    apply (thm_uniform_orientation_implies_oriented_derivation_000055 (Δ ++ Γ ++ Λ) B).1
    constructor
    · intro y hy
      have hy' : y = B ∨ y ∈ Δ ∨ y ∈ Γ ∨ y ∈ Λ := by
        simpa [List.mem_cons, List.mem_append, or_assoc, or_left_comm, or_comm] using hy
      rcases hy' with rfl | hyΔ | hyΓ | hyΛ
      · exact hLeft2.1 y (by exact List.mem_cons_self)
      · exact hLeft2.1 y (by simp [List.mem_cons, List.mem_append, hyΔ])
      · exact hLeft1.1 y (by exact List.mem_cons_of_mem A hyΓ)
      · exact hLeft2.1 y (by simp [List.mem_cons, List.mem_append, hyΛ])
    · exact Mathling.Lambek.ProductFree.cut_admissible hLeft1.2 hLeft2.2
  · intro h
    rcases h with ⟨hΓA, hΔAΛB⟩
    have hRight1 := (thm_right_oriented_derivation_exact_000059 Γ A).mp hΓA
    have hRight2 := (thm_right_oriented_derivation_exact_000059 (Δ ++ [A] ++ Λ) B).mp hΔAΛB
    apply (thm_uniform_orientation_implies_oriented_derivation_000055 (Δ ++ Γ ++ Λ) B).2
    constructor
    · intro y hy
      have hy' : y = B ∨ y ∈ Δ ∨ y ∈ Γ ∨ y ∈ Λ := by
        simpa [List.mem_cons, List.mem_append, or_assoc, or_left_comm, or_comm] using hy
      rcases hy' with rfl | hyΔ | hyΓ | hyΛ
      · exact hRight2.1 y (by exact List.mem_cons_self)
      · exact hRight2.1 y (by simp [List.mem_cons, List.mem_append, hyΔ])
      · exact hRight1.1 y (by exact List.mem_cons_of_mem A hyΓ)
      · exact hRight2.1 y (by simp [List.mem_cons, List.mem_append, hyΛ])
    · exact Mathling.Lambek.ProductFree.cut_admissible hRight1.2 hRight2.2

abbrev LeftOnlyNode (Γ : List Tp) (A : Tp) : Prop :=
  ∀ x ∈ A :: Γ, LeftDivisionOnly x

def LeftFocusedTree : Nat → List Tp → Tp → Prop
  | 0, _, _ => False
  | n + 1, Γ, Tp.atom s =>
      LeftOnlyNode Γ (Tp.atom s) ∧
        (Γ = [Tp.atom s] ∨
          ∃ c ∈ candidates Γ,
            match c with
            | Cand.rdiv L B A Δ Λ =>
                LeftFocusedTree n Δ A ∧
                  LeftFocusedTree n (L ++ [B] ++ Λ) (Tp.atom s)
            | Cand.ldiv Γ₁ Δ A B R =>
                LeftFocusedTree n Δ A ∧
                  LeftFocusedTree n (Γ₁ ++ [B] ++ R) (Tp.atom s))
  | n + 1, Γ, Tp.ldiv A B =>
      LeftOnlyNode Γ (Tp.ldiv A B) ∧ Γ ≠ [] ∧ LeftFocusedTree n ([A] ++ Γ) B
  | n + 1, Γ, Tp.rdiv B A =>
      LeftOnlyNode Γ (Tp.rdiv B A) ∧ Γ ≠ [] ∧ LeftFocusedTree n (Γ ++ [A]) B

/-- Left-only derivable sequents admit a left-homogeneous focused tree. -/
theorem thm_left_only_focused_tree_000062 : ∀ (Γ : List Tp) (A : Tp), ((LeftOnlyNode Γ A) ∧ Γ ⇒ A) → ∃ n : Nat, LeftFocusedTree n Γ A := by
  intro Γ A h
  have hbridge : ∀ {n : Nat} {Γ : List Tp} {A : Tp}, LeftOnlyNode Γ A → FocusedTree n Γ A → LeftFocusedTree n Γ A := by
    intro n
    induction n with
    | zero =>
        intro Γ A hLeft hTree
        cases hTree
    | succ n ih =>
        intro Γ A hLeft hTree
        cases A with
        | atom s =>
            refine ⟨hLeft, ?_⟩
            rcases hTree with rfl | ⟨c, hc, hcTree⟩
            · exact Or.symm (Or.inr rfl)
            · rcases c with ⟨L, B, A, Δ, Λ⟩ | ⟨Γ₁, Δ, A, B, R⟩
              · exfalso
                have hEq : L ++ [B ⧸ A] ++ Δ ++ Λ = Γ := by
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
                have hBad : LeftDivisionOnly (B ⧸ A) := by
                  apply hLeft
                  rw [← hEq]
                  simp
                simp [LeftDivisionOnly] at hBad
              · right
                refine ⟨Cand.ldiv Γ₁ Δ A B R, hc, ?_⟩
                have hEq : Γ₁ ++ Δ ++ [A ⧹ B] ++ R = Γ := by
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
                have hAB : LeftDivisionOnly A ∧ LeftDivisionOnly B := by
                  have : LeftDivisionOnly (A ⧹ B) := by
                    apply hLeft
                    rw [← hEq]
                    simp
                  simpa [LeftDivisionOnly] using this
                have hΔ : LeftOnlyNode Δ A := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact hAB.1
                  · apply hLeft
                    rw [← hEq]
                    simp [hx]
                have hMain : LeftOnlyNode (Γ₁ ++ [B] ++ R) (Tp.atom s) := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact List.Pi.head hLeft
                  · have hx' : x ∈ (Γ₁ ++ [B]) ++ R := by simpa [List.append_assoc] using hx
                    rcases List.mem_append.mp hx' with hxΓ₁B | hxR
                    · rcases List.mem_append.mp hxΓ₁B with hxΓ₁ | hxB
                      · exact hLeft x (by rw [← hEq]; simp [hxΓ₁])
                      · rcases List.mem_singleton.mp hxB with rfl
                        exact (id (And.symm hAB)).left
                    · exact hLeft x (by rw [← hEq]; simp [hxR])
                exact And.imp (ih hΔ) (ih hMain) hcTree
        | ldiv A B =>
            rcases hTree with ⟨hne, hsub⟩
            have hAB : LeftDivisionOnly A ∧ LeftDivisionOnly B := by
              have : LeftDivisionOnly (A ⧹ B) := hLeft _ (by exact List.mem_cons_self)
              simpa [LeftDivisionOnly] using this
            have hSubLeft : LeftOnlyNode ([A] ++ Γ) B := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact (id (And.symm hAB)).left
              · simp at hx
                rcases hx with rfl | hx
                · exact hAB.1
                · exact List.forall_mem_of_forall_mem_cons hLeft x hx
            exact ⟨hLeft, hne, ih hSubLeft hsub⟩
        | rdiv B A =>
            have hBad : LeftDivisionOnly (B ⧸ A) := hLeft _ (by exact List.mem_cons_self)
            simp [LeftDivisionOnly] at hBad
  rcases (thm_sequent_iff_focused_tree_000023 (Γ := Γ) (A := A)).1 h.2 with ⟨n, hn⟩
  exact ⟨n, hbridge h.1 hn⟩

/-- LeftRep inverts left division on nonempty contexts. -/
theorem thm_leftrep_ldiv_inversion_000053 : ∀ (Γ : List Tp) (A B : Tp), Γ ≠ [] → (LeftRep Γ (A ⧹ B) ↔ LeftRep (A :: Γ) B) := by
  intro Γ A B hne
  constructor
  · intro h
    have hExact := (thm_left_oriented_derivation_exact_000058 Γ (A ⧹ B)).mp h
    have hAB : LeftDivisionOnly A ∧ LeftDivisionOnly B := by
      simpa [LeftDivisionOnly] using (hExact.1 (A ⧹ B) (by exact List.mem_cons_self))
    have hLeft : ∀ x ∈ B :: A :: Γ, LeftDivisionOnly x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (id (And.symm hAB)).left
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hAB.1
        · exact hExact.1 x (by exact List.mem_cons_of_mem (A \ B) hx)
    have hSeq : (A :: Γ) ⇒ B := by
      simpa using (ldiv_invertible (Γ := Γ) (A := A) (B := B) hExact.2)
    exact (thm_left_oriented_derivation_exact_000058 (A :: Γ) B).2 ⟨hLeft, hSeq⟩
  · intro h
    have hExact := (thm_left_oriented_derivation_exact_000058 (A :: Γ) B).mp h
    have hLeft : ∀ x ∈ (A ⧹ B) :: Γ, LeftDivisionOnly x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hAB : LeftDivisionOnly A ∧ LeftDivisionOnly B := by
          exact ⟨hExact.1 A (by simp), hExact.1 B (by exact List.mem_cons_self)⟩
        simpa [LeftDivisionOnly] using hAB
      · exact hExact.1 x (by simp [hx])
    have hSeq : Γ ⇒ (A ⧹ B) := by
      simpa using (Sequent.ldiv_r (Γ := Γ) (A := A) (B := B) hne hExact.2)
    exact (thm_left_oriented_derivation_exact_000058 Γ (A ⧹ B)).2 ⟨hLeft, hSeq⟩

abbrev RightOnlyNode (Γ : List Tp) (A : Tp) : Prop :=
  ∀ x ∈ A :: Γ, RightDivisionOnly x

def RightFocusedTree : Nat → List Tp → Tp → Prop
  | 0, _, _ => False
  | n + 1, Γ, Tp.atom s =>
      RightOnlyNode Γ (Tp.atom s) ∧
        (Γ = [Tp.atom s] ∨
          ∃ c ∈ candidates Γ,
            match c with
            | Cand.rdiv L B A Δ Λ =>
                RightFocusedTree n Δ A ∧
                  RightFocusedTree n (L ++ [B] ++ Λ) (Tp.atom s)
            | Cand.ldiv Γ₁ Δ A B R =>
                RightFocusedTree n Δ A ∧
                  RightFocusedTree n (Γ₁ ++ [B] ++ R) (Tp.atom s))
  | n + 1, Γ, Tp.ldiv A B =>
      RightOnlyNode Γ (Tp.ldiv A B) ∧ Γ ≠ [] ∧ RightFocusedTree n ([A] ++ Γ) B
  | n + 1, Γ, Tp.rdiv B A =>
      RightOnlyNode Γ (Tp.rdiv B A) ∧ Γ ≠ [] ∧ RightFocusedTree n (Γ ++ [A]) B

/-- Right-only derivable sequents admit a right-homogeneous focused tree. -/
theorem thm_right_only_focused_tree_000067 : ∀ (Γ : List Tp) (A : Tp), ((RightOnlyNode Γ A) ∧ Γ ⇒ A) → ∃ n : Nat, RightFocusedTree n Γ A := by
  intro Γ A h
  have hbridge : ∀ {n : Nat} {Γ : List Tp} {A : Tp}, RightOnlyNode Γ A → FocusedTree n Γ A → RightFocusedTree n Γ A := by
    intro n
    induction n with
    | zero =>
        intro Γ A hRight hTree
        cases hTree
    | succ n ih =>
        intro Γ A hRight hTree
        cases A with
        | atom s =>
            refine ⟨hRight, ?_⟩
            rcases hTree with rfl | ⟨c, hc, hcTree⟩
            · exact Or.symm (Or.inr rfl)
            · rcases c with ⟨L, B, A, Δ, Λ⟩ | ⟨Γ₁, Δ, A, B, R⟩
              · right
                refine ⟨Cand.rdiv L B A Δ Λ, hc, ?_⟩
                have hEq : L ++ [B ⧸ A] ++ Δ ++ Λ = Γ := by
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
                have hBA : RightDivisionOnly B ∧ RightDivisionOnly A := by
                  have : RightDivisionOnly (B ⧸ A) := by
                    apply hRight
                    rw [← hEq]
                    simp
                  simpa [RightDivisionOnly] using this
                have hΔ : RightOnlyNode Δ A := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact (id (And.symm hBA)).left
                  · apply hRight
                    rw [← hEq]
                    simp [hx]
                have hMain : RightOnlyNode (L ++ [B] ++ Λ) (Tp.atom s) := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact List.Pi.head hRight
                  · have hx' : x ∈ (L ++ [B]) ++ Λ := by
                      simpa [List.append_assoc] using hx
                    rcases List.mem_append.mp hx' with hxLB | hxΛ
                    · rcases List.mem_append.mp hxLB with hxL | hxB
                      · exact hRight x (by rw [← hEq]; simp [hxL])
                      · rcases List.mem_singleton.mp hxB with rfl
                        exact hBA.left
                    · exact hRight x (by rw [← hEq]; simp [hxΛ])
                exact And.imp (ih hΔ) (ih hMain) hcTree
              · exfalso
                have hEq : Γ₁ ++ Δ ++ [A ⧹ B] ++ R = Γ := by
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
                have hBad : RightDivisionOnly (A ⧹ B) := by
                  apply hRight
                  rw [← hEq]
                  simp
                simp [RightDivisionOnly] at hBad
        | ldiv A B =>
            have hBad : RightDivisionOnly (A ⧹ B) := hRight _ (by exact List.mem_cons_self)
            simp [RightDivisionOnly] at hBad
        | rdiv B A =>
            rcases hTree with ⟨hne, hsub⟩
            have hBA : RightDivisionOnly B ∧ RightDivisionOnly A := by
              have : RightDivisionOnly (B ⧸ A) := hRight _ (by exact List.mem_cons_self)
              simpa [RightDivisionOnly] using this
            have hSubRight : RightOnlyNode (Γ ++ [A]) B := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hBA.1
              · have hx' : x ∈ Γ ∨ x = A := by
                  simpa [List.mem_append, List.mem_singleton] using hx
                rcases hx' with hxΓ | rfl
                · exact List.forall_mem_of_forall_mem_cons hRight x hxΓ
                · exact (id (And.symm hBA)).left
            exact ⟨hRight, hne, ih hSubRight hsub⟩
  rcases (thm_sequent_iff_focused_tree_000023 (Γ := Γ) (A := A)).1 h.2 with ⟨n, hn⟩
  exact ⟨n, hbridge h.1 hn⟩

/-- RightRep inverts right division on nonempty contexts. -/
theorem thm_rightrep_rdiv_inversion_000054 : ∀ (Γ : List Tp) (A B : Tp), Γ ≠ [] → (RightRep Γ (B ⧸ A) ↔ RightRep (Γ ++ [A]) B) := by
  intro Γ A B hne
  constructor
  · intro hRight
    have hExact := (thm_right_oriented_derivation_exact_000059 Γ (B ⧸ A)).mp hRight
    have hBA : RightDivisionOnly B ∧ RightDivisionOnly A := by
      have hDiv : RightDivisionOnly (B ⧸ A) := hExact.1 _ (by exact List.mem_cons_self)
      simpa [RightDivisionOnly] using hDiv
    apply (thm_uniform_orientation_implies_oriented_derivation_000055 (Γ ++ [A]) B).2
    constructor
    · intro x hx
      have hx' : x = B ∨ x ∈ Γ ∨ x = A := by
        simpa [List.mem_cons, List.mem_append, or_assoc, or_left_comm, or_comm] using hx
      rcases hx' with rfl | hxΓ | rfl
      · exact hBA.left
      · exact hExact.1 x (by exact List.mem_cons_of_mem (B / A) hxΓ)
      · exact (id (And.symm hBA)).left
    · exact rdiv_invertible hExact.2
  · intro hRight
    have hExact := (thm_right_oriented_derivation_exact_000059 (Γ ++ [A]) B).mp hRight
    have hB : RightDivisionOnly B := hExact.1 _ (by exact List.mem_cons_self)
    have hA : RightDivisionOnly A := hExact.1 _ (by simp)
    apply (thm_uniform_orientation_implies_oriented_derivation_000055 Γ (B ⧸ A)).2
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hxΓ
      · exact ⟨hB, hA⟩
      · exact hExact.1 x (by simp [hxΓ])
    · exact Sequent.rdiv_r hne hExact.2

end AutomatedTheoryConstruction
