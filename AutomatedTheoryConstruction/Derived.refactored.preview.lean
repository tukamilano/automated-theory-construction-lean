import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

/-- A singleton sequent holds exactly when the two types are equal. -/
theorem thm_singleton_sequent_iff_eq_000001_is_false : ¬(∀ {A B : Tp}, [A] ⇒ B ↔ A = B) := by
  intro h
  let A : Tp := Tp.atom "p"
  let B : Tp := (Tp.atom "q" ⧸ Tp.atom "p") ⧹ Tp.atom "q"
  have hseq : [A] ⇒ B := by
    dsimp [A, B]
    apply Sequent.ldiv_r
    · exact List.cons_ne_nil (#"p") []
    · simpa using
        (Sequent.rdiv_l
          (Δ := [Tp.atom "p"])
          (A := Tp.atom "p")
          (Γ := [])
          (B := Tp.atom "q")
          (Λ := [])
          (C := Tp.atom "q")
          Sequent.ax
          Sequent.ax)
  have hEq : A = B := (h (A := A) (B := B)).mp hseq
  dsimp [A, B] at hEq
  cases hEq

/-- An all-atomic derivable context yields an atomic conclusion and a singleton context. -/
theorem thm_atomic_context_singleton_000002_is_false : ¬(∀ {Γ : List Tp} {A : Tp}, (∀ x ∈ Γ, is_atom x) → Γ ⇒ A → is_atom A ∧ Γ = [A]) := by
  intro h
  let p : Tp := #"p"
  let q : Tp := #"q"
  let A : Tp := ((q ⧸ p) ⧹ q)
  have hctx : ∀ x ∈ [p], is_atom x := by
    intro x hx
    simp at hx
    subst hx
    simp [p, is_atom]
  have hpq : [q ⧸ p, p] ⇒ q := by
    have hp : [p] ⇒ p := Sequent.ax
    have hq : [q] ⇒ q := Sequent.ax
    simpa using
      (Sequent.rdiv_l (Γ := []) (Δ := [p]) (Λ := []) (A := p) (B := q) (C := q) hp hq)
  have hder : [p] ⇒ A := by
    have hne : [p] ≠ [] := by exact List.cons_ne_nil p []
    simpa [A] using (Sequent.ldiv_r (Γ := [p]) (A := q ⧸ p) (B := q) hne hpq)
  have hatom : is_atom A := (h hctx hder).1
  simpa [A, is_atom] using hatom

/-- Decompose a derivation of an atomic succedent. -/
theorem thm_atom_sequent_decompose_000009 : ∀ {Γ : List Tp} {s : String}, Γ ⇒ Tp.atom s → Γ = [Tp.atom s] ∨ (∃ (L : List Tp) (B A : Tp) (Δ Λ : List Tp), Γ = L ++ [B ⧸ A] ++ Δ ++ Λ ∧ (Δ ⇒ A) ∧ (L ++ [B] ++ Λ ⇒ Tp.atom s)) ∨ (∃ (Γ₁ Δ : List Tp) (A B : Tp) (R : List Tp), Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R ∧ (Δ ⇒ A) ∧ (Γ₁ ++ [B] ++ R ⇒ Tp.atom s)) := by
  intro Γ s h
  cases h with
  | ax =>
      exact Or.symm (Or.inr rfl)
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      exact Or.inr <| Or.inl ⟨Γ₁, B, A, Δ, Λ, rfl, d_arg, d_main⟩
  | ldiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      exact Or.inr <| Or.inr ⟨Γ₁, Δ, A, B, Λ, rfl, d_arg, d_main⟩

/-- A singleton derives an atom exactly when it is that atom. -/
theorem thm_singleton_atom_iff_eq_000008 : ∀ {A : Tp} {s : String}, ([A] ⇒ Tp.atom s) ↔ A = Tp.atom s := by
  intro A s
  constructor
  · intro h
    have hnil : ∀ X : Tp, prove1 [] X = false := by
      intro X
      unfold prove1
      cases X <;> simp [candidates, picks]
    have hp : prove1 [A] (Tp.atom s) := prove1_complete h
    cases A with
    | atom t =>
        unfold prove1 at hp
        simp [candidates, picks] at hp
        exact (congrArg Tp.atom ∘ fun a => hp) s
    | ldiv A B =>
        unfold prove1 at hp
        simp [candidates, picks, splits, hnil] at hp
    | rdiv B A =>
        unfold prove1 at hp
        simp [candidates, picks, splits, hnil] at hp
  · intro h
    simpa [h] using (Sequent.ax : [Tp.atom s] ⇒ Tp.atom s)

/-- Classifies derivable singleton sequents. -/
theorem thm_singleton_sequent_classification_000017 : ∀ {A B : Tp}, ([A] ⇒ B) ↔ A = B ∨ (∃ C : Tp, ∃ D : Tp, B = D ⧸ C ∧ ([A] ++ [C] ⇒ D)) ∨ (∃ C : Tp, ∃ D : Tp, B = C ⧹ D ∧ ([C] ++ [A] ⇒ D)) := by
  intro A B
  constructor
  · intro h
    cases B with
    | atom s =>
        exact Or.inl (thm_singleton_atom_iff_eq_000008.mp h)
    | rdiv D C =>
        exact Or.inr <| Or.inl ⟨C, D, rfl, rdiv_invertible h⟩
    | ldiv C D =>
        exact Or.inr <| Or.inr ⟨C, D, rfl, ldiv_invertible h⟩
  · intro h
    rcases h with hEq | ⟨C, D, rfl, hDC⟩ | ⟨C, D, rfl, hCD⟩
    · cases hEq
      exact Sequent.ax
    · exact Sequent.rdiv_r (Γ := [A]) (A := C) (B := D) (by exact List.cons_ne_nil A []) hDC
    · exact Sequent.ldiv_r (Γ := [A]) (A := C) (B := D) (by exact List.cons_ne_nil A []) hCD

/-- Atomic derivations admit a finite focused decomposition tree. -/
theorem thm_atomic_focused_tree_exists_000016 : ∀ {Γ : List Tp} {s : String}, Γ ⇒ Tp.atom s → ∃ n : Nat, proveAux n Γ (Tp.atom s) = true := by
  intro Γ s h
  refine ⟨list_degree Γ + tp_degree (Tp.atom s) + 1, ?_⟩
  have h' : prove2 Γ (Tp.atom s) :=
    (prove2_iff_sequent (Γ := Γ) (A := Tp.atom s)).2 h
  simpa [prove2] using h'

def FocusedTree : Nat → List Tp → Tp → Prop
  | 0, _, _ => False
  | n + 1, Γ, Tp.atom s =>
      Γ = [Tp.atom s] ∨
      ∃ c ∈ candidates Γ,
        match c with
        | Cand.rdiv L B A Δ Λ =>
            FocusedTree n Δ A ∧ FocusedTree n (L ++ [B] ++ Λ) (Tp.atom s)
        | Cand.ldiv Γ₁ Δ A B R =>
            FocusedTree n Δ A ∧ FocusedTree n (Γ₁ ++ [B] ++ R) (Tp.atom s)
  | n + 1, Γ, Tp.ldiv A B =>
      Γ ≠ [] ∧ FocusedTree n ([A] ++ Γ) B
  | n + 1, Γ, Tp.rdiv B A =>
      Γ ≠ [] ∧ FocusedTree n (Γ ++ [A]) B

/-- Atomic `proveAux` is exact for focused trees up to height `n`. -/
theorem thm_proveaux_atom_tree_exact_000021 : ∀ {n : Nat} {Γ : List Tp} {s : String}, proveAux n Γ (# s) = true ↔ FocusedTree n Γ (# s) := by
  suffices hmain : ∀ {n : Nat} {Γ : List Tp} {A : Tp}, proveAux n Γ A = true ↔ FocusedTree n Γ A
  · exact fun {n} {Γ} {s} => Iff.symm ((fun {a b} => iff_comm.mp) hmain)
  · intro n
    induction n with
    | zero =>
        intro Γ A
        cases A <;> simp [proveAux, FocusedTree]
    | succ n ih =>
        intro Γ A
        cases A with
        | atom s =>
            simp only [proveAux, FocusedTree, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
            constructor
            · intro h
              rcases h with h | ⟨c, hc, hcTree⟩
              · exact Or.symm (Or.inr h)
              · refine Or.inr ⟨c, hc, ?_⟩
                cases c <;> simpa [Bool.and_eq_true, ih] using hcTree
            · intro h
              rcases h with h | ⟨c, hc, hcTree⟩
              · exact Or.symm (Or.inr h)
              · refine Or.inr ⟨c, hc, ?_⟩
                cases c <;> simpa [Bool.and_eq_true, ih] using hcTree
        | ldiv A B =>
            simp [proveAux, FocusedTree, Bool.and_eq_true, ih]
        | rdiv B A =>
            simp [proveAux, FocusedTree, Bool.and_eq_true, ih]

/-- Any derivable all-atomic context is a singleton atom. -/
theorem thm_atomic_context_singleton_000011_is_false : ¬(∀ {Γ : List Tp} {A : Tp}, (∀ x ∈ Γ, is_atom x) → Γ ⇒ A → ∃ s : String, Γ = [Tp.atom s]) := by
  intro h
  have h_atoms : ∀ x ∈ ([Tp.atom "r", Tp.atom "p"] : List Tp), is_atom x := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> simp [is_atom]
  have h_rq : [Tp.atom "r", Tp.ldiv (Tp.atom "r") (Tp.atom "q")] ⇒ Tp.atom "q" := by
    simpa using
      (Sequent.ldiv_l
        (Δ := [Tp.atom "r"]) (A := Tp.atom "r")
        (Γ := []) (B := Tp.atom "q") (Λ := []) (C := Tp.atom "q")
        Sequent.ax Sequent.ax)
  have h_rpq :
      [Tp.atom "r", Tp.atom "p", Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q"))] ⇒
        Tp.atom "q" := by
    simpa [List.append_assoc] using
      (Sequent.ldiv_l
        (Δ := [Tp.atom "p"]) (A := Tp.atom "p")
        (Γ := [Tp.atom "r"]) (B := Tp.ldiv (Tp.atom "r") (Tp.atom "q")) (Λ := []) (C := Tp.atom "q")
        Sequent.ax h_rq)
  have h_der :
      [Tp.atom "r", Tp.atom "p"] ⇒
        Tp.rdiv (Tp.atom "q") (Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q"))) := by
    apply Sequent.rdiv_r
    · exact List.cons_ne_nil (#"r") [#"p"]
    · simpa using h_rpq
  rcases h (Γ := [Tp.atom "r", Tp.atom "p"])
      (A := Tp.rdiv (Tp.atom "q") (Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q")))) h_atoms h_der with ⟨s, hs⟩
  have hlen := congrArg List.length hs
  simp at hlen

/-- Derivability is equivalent to existence of a finite focused tree. -/
theorem thm_sequent_iff_focused_tree_000023 : ∀ {Γ : List Tp} {A : Tp}, Γ ⇒ A ↔ ∃ n : Nat, FocusedTree n Γ A := by
  intro Γ A
  have hmain : ∀ {n : Nat} {Γ : List Tp} {A : Tp}, proveAux n Γ A = true ↔ FocusedTree n Γ A := by
    intro n
    induction n with
    | zero =>
        intro Γ A
        cases A <;> simp [proveAux, FocusedTree]
    | succ n ih =>
        intro Γ A
        cases A with
        | atom s =>
            exact thm_proveaux_atom_tree_exact_000021
        | ldiv A B =>
            simp [proveAux, FocusedTree, Bool.and_eq_true, ih]
        | rdiv B A =>
            simp [proveAux, FocusedTree, Bool.and_eq_true, ih]
  constructor
  · intro h
    refine ⟨list_degree Γ + tp_degree A + 1, ?_⟩
    have hprove2 : prove2 Γ A := (prove2_iff_sequent).2 h
    exact (hmain (n := list_degree Γ + tp_degree A + 1) (Γ := Γ) (A := A)).1 hprove2
  · rintro ⟨n, hn⟩
    have haux : proveAux n Γ A = true := (hmain (n := n) (Γ := Γ) (A := A)).2 hn
    exact prove1_sound (proveAux_sound haux)

/-- Exact equivalence between proveAux and focused trees. -/
theorem thm_proveaux_focused_tree_exact_000022 : ∀ {n : Nat} {Γ : List Tp} {A : Tp}, proveAux n Γ A = true ↔ FocusedTree n Γ A := by
  intro n
  induction n with
  | zero =>
      intro Γ A
      cases A <;> simp [proveAux, FocusedTree]
  | succ n ih =>
      intro Γ A
      cases A with
      | atom s =>
          exact thm_proveaux_atom_tree_exact_000021
      | ldiv A B =>
          simp [proveAux, FocusedTree, Bool.and_eq_true, ih]
      | rdiv B A =>
          simp [proveAux, FocusedTree, Bool.and_eq_true, ih]

/-- Any depth above the degree bound exactly captures derivability by focused trees. -/
theorem thm_bounded_focused_tree_threshold_000026 : ∀ {Γ : List Tp} {A : Tp} {m : Nat}, list_degree Γ + tp_degree A + 1 ≤ m → (Γ ⇒ A ↔ FocusedTree m Γ A) := by
  intro Γ A m hm
  constructor
  · intro h
    have hN : proveAux (list_degree Γ + tp_degree A + 1) Γ A = true := by
      simpa [prove2] using ((prove2_iff_sequent (Γ := Γ) (A := A)).2 h)
    have hm' : proveAux m Γ A = true := proveAux_mono_le hm hN
    exact thm_proveaux_focused_tree_exact_000022.mp hm'
  · intro h
    have hm' : proveAux m Γ A = true :=
      (thm_proveaux_focused_tree_exact_000022 (n := m) (Γ := Γ) (A := A)).2 h
    exact prove1_sound (proveAux_sound hm')

/-- The degree bound for focused trees is attained exactly. -/
theorem thm_sharp_focused_degree_bound_000029_is_false : ¬(∀ N : Nat, ∃ Γ : List Tp, ∃ A : Tp, list_degree Γ + tp_degree A = N ∧ Γ ⇒ A ∧ FocusedTree (N + 1) Γ A ∧ ∀ m < N + 1, ¬ FocusedTree m Γ A) := by
  intro hforall
  rcases hforall 0 with ⟨Γ, A, hdeg, hder, _, _⟩
  have hApos : 0 < tp_degree A := by
    cases A <;> simp [tp_degree]
  have hΓpos : 0 < list_degree Γ := by
    rcases List.exists_cons_of_ne_nil (nonempty_premises hder) with ⟨B, Δ, rfl⟩
    have hBpos : 0 < tp_degree B := by
      cases B <;> simp [tp_degree]
    simpa [list_degree] using add_pos_of_pos_of_nonneg hBpos (Nat.zero_le (list_degree Δ))
  have hsum : 0 < list_degree Γ + tp_degree A := add_pos hΓpos hApos
  exact (Nat.ne_of_gt hsum) hdeg

abbrev AtomicCtx (Γ : List Tp) : Prop := ∀ x ∈ Γ, is_atom x

abbrev LeftRep (Γ : List Tp) (A : Tp) : Prop :=
  ∃ Γ' : List Left.Tp, ∃ A' : Left.Tp,
    Left.ctxToProductFree Γ' = Γ ∧ A'.toProductFree = A ∧ Left.Sequent Γ' A'

abbrev RightRep (Γ : List Tp) (A : Tp) : Prop :=
  ∃ Γ' : List Right.Tp, ∃ A' : Right.Tp,
    Right.ctxToProductFree Γ' = Γ ∧ A'.toProductFree = A ∧ Right.Sequent Γ' A'

/-- An atomic-context full sequent is absent from both one-sided fragments. -/
theorem thm_atomic_context_fragment_gap_000025 : ∃ Γ A, AtomicCtx Γ ∧ Γ ⇒ A ∧ ¬ LeftRep Γ A ∧ ¬ RightRep Γ A := by
  refine ⟨[Tp.atom "r", Tp.atom "p"], Tp.rdiv (Tp.atom "q") (Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q"))), ?_⟩
  constructor
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> simp [is_atom]
  constructor
  · have h_rq : [Tp.atom "r", Tp.ldiv (Tp.atom "r") (Tp.atom "q")] ⇒ Tp.atom "q" := by
      simpa using
        (Sequent.ldiv_l
          (Δ := [Tp.atom "r"]) (A := Tp.atom "r")
          (Γ := []) (B := Tp.atom "q") (Λ := []) (C := Tp.atom "q")
          Sequent.ax Sequent.ax)
    have h_rpq :
        [Tp.atom "r", Tp.atom "p", Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q"))] ⇒
          Tp.atom "q" := by
      simpa [List.append_assoc] using
        (Sequent.ldiv_l
          (Δ := [Tp.atom "p"]) (A := Tp.atom "p")
          (Γ := [Tp.atom "r"]) (B := Tp.ldiv (Tp.atom "r") (Tp.atom "q")) (Λ := []) (C := Tp.atom "q")
          Sequent.ax h_rq)
    apply Sequent.rdiv_r
    · exact List.cons_ne_nil (#"r") [#"p"]
    · simpa using h_rpq
  constructor
  · intro hLeft
    rcases hLeft with ⟨Γ', A', hΓ, hA, hseq⟩
    cases A' <;> cases hA
  · intro hRight
    rcases hRight with ⟨Γ', A', hΓ, hA, hseq⟩
    cases A' with
    | atom s =>
        cases hA
    | rdiv B C =>
        cases C with
        | atom s =>
            have hC : (Right.Tp.atom s).toProductFree = Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q")) := by
              injection hA with _ hC
            cases hC
        | rdiv C1 C2 =>
            have hC :
                (Right.Tp.rdiv C1 C2).toProductFree =
                  Tp.ldiv (Tp.atom "p") (Tp.ldiv (Tp.atom "r") (Tp.atom "q")) := by
              injection hA with _ hC
            cases hC

/-- Atomic derivability is exactly the axiom case or a derivable candidate. -/
theorem thm_atomic_candidate_exactness_000020 : ∀ {Γ : List Tp} {s : String}, Γ ⇒ # s ↔ Γ = [# s] ∨ ∃ c ∈ candidates Γ, match c with | Cand.rdiv L B A Δ Λ => Δ ⇒ A ∧ L ++ [B] ++ Λ ⇒ # s | Cand.ldiv Γ₁ Δ A B R => Δ ⇒ A ∧ Γ₁ ++ [B] ++ R ⇒ # s := by
  intro Γ s
  rw [← prove1_iff_sequent]
  unfold prove1
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    rcases h with hEq | ⟨⟨c, hc⟩, -, hcProof⟩
    · exact Or.symm (Or.inr hEq)
    · refine Or.inr ⟨c, hc, ?_⟩
      cases c <;> simpa [Bool.and_eq_true, prove1_iff_sequent] using hcProof
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
    rcases h with hEq | ⟨c, hc, hcProof⟩
    · exact Or.symm (Or.inr hEq)
    · refine Or.inr ?_
      refine ⟨⟨c, hc⟩, by exact List.mem_attach (candidates Γ) ⟨c, hc⟩, ?_⟩
      cases c <;> simpa [Bool.and_eq_true, prove1_iff_sequent] using hcProof

/-- Sharp focused degree witnesses exist for every realizable total degree. -/
theorem thm_sharp_focused_degree_from_two_000033_is_false : ¬(∀ N : Nat, 2 ≤ N → ∃ Γ : List Tp, ∃ A : Tp, list_degree Γ + tp_degree A = N ∧ Γ ⇒ A ∧ FocusedTree (N + 1) Γ A ∧ ∀ m < N + 1, ¬ FocusedTree m Γ A) := by
  intro hforall
  rcases hforall 2 (by exact Nat.AtLeastTwo.prop) with ⟨Γ, A, hdeg, hder, _, hmin⟩
  have hApos : 0 < tp_degree A := by
    cases A <;> simp [tp_degree]
  have hΓpos : 0 < list_degree Γ := by
    rcases List.exists_cons_of_ne_nil (nonempty_premises hder) with ⟨B, Δ, rfl⟩
    have hBpos : 0 < tp_degree B := by
      cases B <;> simp [tp_degree]
    simpa [list_degree] using add_pos_of_pos_of_nonneg hBpos (Nat.zero_le (list_degree Δ))
  have hAone : tp_degree A = 1 := by
    omega
  have hΓone : list_degree Γ = 1 := by
    omega
  cases A with
  | atom s =>
      rcases List.exists_cons_of_ne_nil (nonempty_premises hder) with ⟨B, Δ, hΓcons⟩
      subst Γ
      have hΔnil : Δ = [] := by
        cases Δ with
        | nil => exact Array.toList_empty
        | cons C Θ =>
            exfalso
            have hBpos : 0 < tp_degree B := by
              cases B <;> simp [tp_degree]
            have hTailPos : 0 < list_degree (C :: Θ) := by
              have hCpos : 0 < tp_degree C := by
                cases C <;> simp [tp_degree]
              simpa [list_degree] using add_pos_of_pos_of_nonneg hCpos (Nat.zero_le (list_degree Θ))
            have : tp_degree B + list_degree (C :: Θ) = 1 := by
              simpa [list_degree] using hΓone
            omega
      rw [hΔnil] at hΓone hder hmin
      have hBone : tp_degree B = 1 := by
        simpa [list_degree] using hΓone
      cases B with
      | atom t =>
          have hBt : Tp.atom t = Tp.atom s := by
            exact thm_singleton_atom_iff_eq_000008.mp hder
          have hft1 : FocusedTree 1 [Tp.atom s] (Tp.atom s) := by
            simp [FocusedTree]
          exact (hmin 1 (by exact Nat.one_lt_succ_succ 1)) (by simpa [hBt] using hft1)
      | ldiv B1 B2 =>
          exfalso
          have hBcontra := hBone
          simp [tp_degree] at hBcontra
          have hB1pos : 0 < tp_degree B1 := by
            cases B1 <;> simp [tp_degree]
          omega
      | rdiv B1 B2 =>
          exfalso
          have hBcontra := hBone
          simp [tp_degree] at hBcontra
          have hB1pos : 0 < tp_degree B1 := by
            cases B1 <;> simp [tp_degree]
          omega
  | ldiv A1 A2 =>
      exfalso
      have hAcontra := hAone
      simp [tp_degree] at hAcontra
      have hA1pos : 0 < tp_degree A1 := by
        cases A1 <;> simp [tp_degree]
      omega
  | rdiv A1 A2 =>
      exfalso
      have hAcontra := hAone
      simp [tp_degree] at hAcontra
      have hA1pos : 0 < tp_degree A1 := by
        cases A1 <;> simp [tp_degree]
      omega

def LeftDivisionOnly : Tp → Prop
  | Tp.atom _ => True
  | Tp.ldiv A B => LeftDivisionOnly A ∧ LeftDivisionOnly B
  | Tp.rdiv _ _ => False

def RightDivisionOnly : Tp → Prop
  | Tp.atom _ => True
  | Tp.ldiv _ _ => False
  | Tp.rdiv A B => RightDivisionOnly A ∧ RightDivisionOnly B

abbrev SameDivisionOrientation (A : Tp) : Prop :=
  LeftDivisionOnly A ∨ RightDivisionOnly A

lemma left_only_of_left_tp (A : Left.Tp) : LeftDivisionOnly A.toProductFree := by
  induction A with
  | atom s =>
      trivial
  | ldiv A B ihA ihB =>
      exact ⟨ihA, ihB⟩

lemma right_only_of_right_tp (A : Right.Tp) : RightDivisionOnly A.toProductFree := by
  induction A with
  | atom s =>
      trivial
  | rdiv B A ihB ihA =>
      exact ⟨ihB, ihA⟩

lemma exists_left_tp_of_left_only {A : Tp} (hA : LeftDivisionOnly A) :
    ∃ A' : Left.Tp, A'.toProductFree = A := by
  induction A with
  | atom s => exact ⟨Left.Tp.atom s, rfl⟩
  | ldiv A B ihA ihB =>
      rcases hA with ⟨hA, hB⟩
      rcases ihA hA with ⟨A', rfl⟩
      rcases ihB hB with ⟨B', rfl⟩
      exact ⟨Left.Tp.ldiv A' B', rfl⟩
  | rdiv A B =>
      cases hA

lemma exists_right_tp_of_right_only {A : Tp} (hA : RightDivisionOnly A) :
    ∃ A' : Right.Tp, A'.toProductFree = A := by
  induction A with
  | atom s => exact ⟨Right.Tp.atom s, rfl⟩
  | ldiv A B =>
      cases hA
  | rdiv B A ihB ihA =>
      rcases hA with ⟨hB, hA⟩
      rcases ihB hB with ⟨B', rfl⟩
      rcases ihA hA with ⟨A', rfl⟩
      exact ⟨Right.Tp.rdiv B' A', rfl⟩

lemma exists_left_ctx_of_atomic (Γ : List Tp) (hΓ : AtomicCtx Γ) :
    ∃ Γ' : List Left.Tp, Left.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : is_atom A := hΓ A (by exact List.mem_cons_self)
      have htail : AtomicCtx Γ := by
        intro x hx
        exact List.forall_mem_of_forall_mem_cons hΓ x hx
      rcases ih htail with ⟨Γ', hΓ'⟩
      cases A with
      | atom s =>
          refine ⟨Left.Tp.atom s :: Γ', ?_⟩
          simp [Left.ctxToProductFree]
          exact ⟨rfl, hΓ'⟩
      | ldiv A B =>
          cases hA
      | rdiv A B =>
          cases hA

lemma exists_right_ctx_of_atomic (Γ : List Tp) (hΓ : AtomicCtx Γ) :
    ∃ Γ' : List Right.Tp, Right.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : is_atom A := hΓ A (by exact List.mem_cons_self)
      have htail : AtomicCtx Γ := by
        intro x hx
        exact List.forall_mem_of_forall_mem_cons hΓ x hx
      rcases ih htail with ⟨Γ', hΓ'⟩
      cases A with
      | atom s =>
          refine ⟨Right.Tp.atom s :: Γ', ?_⟩
          simp [Right.ctxToProductFree]
          exact ⟨rfl, hΓ'⟩
      | ldiv A B =>
          cases hA
      | rdiv A B =>
          cases hA

/-- Atomic contexts are one-sided representable exactly for derivable one-sided succedents. -/
theorem thm_atomic_context_one_sided_iff_000035 : ∀ (Γ : List Tp) (A : Tp), AtomicCtx Γ → ((LeftRep Γ A ∨ RightRep Γ A) ↔ (Γ ⇒ A ∧ SameDivisionOrientation A)) := by
  intro Γ A hΓ
  constructor
  · intro hRep
    rcases hRep with hLeft | hRight
    · rcases hLeft with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inl ?_⟩
      · simpa [Left.Sequent, hΓ', hA'] using hseq'
      · simpa [hA'] using left_only_of_left_tp A'
    · rcases hRight with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inr ?_⟩
      · simpa [Right.Sequent, hΓ', hA'] using hseq'
      · simpa [hA'] using right_only_of_right_tp A'
  · rintro ⟨hseq, hOrient⟩
    rcases hOrient with hLeftOnly | hRightOnly
    · left
      rcases exists_left_ctx_of_atomic Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_left_tp_of_left_only hLeftOnly with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Left.Sequent, hΓ', hA'] using hseq
    · right
      rcases exists_right_ctx_of_atomic Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_right_tp_of_right_only hRightOnly with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Right.Sequent, hΓ', hA'] using hseq

lemma exists_left_ctx_of_left_only (Γ : List Tp) (hΓ : ∀ x ∈ Γ, LeftDivisionOnly x) :
    ∃ Γ' : List Left.Tp, Left.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : LeftDivisionOnly A := hΓ A (by exact List.mem_cons_self)
      have htail : ∀ x ∈ Γ, LeftDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hΓ x a
      rcases exists_left_tp_of_left_only hA with ⟨A', hA'⟩
      rcases ih htail with ⟨Γ', hΓ'⟩
      refine ⟨A' :: Γ', ?_⟩
      simpa [Left.ctxToProductFree, hA'] using congrArg (List.cons A'.toProductFree) hΓ'

lemma exists_right_ctx_of_right_only (Γ : List Tp) (hΓ : ∀ x ∈ Γ, RightDivisionOnly x) :
    ∃ Γ' : List Right.Tp, Right.ctxToProductFree Γ' = Γ := by
  induction Γ with
  | nil =>
      exact ⟨[], rfl⟩
  | cons A Γ ih =>
      have hA : RightDivisionOnly A := hΓ A (by exact List.mem_cons_self)
      have htail : ∀ x ∈ Γ, RightDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hΓ x a
      rcases exists_right_tp_of_right_only hA with ⟨A', hA'⟩
      rcases ih htail with ⟨Γ', hΓ'⟩
      refine ⟨A' :: Γ', ?_⟩
      simpa [Right.ctxToProductFree, hA'] using congrArg (List.cons A'.toProductFree) hΓ'

/-- One-sided representability is exactly derivability with a uniform division orientation. -/
theorem thm_uniform_orientation_fragment_iff_000041 : ∀ (Γ : List Tp) (A : Tp), (LeftRep Γ A ∨ RightRep Γ A) ↔ (Γ ⇒ A ∧ ((∀ x ∈ A :: Γ, LeftDivisionOnly x) ∨ (∀ x ∈ A :: Γ, RightDivisionOnly x))) := by
  intro Γ A
  constructor
  · intro hRep
    rcases hRep with hLeft | hRight
    · rcases hLeft with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inl ?_⟩
      · simpa [Left.Sequent, hΓ', hA'] using hseq'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa [hA'] using left_only_of_left_tp A'
        · rw [← hΓ'] at hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact left_only_of_left_tp y
    · rcases hRight with ⟨Γ', A', hΓ', hA', hseq'⟩
      refine ⟨?_, Or.inr ?_⟩
      · simpa [Right.Sequent, hΓ', hA'] using hseq'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa [hA'] using right_only_of_right_tp A'
        · rw [← hΓ'] at hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact right_only_of_right_tp y
  · rintro ⟨hseq, hOrient⟩
    rcases hOrient with hLeftOnly | hRightOnly
    · left
      have hA : LeftDivisionOnly A := hLeftOnly A (by exact List.mem_cons_self)
      have hΓ : ∀ x ∈ Γ, LeftDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hLeftOnly x a
      rcases exists_left_ctx_of_left_only Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_left_tp_of_left_only hA with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Left.Sequent, hΓ', hA'] using hseq
    · right
      have hA : RightDivisionOnly A := hRightOnly A (by exact List.mem_cons_self)
      have hΓ : ∀ x ∈ Γ, RightDivisionOnly x := by
        exact fun x a => List.forall_mem_of_forall_mem_cons hRightOnly x a
      rcases exists_right_ctx_of_right_only Γ hΓ with ⟨Γ', hΓ'⟩
      rcases exists_right_tp_of_right_only hA with ⟨A', hA'⟩
      refine ⟨Γ', A', hΓ', hA', ?_⟩
      simpa [Right.Sequent, hΓ', hA'] using hseq

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

/-- Left-focused trees exactly characterize left-only derivable sequents. -/
theorem thm_left_focused_tree_iff_left_only_000071 : ∀ (Γ : List Tp) (A : Tp), (∃ n : Nat, LeftFocusedTree n Γ A) ↔ ((LeftOnlyNode Γ A) ∧ Γ ⇒ A) := by
  intro Γ A
  constructor
  · rintro ⟨n, hTree⟩
    have hForget :
        ∀ {n : Nat} {Γ : List Tp} {A : Tp},
          LeftFocusedTree n Γ A → LeftOnlyNode Γ A ∧ FocusedTree n Γ A := by
      intro n
      induction n with
      | zero =>
          intro Γ A h
          cases h
      | succ n ih =>
          intro Γ A h
          cases A with
          | atom s =>
              rcases h with ⟨hLeft, hTree⟩
              refine ⟨hLeft, ?_⟩
              rcases hTree with rfl | ⟨c, hc, hcTree⟩
              · exact Or.inl rfl
              · refine Or.inr ⟨c, hc, ?_⟩
                cases c with
                | rdiv L B A Δ Λ =>
                    rcases hcTree with ⟨h1, h2⟩
                    exact ⟨(ih h1).2, (ih h2).2⟩
                | ldiv Γ₁ Δ A B R =>
                    rcases hcTree with ⟨h1, h2⟩
                    exact ⟨(ih h1).2, (ih h2).2⟩
          | ldiv A B =>
              rcases h with ⟨hLeft, hNe, hSub⟩
              exact ⟨hLeft, ⟨hNe, (ih hSub).2⟩⟩
          | rdiv B A =>
              rcases h with ⟨hLeft, hNe, hSub⟩
              exact ⟨hLeft, ⟨hNe, (ih hSub).2⟩⟩
    have hRoot := hForget hTree
    exact ⟨hRoot.1, (thm_sequent_iff_focused_tree_000023 (Γ := Γ) (A := A)).2 ⟨n, hRoot.2⟩⟩
  · exact fun a => thm_left_only_focused_tree_000062 Γ A a

/-- Right-focused trees exactly characterize right-only derivable sequents. -/
theorem thm_right_focused_tree_iff_000075 : ∀ (Γ : List Tp) (A : Tp), (∃ n : Nat, RightFocusedTree n Γ A) ↔ ((RightOnlyNode Γ A) ∧ Γ ⇒ A) := by
  intro Γ A
  constructor
  · rintro ⟨n, htree⟩
    have hforget : ∀ {n : Nat} {Γ : List Tp} {A : Tp}, RightFocusedTree n Γ A → FocusedTree n Γ A := by
      intro n
      induction n with
      | zero =>
          intro Γ A h
          cases h
      | succ n ih =>
          intro Γ A h
          cases A with
          | atom s =>
              rcases h with ⟨_, h'⟩
              rcases h' with rfl | ⟨c, hc, hcTree⟩
              · exact Or.inl rfl
              · rcases c with ⟨L, B, A, Δ, Λ⟩ | ⟨Γ₁, Δ, A, B, R⟩
                · right
                  refine ⟨Cand.rdiv L B A Δ Λ, hc, ?_⟩
                  exact And.imp ih ih hcTree
                · right
                  refine ⟨Cand.ldiv Γ₁ Δ A B R, hc, ?_⟩
                  exact And.imp ih ih hcTree
          | ldiv A B =>
              rcases h with ⟨_, hne, hsub⟩
              exact ⟨hne, ih hsub⟩
          | rdiv B A =>
              rcases h with ⟨_, hne, hsub⟩
              exact ⟨hne, ih hsub⟩
    have hright : RightOnlyNode Γ A := by
      cases n with
      | zero =>
          cases htree
      | succ n =>
          cases A with
          | atom s => exact htree.1
          | ldiv A B => exact htree.1
          | rdiv B A => exact htree.1
    refine ⟨hright, ?_⟩
    exact (thm_sequent_iff_focused_tree_000023 (Γ := Γ) (A := A)).2 ⟨n, hforget htree⟩
  · exact fun a => thm_right_only_focused_tree_000067 Γ A a

/-- Atomic left representability reduces to a singleton case or a left-division decomposition. -/
theorem thm_leftrep_atom_reduction_000072 : ∀ (Γ : List Tp) (s : String), LeftRep Γ (Tp.atom s) ↔ (Γ = [Tp.atom s] ∨ ∃ Pi : List Tp, ∃ Δ : List Tp, ∃ Λ : List Tp, ∃ A : Tp, ∃ B : Tp, Γ = Pi ++ Δ ++ [A ⧹ B] ++ Λ ∧ LeftRep Δ A ∧ LeftRep (Pi ++ [B] ++ Λ) (Tp.atom s)) := by
  intro Γ s
  constructor
  · intro h
    have hExact := (thm_left_oriented_derivation_exact_000058 Γ (Tp.atom s)).mp h
    rcases thm_atom_sequent_decompose_000009 hExact.2 with hAx | hRest
    · exact Or.symm (Or.inr hAx)
    · rcases hRest with ⟨Pi, B, A, Δ, Λ, hEq, hΔSeq, hMainSeq⟩ | ⟨Pi, Δ, A, B, Λ, hEq, hΔSeq, hMainSeq⟩
      · exfalso
        have hBad : LeftDivisionOnly (B ⧸ A) := by
          apply hExact.1
          rw [hEq]
          simp
        cases hBad
      · have hAB : LeftDivisionOnly A ∧ LeftDivisionOnly B := by
          have hSlash : LeftDivisionOnly (A ⧹ B) := by
            apply hExact.1
            rw [hEq]
            simp
          simpa [LeftDivisionOnly] using hSlash
        have hΔLeft : ∀ x ∈ A :: Δ, LeftDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hAB.1
          · apply hExact.1
            rw [hEq]
            simp [hx]
        have hMainLeft : ∀ x ∈ Tp.atom s :: (Pi ++ [B] ++ Λ), LeftDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hExact.1 _ (by exact List.mem_cons_self)
          · have hx' : x ∈ (Pi ++ [B]) ++ Λ := by simpa [List.append_assoc] using hx
            rcases List.mem_append.mp hx' with hxPiB | hxΛ
            · rcases List.mem_append.mp hxPiB with hxPi | hxB
              · exact hExact.1 _ (by rw [hEq]; simp [hxPi])
              · rcases List.mem_singleton.mp hxB with rfl
                exact (id (And.symm hAB)).left
            · exact hExact.1 _ (by rw [hEq]; simp [hxΛ])
        exact Or.inr ⟨Pi, Δ, Λ, A, B, hEq, (thm_left_oriented_derivation_exact_000058 Δ A).2 ⟨hΔLeft, hΔSeq⟩, (thm_left_oriented_derivation_exact_000058 (Pi ++ [B] ++ Λ) (Tp.atom s)).2 ⟨hMainLeft, hMainSeq⟩⟩
  · intro h
    rcases h with rfl | ⟨Pi, Δ, Λ, A, B, hEq, hΔ, hMain⟩
    · apply (thm_left_oriented_derivation_exact_000058 [Tp.atom s] (Tp.atom s)).2
      constructor
      · intro x hx
        simp at hx
        subst hx
        simp [LeftDivisionOnly]
      · exact thm_singleton_atom_iff_eq_000008.mpr rfl
    · have hΔExact := (thm_left_oriented_derivation_exact_000058 Δ A).mp hΔ
      have hMainExact := (thm_left_oriented_derivation_exact_000058 (Pi ++ [B] ++ Λ) (Tp.atom s)).mp hMain
      have hLeft : ∀ x ∈ Tp.atom s :: (Pi ++ Δ ++ [A ⧹ B] ++ Λ), LeftDivisionOnly x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hMainExact.1 _ (by exact List.mem_cons_self)
        · have hx' : x ∈ Pi ∨ x ∈ Δ ∨ x = A ⧹ B ∨ x ∈ Λ := by
            simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hx
          rcases hx' with hxPi | hxΔ | rfl | hxΛ
          · exact hMainExact.1 _ (by simp [hxPi])
          · exact hΔExact.1 _ (by exact List.mem_cons_of_mem A hxΔ)
          · have hA : LeftDivisionOnly A := hΔExact.1 _ (by exact List.mem_cons_self)
            have hB : LeftDivisionOnly B := hMainExact.1 _ (by simp)
            simpa [LeftDivisionOnly] using And.intro hA hB
          · exact hMainExact.1 _ (by simp [hxΛ])
      have hSeq : Pi ++ Δ ++ [A ⧹ B] ++ Λ ⇒ Tp.atom s := by
        simpa [List.append_assoc] using
          (Sequent.ldiv_l (Δ := Δ) (A := A) (Γ := Pi) (B := B) (Λ := Λ) (C := Tp.atom s) hΔExact.2 hMainExact.2)
      simpa [hEq] using (thm_left_oriented_derivation_exact_000058 (Pi ++ Δ ++ [A ⧹ B] ++ Λ) (Tp.atom s)).2 ⟨hLeft, hSeq⟩

/-- RightRep of an atom reduces to the singleton case or one right-division step. -/
theorem thm_rightrep_atom_reduction_000078 : ∀ (Γ : List Tp) (s : String), RightRep Γ (# s) ↔ (Γ = [# s] ∨ ∃ (pi delta lam : List Tp) (A B : Tp), Γ = pi ++ [B ⧸ A] ++ delta ++ lam ∧ RightRep delta A ∧ RightRep (pi ++ [B] ++ lam) (# s)) := by
  intro Γ s
  constructor
  · intro hRight
    have hExact := (thm_right_oriented_derivation_exact_000059 Γ (# s)).mp hRight
    rcases thm_atom_sequent_decompose_000009 (Γ := Γ) (s := s) hExact.2 with hAx | hCases
    · exact Or.symm (Or.inr hAx)
    · rcases hCases with ⟨pi, B, A, delta, lam, hΓ, hDeltaSeq, hMainSeq⟩ | ⟨pi, delta, A, B, lam, hΓ, hDeltaSeq, hMainSeq⟩
      · have hBA : RightDivisionOnly B ∧ RightDivisionOnly A := by
          have hDiv : RightDivisionOnly (B ⧸ A) := by
            exact hExact.1 _ (by simp [hΓ])
          simpa [RightDivisionOnly] using hDiv
        have hDeltaRight : ∀ x ∈ A :: delta, RightDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxDelta
          · exact (id (And.symm hBA)).left
          · exact hExact.1 x (by simp [hΓ, hxDelta])
        have hMainRight : ∀ x ∈ (# s) :: (pi ++ [B] ++ lam), RightDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxMain
          · exact hExact.1 _ (by exact List.mem_cons_self)
          · have hxMain' : x ∈ pi ∨ x = B ∨ x ∈ lam := by
              simpa [List.mem_append, List.mem_singleton, or_assoc] using hxMain
            rcases hxMain' with hxPi | rfl | hxLam
            · exact hExact.1 x (by simp [hΓ, hxPi])
            · exact hBA.left
            · exact hExact.1 x (by simp [hΓ, hxLam])
        refine Or.inr ⟨pi, delta, lam, A, B, hΓ, ?_, ?_⟩
        · exact (thm_uniform_orientation_implies_oriented_derivation_000055 delta A).2 ⟨hDeltaRight, hDeltaSeq⟩
        · exact (thm_uniform_orientation_implies_oriented_derivation_000055 (pi ++ [B] ++ lam) (# s)).2 ⟨hMainRight, hMainSeq⟩
      · have hBad : RightDivisionOnly (A ⧹ B) := by
          exact hExact.1 _ (by simp [hΓ])
        simp [RightDivisionOnly] at hBad
  · rintro (rfl | ⟨pi, delta, lam, A, B, hΓ, hDeltaRight, hMainRight⟩)
    · refine (thm_uniform_orientation_implies_oriented_derivation_000055 [# s] (# s)).2 ?_
      constructor
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [RightDivisionOnly]
        · rcases List.mem_singleton.mp hx with rfl
          simp [RightDivisionOnly]
      · exact thm_singleton_atom_iff_eq_000008.mpr rfl
    · subst hΓ
      have hDeltaExact := (thm_right_oriented_derivation_exact_000059 delta A).mp hDeltaRight
      have hMainExact := (thm_right_oriented_derivation_exact_000059 (pi ++ [B] ++ lam) (# s)).mp hMainRight
      refine (thm_uniform_orientation_implies_oriented_derivation_000055 (pi ++ [B ⧸ A] ++ delta ++ lam) (# s)).2 ?_
      constructor
      · intro x hx
        have hx' : x = # s ∨ x ∈ pi ∨ x = B ⧸ A ∨ x ∈ delta ∨ x ∈ lam := by
          simpa [List.mem_cons, List.mem_append, List.mem_singleton, or_assoc, or_left_comm, or_comm] using hx
        rcases hx' with rfl | hxPi | rfl | hxDelta | hxLam
        · simp [RightDivisionOnly]
        · exact hMainExact.1 x (by simp [hxPi])
        · exact ⟨hMainExact.1 B (by simp), hDeltaExact.1 A (by exact List.mem_cons_self)⟩
        · exact hDeltaExact.1 x (by exact List.mem_cons_of_mem A hxDelta)
        · exact hMainExact.1 x (by simp [hxLam])
      · simpa [List.append_assoc] using
          (Mathling.Lambek.ProductFree.Sequent.rdiv_l
            (Δ := delta) (A := A) (Γ := pi) (B := B) (Λ := lam) (C := # s)
            hDeltaExact.2 hMainExact.2)

/-- RightRep is exactly the image of the pure right calculus. -/
theorem thm_rightrep_pure_right_exact_000080 : ∀ (Γ : List Tp) (A : Tp), RightRep Γ A ↔ ∃ ΓR : List Mathling.Lambek.ProductFree.Right.Tp, ∃ AR : Mathling.Lambek.ProductFree.Right.Tp, Γ = ΓR.map Mathling.Lambek.ProductFree.Right.Tp.toProductFree ∧ A = AR.toProductFree ∧ Mathling.Lambek.ProductFree.Right.Sequent ΓR AR := by
  intro Γ A
  constructor
  · intro h
    rcases h with ⟨ΓR, AR, hΓ, hA, hseq⟩
    refine ⟨ΓR, AR, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Right.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))
  · intro h
    rcases h with ⟨ΓR, AR, hΓ, hA, hseq⟩
    refine ⟨ΓR, AR, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Right.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))

/-- LeftRep is exactly the image of the pure left sequent calculus. -/
theorem thm_leftrep_iff_left_sequent_000086 : ∀ (Γ : List Tp) (A : Tp), LeftRep Γ A ↔ ∃ ΓL : List Mathling.Lambek.ProductFree.Left.Tp, ∃ AL : Mathling.Lambek.ProductFree.Left.Tp, Γ = ΓL.map Mathling.Lambek.ProductFree.Left.Tp.toProductFree ∧ A = AL.toProductFree ∧ Mathling.Lambek.ProductFree.Left.Sequent ΓL AL := by
  intro Γ A
  constructor
  · intro h
    rcases h with ⟨ΓL, AL, hΓ, hA, hseq⟩
    refine ⟨ΓL, AL, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Left.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))
  · intro h
    rcases h with ⟨ΓL, AL, hΓ, hA, hseq⟩
    refine ⟨ΓL, AL, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Left.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))

end AutomatedTheoryConstruction
