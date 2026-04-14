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

end AutomatedTheoryConstruction
