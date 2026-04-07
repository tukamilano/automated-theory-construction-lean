import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace Mathling.Lambek.ProductFree

@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : Tp)      : Tp
  | rdiv (A B : Tp)      : Tp
  deriving Repr, DecidableEq

prefix:65 "#" => Tp.atom
infixr:60 " ⧹ " => Tp.ldiv
infixl:60 " ⧸ " => Tp.rdiv

@[grind intro]
inductive Sequent : List Tp → Tp → Prop where
  | ax : Sequent [A] A
  | rdiv_r :
      Γ ≠ [] →
      Sequent (Γ ++ [A]) B →
      Sequent Γ (B ⧸ A)
  | ldiv_r :
      Γ ≠ [] →
      Sequent ([A] ++ Γ) B →
      Sequent Γ (A ⧹ B)
  | rdiv_l :
      Sequent Δ A →
      Sequent (Γ ++ [B] ++ Λ) C →
      Sequent (Γ ++ [B ⧸ A] ++ Δ ++ Λ) C
  | ldiv_l :
      Sequent Δ A →
      Sequent (Γ ++ [B] ++ Λ) C →
      Sequent (Γ ++ Δ ++ [A ⧹ B] ++ Λ) C

infixl:50 " ⇒ " => Sequent

@[grind =]
def tp_degree : Tp → Nat
  | # _     => 1
  | A ⧹ B   => tp_degree A + tp_degree B + 1
  | A ⧸ B   => tp_degree A + tp_degree B + 1

@[grind =]
def list_degree : List Tp → Nat
  | []        => 0
  | A :: Γ    => tp_degree A + list_degree Γ

@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind

@[grind =>]
lemma nonempty_premises (h : Γ ⇒ A) : Γ ≠ [] := by
  induction h <;> grind [List.append_eq_nil_iff]

@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  grind only [List.append_eq_nil_iff]

lemma list_split_2_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  rcases List.append_eq_append_iff.mp h with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · simp [List.cons_eq_append_iff] at hm
    grind
  · grind

lemma list_split_3_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃) ∨
  (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_2_cases h1.symm with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind

lemma list_split_4_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃ ++ Δ₄) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R ++ Δ₄)
  ∨ (∃ L R, Δ₄ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ Δ₃ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_3_cases (by simpa using h1.symm)
    with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind

set_option maxHeartbeats 1000000 in
-- The nested case split in `cut_admissible` needs a higher local heartbeat budget.
@[grind =>]
theorem cut_admissible
  (d_left : Γ ⇒ A)
  (d_right : Δ ++ [A] ++ Λ ⇒ B) :
  Δ ++ Γ ++ Λ ⇒ B := by
    let deg := list_degree (Δ ++ Γ ++ Λ) + tp_degree A + tp_degree B
    generalize h_n : deg = n
    induction n using Nat.strong_induction_on generalizing Γ Δ Λ A B
    next n ih =>
      subst h_n
      cases d_left with
      | ax => exact ((fun a => d_right) ∘ fun a => A) A
      | ldiv_r h_ne_L d_inner_L =>
        rename_i A₁ A₂
        have h_der_A : Γ ⇒ A₁ ⧹ A₂ := Sequent.ldiv_r h_ne_L d_inner_L
        generalize d_right_eq_x : Δ ++ [A₁ ⧹ A₂] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax =>
          grind only [List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Sequent.ldiv_r]
        | ldiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree ([C] ++ Δ ++ Γ ++ Λ) + tp_degree (A₁ ⧹ A₂) + tp_degree D
          have h_deg_lt : m < deg := by grind only [usr List.append_assoc, = List.cons_append, = list_degree_traversible, tp_degree, list_degree]
          have d_permuted_inner : [C] ++ Δ ++ [ A₁ ⧹ A₂ ] ++ Λ ⇒ D := by grind only
          have d_cut_result : [C] ++ Δ ++ Γ ++ Λ ⇒ D := Function.const
              (List Tp)
              (ih m h_deg_lt h_der_A d_permuted_inner rfl)
              Γ
          grind only [=> nonempty_premises, => nonempty_append, Sequent.ldiv_r]
        | rdiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree (Δ ++ Γ ++ Λ ++ [C]) + tp_degree (A₁ ⧹ A₂) + tp_degree D
          have h_deg_lt : m < deg := by grind only [= list_degree_traversible, list_degree, tp_degree]
          have d_permuted_inner : Δ ++ [ A₁ ⧹ A₂ ] ++ Λ ++ [C] ⇒ D := by grind only
          have d_cut_result : Δ ++ Γ ++ Λ ++ [C] ⇒ D := by grind only [usr List.append_assoc, = list_degree_traversible, list_degree, tp_degree]
          grind only [=> nonempty_premises, => nonempty_append, Sequent.rdiv_r]
        | ldiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, h_princ, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R))
                   + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by grind only [usr List.append_assoc, = list_degree_traversible, list_degree, = List.cons_append, tp_degree]
            have d_cut_main : Δ ++ Γ ++ R ++ [B_res] ++ Γ_R ⇒ B := by grind
            have d_reconstructed :
                Δ ++ Γ ++ R ++ Δ_arg ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B :=
              Sequent.ldiv_l d_arg d_cut_main
            grind only
          · let m := list_degree (L ++ Γ ++ R) + tp_degree A_arg + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by grind
            have d_reconstructed :
                Γ_L ++ (L ++ Γ ++ R) ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B :=
              Sequent.ldiv_l d_cut_arg d_main
            grind only
          · have h_eq_decomp :
                [A_arg ⧹ B_res] = L ++ [A₁ ⧹ A₂] ++ R →
                  L = [] ∧ R = [] ∧ A_arg = A₁ ∧ B_res = A₂ := by
              grind [List.singleton_eq_append_iff]
            have h_decomp : L = [] ∧ R = [] ∧ A_arg = A₁ ∧ B_res = A₂ := by
              exact And.symm ((fun {a b} => And.comm.mp) (h_eq_decomp h_princ))
            let m1 := list_degree (Γ_L ++ ([A₁] ++ Γ) ++ Γ_R) + tp_degree A₂ + tp_degree B
            have h_deg_lt_princ : m1 < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_reduced : Γ_L ++ Δ_arg ++ Γ ++ Γ_R ⇒ B := by grind
            grind only
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ Δ_arg ++ [A_arg ⧹ B_res] ++ (L ++ Γ ++ Λ) ⇒ B := by grind
            grind only
        | rdiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, h, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ R ++ [B_res] ++ Γ_R) + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R) ⇒ B := by grind
            have d_reconstructed : (Δ ++ Γ ++ R) ++ [B_res ⧸ A_arg] ++ Δ_arg ++ Γ_R ⇒ B := by grind
            grind only
          · grind [List.singleton_eq_append_iff]
          · let m := list_degree (L ++ Γ ++ R) + tp_degree (A₁ ⧹ A₂) + tp_degree A_arg
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by
              exact Function.const (List Tp) (ih m h_deg_lt h_der_A d_arg rfl) Γ
            have d_reconstructed :
                Γ_L ++ [B_res ⧸ A_arg] ++ (L ++ Γ ++ R) ++ Γ_R ⇒ B :=
              Sequent.rdiv_l (ih m h_deg_lt h_der_A d_arg rfl) d_main
            grind only
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ [A₁ ⧹ A₂] ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by
              exact Function.const
                (List Tp)
                (ih m h_deg_lt h_der_A d_cut_main rfl)
                Γ
            grind
      | rdiv_r h_ne_L d_inner_L =>
        rename_i A₁ A₂
        have h_der_A : Γ ⇒ A₂ ⧸ A₁ := Sequent.rdiv_r h_ne_L d_inner_L
        generalize d_right_eq_x : Δ ++ [A₂ ⧸ A₁] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax => grind only [nonempty_append, List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Sequent.rdiv_r]
        | ldiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree ([C] ++ Δ ++ Γ ++ Λ) + tp_degree (A₂ ⧸ A₁) + tp_degree D
          have h_deg_lt : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have d_permuted_inner : [C] ++ Δ ++ [ A₂ ⧸ A₁ ] ++ Λ ⇒ D := by grind
          have d_cut_result : [C] ++ Δ ++ Γ ++ Λ ⇒ D := by
            exact Function.const
              (List Tp)
              (ih m h_deg_lt h_der_A d_permuted_inner rfl)
              Γ
          grind
        | rdiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree (Δ ++ Γ ++ Λ ++ [C]) + tp_degree ( A₂ ⧸ A₁ ) + tp_degree D
          have h_deg_lt : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have d_permuted_inner : Δ ++ [ A₂ ⧸ A₁ ] ++ Λ ++ [C] ⇒ D := by grind
          have d_cut_result : Δ ++ Γ ++ Λ ++ [C] ⇒ D := by grind
          grind
        | ldiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, h_contra, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R))
                   + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Δ ++ Γ ++ R ++ [B_res] ++ Γ_R ⇒ B := by grind
            have d_reconstructed :
                Δ ++ Γ ++ R ++ Δ_arg ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B :=
              Sequent.ldiv_l d_arg d_cut_main
            grind
          · let m := list_degree (L ++ Γ ++ R) + tp_degree A_arg + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by grind
            have d_reconstructed :
                Γ_L ++ (L ++ Γ ++ R) ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B :=
              Sequent.ldiv_l d_cut_arg d_main
            grind
          · grind [List.singleton_eq_append_iff]
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ Δ_arg ++ [A_arg ⧹ B_res] ++ (L ++ Γ ++ Λ) ⇒ B := by grind
            grind
        | rdiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, h, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ R ++ [B_res] ++ Γ_R) + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R) ⇒ B := by grind
            have d_reconstructed : (Δ ++ Γ ++ R) ++ [B_res ⧸ A_arg] ++ Δ_arg ++ Γ_R ⇒ B := by grind
            grind
          · have h_eq_decomp :
                [B_res ⧸ A_arg] = L ++ [A₂ ⧸ A₁] ++ R →
                  L = [] ∧ R = [] ∧ B_res = A₂ ∧ A_arg = A₁ := by
              grind [List.singleton_eq_append_iff]
            have h_decomp : L = [] ∧ R = [] ∧ B_res = A₂ ∧ A_arg = A₁ := by
              exact And.symm ((fun {a b} => And.comm.mp) (h_eq_decomp h))
            let m1 := list_degree (Γ_L ++ (Γ ++ [A₁]) ++ Γ_R) + tp_degree A₂ + tp_degree B
            have h_deg_lt_princ : m1 < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_reduced : (Γ_L ++ Γ) ++ Δ_arg ++ Γ_R ⇒ B := by grind
            grind
          · let m := list_degree (L ++ Γ ++ R) + tp_degree (A₂ ⧸ A₁) + tp_degree A_arg
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by
              exact Function.const (List Tp) (ih m h_deg_lt h_der_A d_arg rfl) Γ
            have d_reconstructed :
                Γ_L ++ [B_res ⧸ A_arg] ++ (L ++ Γ ++ R) ++ Γ_R ⇒ B :=
              Sequent.rdiv_l (ih m h_deg_lt h_der_A d_arg rfl) d_main
            grind
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ [A₂ ⧸ A₁] ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by
              exact Function.const
                (List Tp)
                (ih m h_deg_lt h_der_A d_cut_main rfl)
                Γ
            grind
      | rdiv_l d_arg d_main =>
        rename_i Γ_L Γ_R  Δ_arg A_arg B_res
        let m := list_degree (Δ ++ (Δ_arg ++ [A_arg] ++ B_res) ++ Λ) + tp_degree A + tp_degree B
        have h_deg_lt : m < deg := by grind
        have d_restored_context : Δ ++ Δ_arg ++ [A_arg] ++ B_res ++ Λ ⇒ B := by grind
        have d_final : Δ ++ Δ_arg ++ [A_arg ⧸ Γ_R] ++ Γ_L ++ B_res ++ Λ ⇒ B := by grind
        grind
      | ldiv_l d_arg d_main =>
        rename_i Γ_L Γ_R Δ_arg A_arg B_res
        let m := list_degree (Δ ++ (Δ_arg ++ [A_arg] ++ B_res) ++ Λ) + tp_degree A + tp_degree B
        have h_deg_lt : m < deg := by grind
        have d_restored_context : Δ ++ Δ_arg ++ [A_arg] ++ B_res ++ Λ ⇒ B := by grind
        have d_final : Δ ++ Δ_arg ++ Γ_L ++ [Γ_R ⧹ A_arg] ++ B_res ++ Λ ⇒ B := by grind
        grind

@[grind =>]
theorem ldiv_invertible {Γ : List Tp} {A B : Tp} (h : Γ ⇒ (A ⧹ B)) :
  [A] ++ Γ ⇒ B := by
    have a : [A] ⇒ A := Sequent.ax
    have b : [B] ⇒ B := Sequent.ax
    have c : [] ++ [A] ++ [A ⧹ B] ++ [] ⇒ B := by grind
    grind

@[grind =>]
theorem rdiv_invertible {Γ : List Tp} {A B : Tp} (h : Γ ⇒ (B ⧸ A)) :
  Γ ++ [A] ⇒ B := by
    have a : [A] ⇒ A := Sequent.ax
    have b : [B] ⇒ B := Sequent.ax
    have c : [] ++ [B ⧸ A] ++ ([A] ++ []) ⇒ B := by grind
    grind

@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _   => False

@[grind =>]
theorem atom_generation
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Γ ⇒ Tp.atom s) :
    Γ = [Tp.atom s] := by
  cases h_der with
  | ax =>
      exact List.singleton_inj.mpr rfl
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      have hbad : is_atom (B ⧸ A) := by grind
      grind
  | ldiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      have hbad : is_atom (A ⧹ B) := by grind
      grind

def translatedTpDegree (toProductFree : α → Tp) (A : α) : Nat :=
  tp_degree (toProductFree A)

def translatedListDegree (toProductFree : α → Tp) (Γ : List α) : Nat :=
  list_degree (Γ.map toProductFree)

lemma translatedListDegree_traversible (toProductFree : α → Tp) :
    translatedListDegree toProductFree (Γ ++ Δ) =
      translatedListDegree toProductFree Γ + translatedListDegree toProductFree Δ := by
  simp [translatedListDegree, list_degree_traversible]

def translatedIsAtom (toProductFree : α → Tp) (A : α) : Prop :=
  is_atom (toProductFree A)

lemma translatedNonemptyAppend (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  exact nonempty_append h

end Mathling.Lambek.ProductFree
