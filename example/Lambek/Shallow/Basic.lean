import example.Lambek.Basic

namespace Mathling.Lambek.ProductFree.Shallow

@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : String)  : Tp
  | rdiv (B A : String)  : Tp
  deriving Repr, DecidableEq

local prefix:65 "#" => Tp.atom

local infixr:60 " ⧹ " => Tp.ldiv

local infixl:60 " ⧸ " => Tp.rdiv

@[grind =]
def tp_degree : Tp → Nat
  | Tp.atom _ => 1
  | Tp.ldiv _ _ => 3
  | Tp.rdiv _ _ => 3

@[grind =]
def list_degree : List Tp → Nat
  | [] => 0
  | A :: Γ => tp_degree A + list_degree Γ

@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind

def Tp.toProductFree : Tp → Mathling.Lambek.ProductFree.Tp
  | .atom name => Mathling.Lambek.ProductFree.Tp.atom name
  | .ldiv A B =>
      Mathling.Lambek.ProductFree.Tp.ldiv
        (Mathling.Lambek.ProductFree.Tp.atom A)
        (Mathling.Lambek.ProductFree.Tp.atom B)
  | .rdiv B A =>
      Mathling.Lambek.ProductFree.Tp.rdiv
        (Mathling.Lambek.ProductFree.Tp.atom B)
        (Mathling.Lambek.ProductFree.Tp.atom A)

def ctxToProductFree : List Tp → List Mathling.Lambek.ProductFree.Tp :=
  List.map Tp.toProductFree

@[simp] lemma ctxToProductFree_nil :
    ctxToProductFree [] = [] := rfl

@[simp] lemma ctxToProductFree_cons :
    ctxToProductFree (A :: Γ) = A.toProductFree :: ctxToProductFree Γ := rfl

@[simp] lemma ctxToProductFree_append :
    ctxToProductFree (Γ ++ Δ) = ctxToProductFree Γ ++ ctxToProductFree Δ := by
  simp [ctxToProductFree]

def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree

namespace Sequent

theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ax :
      Mathling.Lambek.ProductFree.Sequent [A.toProductFree] A.toProductFree)

theorem ldiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent ([Tp.atom A] ++ Γ) (Tp.atom B)) :
  Sequent Γ (Tp.ldiv A B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_r
      (by simpa using h_ne) h)

theorem rdiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent (Γ ++ [Tp.atom A]) (Tp.atom B)) :
  Sequent Γ (Tp.rdiv B A) := by
  have h_ne_pf : ctxToProductFree Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [Mathling.Lambek.ProductFree.Tp.atom A])
        (Mathling.Lambek.ProductFree.Tp.atom B) := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.rdiv_r
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h_ne_pf
      h_pf)

theorem ldiv_l
  (h_arg : Sequent Δ (Tp.atom A))
  (h_main : Sequent (Γ ++ [Tp.atom B] ++ Λ) C) :
  Sequent (Γ ++ Δ ++ [Tp.ldiv A B] ++ Λ) C := by
  have h_main_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [Mathling.Lambek.ProductFree.Tp.atom B] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_l
      (Δ := ctxToProductFree Δ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (Γ := ctxToProductFree Γ)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)

theorem rdiv_l
  (h_arg : Sequent Δ (Tp.atom A))
  (h_main : Sequent (Γ ++ [Tp.atom B] ++ Λ) C) :
  Sequent (Γ ++ [Tp.rdiv B A] ++ Δ ++ Λ) C := by
  have h_main_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [Mathling.Lambek.ProductFree.Tp.atom B] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (Mathling.Lambek.ProductFree.Sequent.rdiv_l
      (Δ := ctxToProductFree Δ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (Γ := ctxToProductFree Γ)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)

end Sequent

infixl:50 " ⇒ " => Sequent

@[grind =>]
lemma nonempty_premises
  (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToProductFree] using
        (Mathling.Lambek.ProductFree.nonempty_premises h)
  | cons head tail => exact List.cons_ne_nil head tail

@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  exact ProductFree.nonempty_append h

@[grind =>]
theorem cut_admissible
  (d_left : Mathling.Lambek.ProductFree.Shallow.Sequent Γ A)
  (d_right : Mathling.Lambek.ProductFree.Shallow.Sequent (Δ ++ [A] ++ Λ) B) :
  Mathling.Lambek.ProductFree.Shallow.Sequent (Δ ++ Γ ++ Λ) B := by
  have d_left_pf :
      Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using d_left
  have d_right_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Δ ++ [A.toProductFree] ++ ctxToProductFree Λ) B.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using d_right
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (Mathling.Lambek.ProductFree.cut_admissible d_left_pf d_right_pf)

theorem ldiv_invertible {Γ : List Tp} {A B : String}
  (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ (Tp.ldiv A B)) :
  Mathling.Lambek.ProductFree.Shallow.Sequent ([Tp.atom A] ++ Γ) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.ldiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h)

theorem rdiv_invertible {Γ : List Tp} {A B : String}
  (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ (Tp.rdiv B A)) :
  Mathling.Lambek.ProductFree.Shallow.Sequent (Γ ++ [Tp.atom A]) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.rdiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h)

@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _ => False

theorem atom_generation
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Mathling.Lambek.ProductFree.Shallow.Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_pf :
      ∀ x ∈ ctxToProductFree Γ, Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    cases y with
    | atom name =>
        simp [Tp.toProductFree, Mathling.Lambek.ProductFree.is_atom]
    | ldiv A B =>
        have : False := by simpa [is_atom] using h_ctx _ hy
        exact False.elim this
    | rdiv B A =>
        have : False := by simpa [is_atom] using h_ctx _ hy
        exact False.elim this
  have h_pf :
      ctxToProductFree Γ = [Mathling.Lambek.ProductFree.Tp.atom s] := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
      (Mathling.Lambek.ProductFree.atom_generation h_ctx_pf h_der)
  cases Γ with
  | nil =>
      simp [ctxToProductFree] at h_pf
  | cons x xs =>
      cases x with
      | atom name =>
          cases xs with
          | nil =>
              simpa [ctxToProductFree, Tp.toProductFree] using h_pf
          | cons y ys =>
              simp [ctxToProductFree] at h_pf
      | ldiv A B =>
          simp [ctxToProductFree, Tp.toProductFree] at h_pf
      | rdiv B A =>
          simp [ctxToProductFree, Tp.toProductFree] at h_pf

end Mathling.Lambek.ProductFree.Shallow
