import example.Lambek.Basic

namespace Mathling.Lambek.ProductFree.Left

@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : Tp) : Tp
  deriving Repr, DecidableEq

local prefix:65 "☉" => Tp.atom

local infixr:60 " ⧹ " => Tp.ldiv

def Tp.toProductFree : Tp → _root_.Mathling.Lambek.ProductFree.Tp
  | .atom name => _root_.Mathling.Lambek.ProductFree.Tp.atom name
  | .ldiv A B => _root_.Mathling.Lambek.ProductFree.Tp.ldiv A.toProductFree B.toProductFree

@[grind =]
def tp_degree (A : Tp) : Nat :=
  _root_.Mathling.Lambek.ProductFree.translatedTpDegree Tp.toProductFree A

@[grind =]
def list_degree (Γ : List Tp) : Nat :=
  _root_.Mathling.Lambek.ProductFree.translatedListDegree Tp.toProductFree Γ

@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  simpa [list_degree] using
    (_root_.Mathling.Lambek.ProductFree.translatedListDegree_traversible Tp.toProductFree
      (Γ := Γ) (Δ := Δ))

def ctxToProductFree : List Tp → List _root_.Mathling.Lambek.ProductFree.Tp :=
  List.map Tp.toProductFree

@[simp] lemma ctxToProductFree_nil : ctxToProductFree [] = [] := rfl

@[simp] lemma ctxToProductFree_cons :
    ctxToProductFree (A :: Γ) = A.toProductFree :: ctxToProductFree Γ := rfl

@[simp] lemma ctxToProductFree_append :
    ctxToProductFree (Γ ++ Δ) = ctxToProductFree Γ ++ ctxToProductFree Δ := by
  simp [ctxToProductFree]

def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  _root_.Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree

namespace Sequent

theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.ax :
      _root_.Mathling.Lambek.ProductFree.Sequent [A.toProductFree] A.toProductFree)

theorem ldiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent ([A] ++ Γ) B) :
  Sequent Γ (A ⧹ B) := by
  have h_ne_pf : ctxToProductFree Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        ([A.toProductFree] ++ ctxToProductFree Γ)
        B.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.ldiv_r
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      (B := B.toProductFree)
      h_ne_pf h_pf)

theorem ldiv_l
  (h_arg : Sequent Δ A)
  (h_main : Sequent (Γ ++ [B] ++ Λ) C) :
  Sequent (Γ ++ Δ ++ [A ⧹ B] ++ Λ) C := by
  have h_main_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [B.toProductFree] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.ldiv_l
      (Δ := ctxToProductFree Δ)
      (A := A.toProductFree)
      (Γ := ctxToProductFree Γ)
      (B := B.toProductFree)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)

end Sequent

infixl:50 " ⇒ " => Sequent

@[grind =>]
lemma nonempty_premises (h : _root_.Mathling.Lambek.ProductFree.Left.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToProductFree] using
        (_root_.Mathling.Lambek.ProductFree.nonempty_premises h)
  | cons head tail => exact List.cons_ne_nil head tail

@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  exact ProductFree.nonempty_append h

theorem cut_admissible
  {Γ Δ Λ : List Tp} {A B : Tp}
  (d_left : _root_.Mathling.Lambek.ProductFree.Left.Sequent Γ A)
  (d_right : _root_.Mathling.Lambek.ProductFree.Left.Sequent (Δ ++ [A] ++ Λ) B) :
  _root_.Mathling.Lambek.ProductFree.Left.Sequent (Δ ++ Γ ++ Λ) B := by
  have d_left_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using d_left
  have d_right_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Δ ++ [A.toProductFree] ++ ctxToProductFree Λ) B.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using d_right
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (_root_.Mathling.Lambek.ProductFree.cut_admissible d_left_pf d_right_pf)

theorem ldiv_invertible {Γ : List Tp} {A B : Tp}
  (h : _root_.Mathling.Lambek.ProductFree.Left.Sequent Γ (A ⧹ B)) :
  _root_.Mathling.Lambek.ProductFree.Left.Sequent ([A] ++ Γ) B := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.ldiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      (B := B.toProductFree)
      h)

@[grind]
def is_atom (A : Tp) : Prop :=
  _root_.Mathling.Lambek.ProductFree.translatedIsAtom Tp.toProductFree A

theorem atom_generation {Γ : List Tp} {s : String}
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : _root_.Mathling.Lambek.ProductFree.Left.Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_pf :
      ∀ x ∈ ctxToProductFree Γ, _root_.Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    cases y with
    | atom name =>
        simp [Tp.toProductFree, _root_.Mathling.Lambek.ProductFree.is_atom]
    | ldiv A B =>
        have : False := by simpa [is_atom] using h_ctx _ hy
        exact False.elim this
  have h_pf :
      ctxToProductFree Γ = [_root_.Mathling.Lambek.ProductFree.Tp.atom s] := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
      (_root_.Mathling.Lambek.ProductFree.atom_generation h_ctx_pf h_der)
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

end Mathling.Lambek.ProductFree.Left
