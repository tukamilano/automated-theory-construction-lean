    import Mathlib.Data.List.Basic
    import Mathlib.Data.Nat.Basic
    import Mathling.Lambek.ProductFree.Basic
    import LiterateLean

# Right Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の right 断片を定義する。
right 断片では右除法だけを許し、基本的なメタ理論は
`Mathling.Lambek.ProductFree.Basic` への翻訳で再利用する。

まず right 断片の名前空間を開く。

```lean
namespace Mathling.Lambek.ProductFree.Right
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

まず、right 断片の論理式を定義する。

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | rdiv (B A : Tp) : Tp
  deriving Repr, DecidableEq
```

原子式の記法を導入する。

```lean
prefix:65 "#" => Tp.atom
```

右除法の記法を導入する。

```lean
infixl:60 " ⧸ " => Tp.rdiv
```

各 right 論理式を一般の product-free 論理式へ写す。

```lean
def Tp.toProductFree : Tp → _root_.Mathling.Lambek.ProductFree.Tp
  | .atom name => _root_.Mathling.Lambek.ProductFree.Tp.atom name
  | .rdiv B A => _root_.Mathling.Lambek.ProductFree.Tp.rdiv B.toProductFree A.toProductFree
```

論理式ひとつの次数は一般断片の次数を通じて定義する。

```lean
@[grind =]
def tp_degree (A : Tp) : Nat :=
  _root_.Mathling.Lambek.ProductFree.translatedTpDegree Tp.toProductFree A
```

文脈全体の次数も一般断片側の定義を再利用する。

```lean
@[grind =]
def list_degree (Γ : List Tp) : Nat :=
  _root_.Mathling.Lambek.ProductFree.translatedListDegree Tp.toProductFree Γ
```

連結に対する加法性も一般断片側から従う。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  simpa [list_degree] using
    (_root_.Mathling.Lambek.ProductFree.translatedListDegree_traversible Tp.toProductFree
      (Γ := Γ) (Δ := Δ))
```

文脈も同じ写像で翻訳する。

```lean
def ctxToProductFree : List Tp → List _root_.Mathling.Lambek.ProductFree.Tp :=
  List.map Tp.toProductFree
```

空文脈の翻訳は自明である。

```lean
@[simp] lemma ctxToProductFree_nil : ctxToProductFree [] = [] := rfl
```

先頭要素を付けた文脈の翻訳も簡約できる。

```lean
@[simp] lemma ctxToProductFree_cons :
    ctxToProductFree (A :: Γ) = A.toProductFree :: ctxToProductFree Γ := rfl
```

連結についても翻訳が分配される。

```lean
@[simp] lemma ctxToProductFree_append :
    ctxToProductFree (Γ ++ Δ) = ctxToProductFree Γ ++ ctxToProductFree Δ := by
  simp [ctxToProductFree]
```

right シーケントは一般断片のシーケントとして実装する。

```lean
def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  _root_.Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree
```

以下では right 規則をまとめる名前空間を開く。

```lean
namespace Sequent
```

公理規則は翻訳先の公理そのものである。

```lean
theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.ax :
      _root_.Mathling.Lambek.ProductFree.Sequent [A.toProductFree] A.toProductFree)
```

右除法の右規則は一般断片側の定理を持ち上げる。

```lean
theorem rdiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent (Γ ++ [A]) B) :
  Sequent Γ (B ⧸ A) := by
  have h_ne_pf : ctxToProductFree Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [A.toProductFree])
        B.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.rdiv_r
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      (B := B.toProductFree)
      h_ne_pf h_pf)
```

右除法の左規則も翻訳先からそのまま再利用する。

```lean
theorem rdiv_l
  (h_arg : Sequent Δ A)
  (h_main : Sequent (Γ ++ [B] ++ Λ) C) :
  Sequent (Γ ++ [B ⧸ A] ++ Δ ++ Λ) C := by
  have h_main_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [B.toProductFree] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.rdiv_l
      (Δ := ctxToProductFree Δ)
      (A := A.toProductFree)
      (Γ := ctxToProductFree Γ)
      (B := B.toProductFree)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)
```

規則定義の名前空間をここで閉じる。

```lean
end Sequent
```

読みやすさのため right 断片側の記法を与える。

```lean
infixl:50 " ⇒ " => Sequent
```

導出可能なシーケントは空文脈を持たない。

```lean
@[grind =>]
lemma nonempty_premises (h : _root_.Mathling.Lambek.ProductFree.Right.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToProductFree] using
        (_root_.Mathling.Lambek.ProductFree.nonempty_premises h)
  | cons => simp
```

非空文脈を含む連結もやはり非空である。

```lean
@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  exact _root_.Mathling.Lambek.ProductFree.translatedNonemptyAppend h
```

カット許容性は一般断片での結果を翻訳して得る。

```lean
theorem cut_admissible
  {Γ Δ Λ : List Tp} {A B : Tp}
  (d_left : _root_.Mathling.Lambek.ProductFree.Right.Sequent Γ A)
  (d_right : _root_.Mathling.Lambek.ProductFree.Right.Sequent (Δ ++ [A] ++ Λ) B) :
  _root_.Mathling.Lambek.ProductFree.Right.Sequent (Δ ++ Γ ++ Λ) B := by
  have d_left_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using d_left
  have d_right_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Δ ++ [A.toProductFree] ++ ctxToProductFree Λ) B.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using d_right
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (_root_.Mathling.Lambek.ProductFree.cut_admissible d_left_pf d_right_pf)
```

右除法右導入の逆転可能性を再輸出する。

```lean
theorem rdiv_invertible {Γ : List Tp} {A B : Tp}
  (h : _root_.Mathling.Lambek.ProductFree.Right.Sequent Γ (B ⧸ A)) :
  _root_.Mathling.Lambek.ProductFree.Right.Sequent (Γ ++ [A]) B := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.rdiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      (B := B.toProductFree)
      h)
```

原子式だけを見分ける述語を定義する。

```lean
@[grind]
def is_atom (A : Tp) : Prop :=
  _root_.Mathling.Lambek.ProductFree.translatedIsAtom Tp.toProductFree A
```

原子式だけの文脈では導出は公理の形に限られる。

```lean
theorem atom_generation {Γ : List Tp} {s : String}
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : _root_.Mathling.Lambek.ProductFree.Right.Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_pf :
      ∀ x ∈ ctxToProductFree Γ, _root_.Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    cases y with
    | atom name =>
        simp [Tp.toProductFree, _root_.Mathling.Lambek.ProductFree.is_atom]
    | rdiv B A =>
        have : False := by simpa [is_atom] using h_ctx _ hy
        contradiction
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
      | rdiv B A =>
          simp [ctxToProductFree, Tp.toProductFree] at h_pf
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Right
```

<!-- vim: set filetype=markdown : -->
