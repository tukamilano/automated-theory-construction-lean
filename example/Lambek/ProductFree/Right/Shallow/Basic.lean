    import Mathlib.Data.List.Basic
    import Mathlib.Data.Nat.Basic
import Mathling.Lambek.ProductFree.Basic
    import LiterateLean

# Right-Shallow Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の right-shallow 断片を定義する。
right-shallow 断片では、右除法の分母は原子式に限定される。

基本的なメタ理論は `_root_.Mathling.Lambek.ProductFree.Basic` に翻訳して再利用する。

```lean
namespace Mathling.Lambek.ProductFree.Right.Shallow
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

まず、right-shallow 断片の論理式を定義する。

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | rdiv (B : String) (A : String) : Tp
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

各 shallow 論理式を一般の product-free 論理式へ直接写す。

```lean
def Tp.toProductFree : Tp → _root_.Mathling.Lambek.ProductFree.Tp
  | .atom name => _root_.Mathling.Lambek.ProductFree.Tp.atom name
  | .rdiv B A =>
      _root_.Mathling.Lambek.ProductFree.Tp.rdiv
        (_root_.Mathling.Lambek.ProductFree.Tp.atom B)
        (_root_.Mathling.Lambek.ProductFree.Tp.atom A)
```

次数は一般断片の次数を通じて定義する。

```lean
@[grind =]
def tp_degree (A : Tp) : Nat :=
  _root_.Mathling.Lambek.ProductFree.translatedTpDegree Tp.toProductFree A
```

文脈の次数も一般断片側の定義を再利用する。

```lean
@[grind =]
def list_degree (Γ : List Tp) : Nat :=
  _root_.Mathling.Lambek.ProductFree.translatedListDegree Tp.toProductFree Γ
```

連結に対する加法性も一般断片から従う。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  simpa [list_degree] using
    (_root_.Mathling.Lambek.ProductFree.translatedListDegree_traversible Tp.toProductFree
      (Γ := Γ) (Δ := Δ))
```

## 一般断片への翻訳

right-shallow の定理は一般の product-free 断片への翻訳から得る。

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

shallow シーケントは一般断片のシーケントとして実装する。

```lean
def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  _root_.Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree
```

## shallow 規則

以下では shallow 規則をまとめる名前空間を開く。

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

右導入規則は right 断片側の定理を持ち上げる。

```lean
theorem rdiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent (Γ ++ [Tp.atom A]) (Tp.atom B)) :
  Sequent Γ (Tp.rdiv B A) := by
  have h_ne_pf : ctxToProductFree Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [_root_.Mathling.Lambek.ProductFree.Tp.atom A])
        (_root_.Mathling.Lambek.ProductFree.Tp.atom B) := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.rdiv_r
      (Γ := ctxToProductFree Γ)
      (A := _root_.Mathling.Lambek.ProductFree.Tp.atom A)
      (B := _root_.Mathling.Lambek.ProductFree.Tp.atom B)
      h_ne_pf h_pf)
```

左導入規則も翻訳先からそのまま再利用する。

```lean
theorem rdiv_l
  (h_arg : Sequent Δ (Tp.atom A))
  (h_main : Sequent (Γ ++ [Tp.atom B] ++ Λ) C) :
  Sequent (Γ ++ [Tp.rdiv B A] ++ Δ ++ Λ) C := by
  have h_main_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [_root_.Mathling.Lambek.ProductFree.Tp.atom B] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (_root_.Mathling.Lambek.ProductFree.Sequent.rdiv_l
      (Δ := ctxToProductFree Δ)
      (A := _root_.Mathling.Lambek.ProductFree.Tp.atom A)
      (Γ := ctxToProductFree Γ)
      (B := _root_.Mathling.Lambek.ProductFree.Tp.atom B)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)
```

規則定義の名前空間をここで閉じる。

```lean
end Sequent
```

読みやすさのため shallow 断片側の記法を与える。

```lean
infixl:50 " ⇒ " => Sequent
```

## 基本補題と主要定理

導出可能なシーケントは空文脈を持たない。

```lean
@[grind =>]
lemma nonempty_premises
  (h : _root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ A) : Γ ≠ [] := by
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

カット許容性は right 断片での結果を翻訳して得る。

```lean
theorem cut_admissible
  {Γ Δ Λ : List Tp} {A B : Tp}
  (d_left : _root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ A)
  (d_right : _root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent (Δ ++ [A] ++ Λ) B) :
  _root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent (Δ ++ Γ ++ Λ) B := by
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

右除法の右規則の逆転可能性も再輸出する。

```lean
theorem rdiv_invertible {Γ : List Tp} {B A : String}
  (h : _root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ (Tp.rdiv B A)) :
  _root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent (Γ ++ [Tp.atom A]) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.rdiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := _root_.Mathling.Lambek.ProductFree.Tp.atom A)
      (B := _root_.Mathling.Lambek.ProductFree.Tp.atom B)
      h)
```

原子式だけを見分ける述語を定義する。

```lean
@[grind]
def is_atom (A : Tp) : Prop :=
  _root_.Mathling.Lambek.ProductFree.translatedIsAtom Tp.toProductFree A
```

原子式のみの文脈から導出できる原子式は公理の場合に限られる。

```lean
theorem atom_generation {Γ : List Tp} {s : String}
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : _root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_pf :
      ∀ x ∈ ctxToProductFree Γ, _root_.Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [is_atom, Tp.toProductFree, _root_.Mathling.Lambek.ProductFree.is_atom,
      _root_.Mathling.Lambek.ProductFree.translatedIsAtom] using h_ctx y hy
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
end Mathling.Lambek.ProductFree.Right.Shallow
```

<!-- vim: set filetype=markdown : -->
