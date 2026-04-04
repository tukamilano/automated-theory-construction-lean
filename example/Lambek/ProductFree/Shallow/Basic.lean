    import Mathlib.Data.List.Basic
    import Mathlib.Data.Nat.Basic
    import Mathling.Lambek.ProductFree.Basic
    import LiterateLean

# Shallow Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の shallow 断片を定義する。
shallow 断片では、除法の引数は原子式に限定される。

基本的なメタ理論は `Mathling.Lambek.ProductFree.Basic` に翻訳して再利用する。
これにより、shallow 断片の定義は独立に保ちつつ、重い証明を重複させずに済む。

```lean
namespace Mathling.Lambek.ProductFree.Shallow
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

まず、shallow 断片で扱う論理式を定義する。

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : String)  : Tp
  | rdiv (B A : String)  : Tp
  deriving Repr, DecidableEq
```

原子式の記法を導入する。

```lean
prefix:65 "#" => Tp.atom
```

左除法の記法を導入する。

```lean
infixr:60 " ⧹ " => Tp.ldiv
```

右除法の記法を導入する。

```lean
infixl:60 " ⧸ " => Tp.rdiv
```

次数は shallow の構文に合わせて単純に数える。

```lean
@[grind =]
def tp_degree : Tp → Nat
  | Tp.atom _ => 1
  | Tp.ldiv _ _ => 3
  | Tp.rdiv _ _ => 3
```

文脈全体の次数は要素ごとの次数の和で定義する。

```lean
@[grind =]
def list_degree : List Tp → Nat
  | [] => 0
  | A :: Γ => tp_degree A + list_degree Γ
```

連結に対する加法性もここで押さえる。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind
```

## 一般断片への翻訳

shallow 断片の証明は、一般の product-free 断片へ翻訳して再利用する。

各 shallow 論理式を一般断片の論理式へ写す。

```lean
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
```

文脈も要素ごとに翻訳する。

```lean
def ctxToProductFree : List Tp → List Mathling.Lambek.ProductFree.Tp :=
  List.map Tp.toProductFree
```

空文脈の翻訳は自明である。

```lean
@[simp] lemma ctxToProductFree_nil :
    ctxToProductFree [] = [] := rfl
```

先頭要素を付けた文脈の翻訳も簡約できる。

```lean
@[simp] lemma ctxToProductFree_cons :
    ctxToProductFree (A :: Γ) = A.toProductFree :: ctxToProductFree Γ := rfl
```

連結に対して翻訳が分配されることを記録する。

```lean
@[simp] lemma ctxToProductFree_append :
    ctxToProductFree (Γ ++ Δ) = ctxToProductFree Γ ++ ctxToProductFree Δ := by
  simp [ctxToProductFree]
```

shallow シーケントは翻訳先のシーケントとして実装する。

```lean
def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree
```

## shallow シーケント規則

基本規則は翻訳先の定理をそのまま持ち上げる。

以下では shallow 規則をまとめるための名前空間を開く。

```lean
namespace Sequent
```

公理規則は翻訳先の公理からそのまま従う。

```lean
theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ax :
      Mathling.Lambek.ProductFree.Sequent [A.toProductFree] A.toProductFree)
```

左除法の右規則も翻訳先から持ち上げる。

```lean
theorem ldiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent ([Tp.atom A] ++ Γ) (Tp.atom B)) :
  Sequent Γ (Tp.ldiv A B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_r
      (by simpa using h_ne) h)
```

右除法の右規則では非空性と前提の翻訳を明示する。

```lean
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
```

左除法の左規則も翻訳先の規則から再利用する。

```lean
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
```

右除法の左規則も同様に翻訳から得る。

```lean
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
```

規則定義をここで閉じる。

```lean
end Sequent
```

読みやすさのため shallow シーケントの記法を与える。

```lean
infixl:50 " ⇒ " => Sequent
```

## 基本補題と主要定理

カット許容性、逆転可能性、原子式生成は一般断片の結果から従う。

導出可能なシーケントは必ず非空の文脈を持つ。

```lean
@[grind =>]
lemma nonempty_premises
  (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToProductFree] using
        (Mathling.Lambek.ProductFree.nonempty_premises h)
  | cons => simp
```

非空文脈を含む連結もやはり非空である。

```lean
@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  cases Γ <;> simp at h ⊢
```

カット許容性は一般断片での定理を翻訳して得る。

```lean
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
```

左除法の右規則の逆転可能性を再輸出する。

```lean
theorem ldiv_invertible {Γ : List Tp} {A B : String}
  (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ (Tp.ldiv A B)) :
  Mathling.Lambek.ProductFree.Shallow.Sequent ([Tp.atom A] ++ Γ) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.ldiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h)
```

右除法についても同じく逆転可能性を得る。

```lean
theorem rdiv_invertible {Γ : List Tp} {A B : String}
  (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ (Tp.rdiv B A)) :
  Mathling.Lambek.ProductFree.Shallow.Sequent (Γ ++ [Tp.atom A]) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.rdiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h)
```

原子式かどうかを判定する述語を定義する。

```lean
@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _ => False
```

原子式だけからなる文脈では、導出できる原子式は公理の場合に限られる。

```lean
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
        contradiction
    | rdiv B A =>
        have : False := by simpa [is_atom] using h_ctx _ hy
        contradiction
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
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Shallow
```

<!-- vim: set filetype=markdown : -->
