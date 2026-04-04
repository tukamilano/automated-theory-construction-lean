    import Mathlib.Data.Bool.Basic
    import Mathlib.Data.List.Basic
    import Mathling.Lambek.ProductFree.Right.Shallow.Basic
    import Mathling.Lambek.ProductFree.Decidable
    import LiterateLean

# Decidability for the Right-Shallow Fragment

このファイルでは、right-shallow 断片の決定可能性を
`_root_.Mathling.Lambek.ProductFree.Right.Decidable` への翻訳で与える。

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

`prove1` は right 断片側の主探索を shallow 側へ持ち上げたものである。

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  _root_.Mathling.Lambek.ProductFree.translatedProve1 Tp.toProductFree Γ A
```

`proveAux` は深さ付き探索を表す。

```lean
@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  _root_.Mathling.Lambek.ProductFree.translatedProveAux
    Tp.toProductFree n Γ A
```

`prove2` は決定手続きとして使う最終版である。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  _root_.Mathling.Lambek.ProductFree.translatedProve2 Tp.toProductFree Γ A
```

## 単調性と補助補題

1 ステップだけ探索深さを増やしても成功は保たれる。

```lean
@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  simpa [proveAux] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_mono
      Tp.toProductFree h)
```

より大きい深さへの単調性も同様に従う。

```lean
@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  simpa [proveAux] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_mono_le
      Tp.toProductFree h hp)
```

深さ付き探索が成功すれば主探索も成功する。

```lean
@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  simpa [prove1, proveAux] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_sound
      Tp.toProductFree h)
```

逆に、主探索の成功から十分大きい深さ付き探索が得られる。

```lean
@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  simpa [prove1, prove2] using
    (_root_.Mathling.Lambek.ProductFree.translatedProveAux_complete
      Tp.toProductFree h)
```

したがって `prove1` と `prove2` は同値である。

```lean
lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  simpa [prove1, prove2] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve1_iff_Prove2
      Tp.toProductFree (Γ := Γ) (A := A))
```

## シーケント体系との一致

探索の成功はシーケント導出を与える。

```lean
@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve1_sound
      Tp.toProductFree h)
```

シーケント導出から探索の成功も従う。

```lean
@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  have h_pf :
      _root_.Mathling.Lambek.ProductFree.Sequent
        (List.map Tp.toProductFree Γ) A.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [prove1] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve1_complete
      Tp.toProductFree h_pf)
```

これで探索と導出の同値が得られる。

```lean
@[grind .]
lemma prove1_iff_sequent {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ Γ ⇒ A := by
  constructor <;> [apply prove1_sound; apply prove1_complete]
```

`prove2` についても同じ同値を使える。

```lean
@[grind .]
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  simpa [prove2, Sequent, ctxToProductFree, Tp.toProductFree] using
    (_root_.Mathling.Lambek.ProductFree.translatedProve2_iff_Sequent
      Tp.toProductFree (Γ := Γ) (A := A))
```

したがって shallow シーケントには `Decidable` instance が入る。

```lean
instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

記法が期待通りに展開される例を置く。

```lean
example : [Tp.rdiv "q" "p", Tp.atom "p"] = [Tp.rdiv "q" "p", Tp.atom "p"] := rfl
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Right.Shallow
```

<!-- vim: set filetype=markdown : -->
