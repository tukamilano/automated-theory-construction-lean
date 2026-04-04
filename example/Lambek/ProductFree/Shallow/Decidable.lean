    import Mathlib.Data.Bool.Basic
    import Mathlib.Data.List.Basic
    import Mathling.Lambek.ProductFree.Decidable
    import Mathling.Lambek.ProductFree.Shallow.Basic
    import LiterateLean

# Decidability for the Shallow Fragment

このファイルでは、shallow 断片の決定可能性を
`Mathling.Lambek.ProductFree.Decidable` への翻訳で与える。

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

`prove1` は翻訳先の主探索手続きを呼び出す。

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.prove1 (ctxToProductFree Γ) A.toProductFree
```

`proveAux` は深さ付き探索を shallow 側へ持ち上げたものである。

```lean
@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.proveAux n (ctxToProductFree Γ) A.toProductFree
```

`prove2` は十分大きい深さを与えた決定手続きである。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.prove2 (ctxToProductFree Γ) A.toProductFree
```

## 単調性と補助補題

探索深さを増やしても証明可能性は保たれる。

1 ステップだけ探索深さを増やしても成功は保たれる。

```lean
@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  simpa [proveAux, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_mono
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)
```

より大きい任意の深さへの単調性も従う。

```lean
@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  simpa [proveAux, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_mono_le
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h hp)
```

深さ付き探索が成功すれば主探索も成功する。

```lean
@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  simpa [prove1, proveAux, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_sound
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)
```

逆向きには、主探索の成功から十分な深さ付き探索が得られる。

```lean
@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  simpa [prove1, prove2, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.proveAux_complete
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)
```

したがって `prove1` と `prove2` は同値である。

```lean
lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  simpa [prove1, prove2, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_iff_prove2
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree))
```

## シーケント体系との一致

翻訳先での健全性・完全性を shallow 断片へ移す。

探索が成功したら shallow シーケントは導出可能である。

```lean
@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_sound
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)
```

導出可能性から探索の成功も従う。

```lean
@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_complete
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)
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
  rw [← prove1_iff_prove2, prove1_iff_sequent]
```

したがって shallow シーケントには `Decidable` instance が入る。

```lean
instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

left-shallow の典型例を `by decide` で確認する。

```lean
example : [Tp.atom "p", Tp.ldiv "p" "q"] ⇒ Tp.atom "q" := by decide
```

right-shallow の典型例も同様に確認する。

```lean
example : [Tp.rdiv "q" "p", Tp.atom "p"] ⇒ Tp.atom "q" := by decide
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Shallow
```

<!-- vim: set filetype=markdown : -->
