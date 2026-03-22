import AutomatedTheoryConstruction.Theory

namespace AutomatedTheoryConstruction

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


theorem thm_op_000001_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, (x * y) * z = x * (y * z)) := by
  intro h
  let T : Type u := ULift (Fin 3)
  let a0 : T := ULift.up (0 : Fin 3)
  let a1 : T := ULift.up (1 : Fin 3)
  let a2 : T := ULift.up (2 : Fin 3)
  let mulFin : Fin 3 → Fin 3 → Fin 3 := fun a b =>
    if a = 0 then 0
    else if a = 1 then
      if b = 1 then 1 else 0
    else
      if b = 0 then 0 else 2
  let mulT : T → T → T := fun a b => ULift.up (mulFin a.down b.down)
  let mulInst : Mul T := ⟨mulT⟩
  let sg : SemigroupLike01 T := by
    letI : Mul T := mulInst
    refine
      { mul := mulT
        ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · native_decide
    · native_decide
    · native_decide
  letI : SemigroupLike01 T := sg
  have h' := h (α := T) a2 a1 a2
  change a2 = a0 at h'
  have hne : a2 ≠ a0 := by
    native_decide
  exact hne h'


theorem thm_op_000002_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y : α, x * y = y * x) := by
  intro h
  let T : Type u := ULift (Fin 2)
  let a0 : T := ULift.up (0 : Fin 2)
  let a1 : T := ULift.up (1 : Fin 2)
  let mulT : T → T → T := fun a _ => a
  let mulInst : Mul T := ⟨mulT⟩
  let sg : SemigroupLike01 T := by
    letI : Mul T := mulInst
    refine
      { mul := mulT
        ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      rfl
    · intro x y
      rfl
    · intro x y z
      rfl
  letI : SemigroupLike01 T := sg
  have h' := h (α := T) a0 a1
  change a0 = a1 at h'
  have hne : a0 ≠ a1 := by
    native_decide
  exact hne h'


theorem thm_op_000003_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, e * x = x ∧ x * e = x) := by
  intro h
  let T : Type u := ULift Bool
  let t : T := ULift.up true
  let f : T := ULift.up false
  let semigroupLikeT : SemigroupLike01 T :=
    { mul := fun x y => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  letI : SemigroupLike01 T := semigroupLikeT
  obtain ⟨e, he⟩ := h (α := T)
  have ht : e = t := by
    simpa [t] using (he t).1
  have hf : e = f := by
    simpa [f] using (he f).1
  have htf : t = f := ht.symm.trans hf
  have hbool : true = false := by
    simpa [t, f] using congrArg ULift.down htf
  cases hbool


theorem thm_op_000004_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∃ e : α, ∀ x : α, ∃ y : α, x * y = e ∧ y * x = e) := by
  intro h
  let T : Type u := ULift Int
  let mulT : T → T → T := fun a b => ULift.up (min a.down b.down)
  let mulInst : Mul T := ⟨mulT⟩
  let sg : SemigroupLike01 T := by
    letI : Mul T := mulInst
    refine
      { mul := mulT
        ax_left_idempotent := ?_
        ax_right_absorb_duplicate := ?_
        ax_middle_swap := ?_ }
    · intro x
      change ULift.up (min x.down x.down) = x
      cases x
      simp [mulT]
    · intro x y
      change ULift.up (min x.down (min x.down y.down)) = ULift.up (min x.down y.down)
      simp [← min_assoc]
    · intro x y z
      change ULift.up (min (min x.down y.down) z.down) = ULift.up (min (min x.down z.down) y.down)
      exact congrArg ULift.up (min_right_comm x.down y.down z.down)
  letI : SemigroupLike01 T := sg
  obtain ⟨e, he⟩ := h (α := T)
  have hbelow : ∀ x : T, e.down ≤ x.down := by
    intro x
    obtain ⟨y, hxy, hyx⟩ := he x
    change ULift.up (min x.down y.down) = e at hxy
    have hxy' : min x.down y.down = e.down := by
      simpa using congrArg ULift.down hxy
    rw [← hxy']
    exact min_le_left _ _
  have hbad : e.down ≤ e.down - 1 := hbelow (ULift.up (e.down - 1))
  omega


theorem thm_op_000005_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ join : α → α → α, ∀ x y z : α, x * (join y z) = join (x * y) (x * z)) := by
  intro h
  let T : Type u := ULift.{u, 0} (Sum (Fin 1) (Fin 1))
  let a : T := ULift.up (Sum.inl 0)
  let b : T := ULift.up (Sum.inr 0)
  let join : T → T → T := fun _ _ => a
  let inst : SemigroupLike01 T :=
    { mul := fun x y => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  letI : SemigroupLike01 T := inst
  have hEq : b * join a a = join (b * a) (b * a) :=
    h (α := T) join b a a
  have hba : b = a := by
    simpa [a, b, join, inst] using hEq
  have hs : (Sum.inr (0 : Fin 1) : Sum (Fin 1) (Fin 1)) = Sum.inl (0 : Fin 1) := by
    simpa [a, b] using congrArg ULift.down hba
  cases hs


theorem thm_op_000006_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ x y z : α, x * y = x * z → y = z) := by
  intro h
  let T : Type u := ULift.{u, 0} (Fin 2)
  let a0 : T := ULift.up (0 : Fin 2)
  let a1 : T := ULift.up (1 : Fin 2)
  let semigroupLikeT : SemigroupLike01 T :=
    { mul := fun x _ => x
      ax_left_idempotent := by
        intro x
        rfl
      ax_right_absorb_duplicate := by
        intro x y
        rfl
      ax_middle_swap := by
        intro x y z
        rfl }
  letI : SemigroupLike01 T := semigroupLikeT
  have h01 : a0 = a1 := by
    apply h (α := T) a0 a0 a1
    rfl
  have hne : a0 ≠ a1 := by
    native_decide
  exact hne h01


theorem thm_op_000007 : ∀ {α : Type u} [SemigroupLike01 α], ∀ x : α, x * x = x := by
  intro α _ x
  simpa [AutomatedTheoryConstruction.op] using
    (AutomatedTheoryConstruction.SemigroupLike01.ax_left_idempotent (α := α) x)


theorem thm_op_000008_is_false : ¬(∀ {α : Type u} [SemigroupLike01 α], ∀ meet : α → α → α, ∀ x y : α, x * (meet x y) = x) := by
  intro h
  let α := ULift.{u} Bool
  let sg : SemigroupLike01 α :=
    { mul := fun a b => ⟨a.down && b.down⟩
      ax_left_idempotent := by
        intro x
        cases x with
        | up b =>
            cases b <;> rfl
      ax_right_absorb_duplicate := by
        intro x y
        cases x with
        | up a =>
            cases y with
            | up b =>
                cases a <;> cases b <;> rfl
      ax_middle_swap := by
        intro x y z
        cases x with
        | up a =>
            cases y with
            | up b =>
                cases z with
                | up c =>
                    cases a <;> cases b <;> cases c <;> rfl }
  letI : SemigroupLike01 α := sg
  have hbad : ((⟨true⟩ : α) * ⟨false⟩) = (⟨true⟩ : α) :=
    h (α := α) (meet := fun _ _ : α => ⟨false⟩) ⟨true⟩ ⟨true⟩
  change ((⟨false⟩ : α) = (⟨true⟩ : α)) at hbad
  cases hbad


theorem thm_op_000009 : ∀ {α : Type u} [SemigroupLike01 α], (∀ x y : α, x * y = y * x) → ∀ x y z : α, (x * y) * z = x * (y * z) := by
  intro α _ hcomm x y z
  calc
    (x * y) * z = (y * x) * z := by rw [hcomm x y]
    _ = (y * z) * x := by simpa [op] using (SemigroupLike01.ax_middle_swap y x z)
    _ = x * (y * z) := by rw [hcomm (y * z) x]


theorem thm_op_000010 : ∀ {α : Type u} [SemigroupLike01 α] [Fintype α], (∃ x y z : α, (x * y) * z ≠ x * (y * z)) → 3 ≤ Fintype.card α := by
  intro α _ _ hnonassoc
  classical
  have hxx : ∀ t : α, t * t = t := by
    intro t
    simpa [AutomatedTheoryConstruction.op] using
      (SemigroupLike01.ax_left_idempotent (α := α) t)
  have habs : ∀ a b : α, a * (a * b) = a * b := by
    intro a b
    simpa [AutomatedTheoryConstruction.op] using
      (SemigroupLike01.ax_right_absorb_duplicate (α := α) a b)
  have hswap : ∀ a b c : α, (a * b) * c = (a * c) * b := by
    intro a b c
    simpa [AutomatedTheoryConstruction.op] using
      (SemigroupLike01.ax_middle_swap (α := α) a b c)
  by_contra hlt
  have hcard : Fintype.card α ≤ 2 := by
    omega
  have hpair : ∀ a b c : α, a = b ∨ b = c ∨ a = c := by
    intro a b c
    by_contra h
    push_neg at h
    have h3 : 3 ≤ Fintype.card α := by
      calc
        3 = ({a, b, c} : Finset α).card := by
          simp [h.1, h.2.1, h.2.2]
        _ ≤ Fintype.card α := Finset.card_le_univ _
    omega
  obtain ⟨x, y, z, hne⟩ := hnonassoc
  have hassoc : (x * y) * z = x * (y * z) := by
    rcases hpair x y z with hxy | hyz | hxz
    · calc
        (x * y) * z = (x * x) * z := by simpa [hxy]
        _ = x * z := by rw [hxx x]
        _ = x * (x * z) := by simpa using (habs x z).symm
        _ = x * (y * z) := by simpa [hxy]
    · calc
        (x * y) * z = (x * y) * y := by simpa [hyz]
        _ = x * y := by
          have hmul : x * y = x ∨ x * y = y := by
            rcases hpair (x * y) x y with h | h | h
            · exact Or.inl h
            · exact Or.inl <| by simpa [h] using hxx x
            · exact Or.inr h
          rcases hmul with h | h
          · rw [h, h]
          · rw [h, hxx y]
        _ = x * (y * y) := by rw [hxx y]
        _ = x * (y * z) := by simpa [hyz]
    · calc
        (x * y) * z = (x * y) * x := by simpa [hxz]
        _ = (x * x) * y := by simpa using hswap x y x
        _ = x * y := by rw [hxx x]
        _ = x * (y * x) := by
          have hyx : y * x = x ∨ y * x = y := by
            rcases hpair (y * x) x y with h | h | h
            · exact Or.inl h
            · exact Or.inl <| by simpa [h] using hxx y
            · exact Or.inr h
          rcases hyx with h | h
          · have hxy' : x * y = x := by
              have hyxy : (y * x) * y = y * x := by
                calc
                  (y * x) * y = (y * y) * x := by simpa using hswap y x y
                  _ = y * x := by rw [hxx y]
              simpa [h] using hyxy
            rw [h, hxy', hxx x]
          · rw [h]
        _ = x * (y * z) := by simpa [hxz]
  exact hne hassoc


theorem thm_op_000014 : ∀ {α : Type u} [SemigroupLike01 α], (∃ e : α, ∀ x : α, e * x = x) → ∀ x y : α, x * y = y * x := by
  intro α _ h x y
  rcases h with ⟨e, he⟩
  simpa [AutomatedTheoryConstruction.op, he x, he y] using
    (AutomatedTheoryConstruction.SemigroupLike01.ax_middle_swap (x := e) (y := x) (z := y))

end AutomatedTheoryConstruction
