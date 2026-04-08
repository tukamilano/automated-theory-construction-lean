import Mathlib.Data.Bool.Basic
import AutomatedTheoryConstruction.Lambek.Basic

namespace Mathling.Lambek.ProductFree

local prefix:65 "☉" => Tp.atom
local infixr:60 " ⧹ " => Tp.ldiv
local infixl:60 " ⧸ " => Tp.rdiv

@[grind]
def splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun (l, r) => (x :: l, r))

@[grind .]
lemma splits_list_degree (h : X ∈ splits Γ) :
  X.1 ++ X.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind .]
lemma splits_mem {α} (Γ Δ : List α) : (Γ, Δ) ∈ splits (Γ ++ Δ) := by
  induction Γ with
  | nil =>
      cases Δ <;> simp [splits]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ?_
      refine ⟨(xs, Δ), ih, ?_⟩
      exact Prod.ext rfl rfl

@[grind]
def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))

@[grind =>]
lemma picks_list_degree (h : X ∈ picks Γ) :
   X.1 ++ [X.2.1] ++ X.2.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind .]
lemma picks_mem {α} (Γ Δ : List α) (a : α) :
    (Γ, a, Δ) ∈ picks (Γ ++ [a] ++ Δ) := by
  induction Γ with
  | nil => simp [picks]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ?_
      refine ⟨(xs, a, Δ), ?_, ?_⟩
      · simpa [List.append_assoc] using ih
      · exact Prod.ext rfl rfl

@[grind]
inductive Cand where
  | rdiv (L : List Tp) (B A : Tp) (Δ Λ : List Tp)
  | ldiv (Γ Δ : List Tp) (A B : Tp) (Λ : List Tp)

@[grind]
def candidates (Γ : List Tp) : List Cand :=
  (picks Γ).flatMap (fun (L, f, R) =>
    match f with
    | B ⧸ A =>
        (splits R).map (fun (Δ, Λ) => .rdiv L B A Δ Λ)
    | A ⧹ B =>
        (splits L).map (fun (Γ, Δ) => .ldiv Γ Δ A B R)
    | ☉ _ => [])

@[grind =>]
lemma candidates_list_degree (h : c ∈ candidates Γ) :
  match c with
    | .rdiv L B A Δ Λ => L ++ [B ⧸ A] ++ Δ ++ Λ = Γ
    | .ldiv Γ₁ Δ A B R => Γ₁ ++ Δ ++ [A ⧹ B] ++ R = Γ := by
  simp only [candidates, List.mem_flatMap, Prod.exists] at h
  rcases h with ⟨L, f, R, h_pick, h_cand⟩
  cases f with
  | atom s =>
      grind
  | rdiv B A =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = R := splits_list_degree hX
      grind
  | ldiv A B =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = L := splits_list_degree hX
      grind

@[grind .]
lemma candidates_rdiv_mem (Γ Δ Λ : List Tp) (A B : Tp) :
  Cand.rdiv Γ B A Δ Λ ∈ candidates (Γ ++ [B ⧸ A] ++ Δ ++ Λ) := by
  unfold candidates
  refine List.mem_flatMap.mpr ?_
  refine ⟨(Γ, B ⧸ A, Δ ++ Λ), ?_, ?_⟩
  · grind
  · refine List.mem_map.mpr ?_
    refine ⟨(Δ, Λ), ?_, ?_⟩ <;> grind

@[grind .]
lemma candidates_ldiv_mem (Γ₁ Δ R : List Tp) (A B : Tp) :
  Cand.ldiv Γ₁ Δ A B R ∈ candidates (Γ₁ ++ Δ ++ [A ⧹ B] ++ R) := by
  unfold candidates
  refine List.mem_flatMap.mpr ?_
  refine ⟨(Γ₁ ++ Δ, A ⧹ B, R), ?_, ?_⟩
  · exact picks_mem (Γ₁ ++ Δ) R (A ⧹ B)
  · refine List.mem_map.mpr ?_
    refine ⟨(Γ₁, Δ), ?_, ?_⟩ <;> grind

@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  match A with
  | Tp.atom s =>
    (Γ = [Tp.atom s]) ||
    (candidates Γ).attach.any (fun ⟨c, _hc⟩ =>
      match c with
      | .rdiv L B A' Δ Λ =>
        prove1 Δ A' && prove1 (L ++ [B] ++ Λ) (☉ s)
      | .ldiv Λ Δ A' B R =>
        prove1 Δ A' && prove1 (Λ ++ [B] ++ R) (☉ s))
  | Tp.ldiv A' B =>
    Γ ≠ [] && prove1 ([A'] ++ Γ) B
  | Tp.rdiv B A' =>
    Γ ≠ [] && prove1 (Γ ++ [A']) B
termination_by
  list_degree Γ + tp_degree A
decreasing_by
  all_goals grind

@[grind .]
def proveAux : Nat → List Tp → Tp → Bool
  | 0, _,  _ => false
  | n + 1, Γ,  A =>
    match A with
    | Tp.atom s =>
        (Γ = [Tp.atom s]) ||
        (candidates Γ).any (fun c =>
          match c with
          | .rdiv L B A' Δ Λ =>
              proveAux n Δ A' &&
              proveAux n (L ++ [B] ++ Λ) (☉ s)
          | .ldiv Γ₁ Δ A' B R =>
              proveAux n Δ A' &&
              proveAux n (Γ₁ ++ [B] ++ R) (☉ s))
    | Tp.ldiv A' B =>
        (Γ ≠ []) && proveAux n ([A'] ++ Γ) B
    | Tp.rdiv B A' =>
        (Γ ≠ []) && proveAux n (Γ ++ [A']) B

@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  proveAux (list_degree Γ + tp_degree A + 1) Γ A

@[grind =>]
lemma proveAux_mono (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  induction n generalizing Γ A <;> grind

@[grind =>]
lemma proveAux_mono_le {n m : Nat} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  induction h <;> grind

@[grind =>]
lemma proveAux_sound (h : proveAux n Γ A) : prove1 Γ A := by
  induction n generalizing Γ A with
  | zero => grind
  | succ n ih =>
      cases A with
      | atom s =>
        simp only [proveAux, Bool.or_eq_true, List.any_eq_true] at h
        unfold prove1
        simp only [Bool.or_eq_true]
        rcases h with h_base | h_cand
        · exact Or.symm (Or.inr h_base)
        · right
          rcases h_cand with ⟨c, hc_mem, hc_val⟩
          simp only [List.any_eq_true]
          refine ⟨⟨c, hc_mem⟩, ?_, ?_⟩
          · exact List.mem_attach (candidates Γ) ⟨c, hc_mem⟩
          grind
      | ldiv A' B => grind
      | rdiv B A' => grind

@[grind =>]
lemma proveAux_complete (h : prove1 Γ A) : prove2 Γ A := by
  unfold prove2
  induction Γ, A using prove1.induct
  case case1 Γ s h_rdiv_left h_rdiv_right h_ldiv_left h_ldiv_right =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h ⊢
    rcases h with h_ax | h_left
    · exact Or.symm (Or.inr h_ax)
    · right
      rcases h_left with ⟨⟨c, hc_mem⟩, -, hc_val⟩
      refine ⟨c, hc_mem, ?_⟩
      cases c with
      | rdiv L B A' Δ Λ =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · have h_le :
            list_degree Δ + tp_degree A' + 1 ≤
              list_degree Γ + tp_degree (☉ s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
        · have h_le :
            list_degree (L ++ [B] ++ Λ) + tp_degree (☉ s) + 1 ≤
              list_degree Γ + tp_degree (☉ s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
      | ldiv Γ₁ Δ A' B R =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · have h_le :
            list_degree Δ + tp_degree A' + 1 ≤
              list_degree Γ + tp_degree (☉ s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
        · have h_le :
            list_degree (Γ₁ ++ [B] ++ R) + tp_degree (☉ s) + 1 ≤
              list_degree Γ + tp_degree (☉ s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
  case case2 Γ A' B h_rec =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor
    · exact Bool.eq_false_imp_eq_true.mp fun a => h_ne
    · have h_eq :
        list_degree (A' :: Γ) + tp_degree B + 1 =
          list_degree Γ + tp_degree (A' ⧹ B) := by
        grind
      grind
  case case3 Γ B A' h_rec =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor
    · exact Bool.eq_false_imp_eq_true.mp fun a => h_ne
    · have h_eq :
        list_degree (Γ ++ [A']) + tp_degree B + 1 =
          list_degree Γ + tp_degree (B ⧸ A') := by
        grind
      grind

lemma prove1_iff_prove2 : prove1 Γ A ↔ prove2 Γ A := by grind

@[grind =>]
lemma prove1_sound (h : prove1 Γ A) : Γ ⇒ A := by
  induction Γ, A using prove1.induct with
  | case1 Γ s h_rdiv_left h_rdiv_right h_ldiv_left h_ldiv_right =>
      grind only [prove1, List.any_eq, List.any_eq_false, Sequent.ax, candidates_list_degree,
        Sequent.rdiv_l, Sequent.ldiv_l]
  | case2 Γ A' B h_rec => grind
  | case3 Γ B A' h_rec => grind

@[grind =>]
lemma prove1_complete (h : Γ ⇒ A) : prove1 Γ A := by
  revert h
  classical
  have hp :
      ∀ n Γ A, list_degree Γ + tp_degree A = n → Γ ⇒ A → prove1 Γ A := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih Γ A h_deg h
    unfold prove1
    cases A with
    | atom s =>
        cases h with
        | ax => grind
        | rdiv_l d_arg d_main =>
            rename_i Δ A Γ₁ B Λ
            simp only [Bool.or_eq_true, List.any_eq_true]
            right
            refine ⟨⟨Cand.rdiv Γ₁ B A Δ Λ, ?_⟩, by simp, ?_⟩
            · exact candidates_rdiv_mem Γ₁ Δ Λ A B
            grind
        | ldiv_l d_arg d_main =>
            rename_i Δ A Γ₁ B Λ
            simp only [Bool.or_eq_true, List.any_eq_true]
            right
            refine ⟨⟨Cand.ldiv Γ₁ Δ A B Λ, ?_⟩, by simp, ?_⟩
            · exact candidates_ldiv_mem Γ₁ Δ Λ A B
            grind
    | ldiv A' B => grind
    | rdiv B A' => grind
  exact fun h =>
    (fun {b} => Bool.eq_false_imp_eq_true.mp) fun a =>
      hp (list_degree Γ + tp_degree A) Γ A rfl h

@[grind .]
lemma prove1_iff_sequent : prove1 Γ A ↔ Γ ⇒ A := by grind

@[grind .]
theorem prove2_iff_sequent : prove2 Γ A ↔ Γ ⇒ A := by grind

instance : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent

example : [Tp.atom "p", Tp.ldiv (Tp.atom "p") (Tp.atom "q")] ⇒ Tp.atom "q" :=
  by decide

def translatedProve1 (toProductFree : α → Tp) (Γ : List α) (A : α) : Bool :=
  prove1 (Γ.map toProductFree) (toProductFree A)

def translatedProveAux (toProductFree : α → Tp) (n : Nat) (Γ : List α) (A : α) : Bool :=
  proveAux n (Γ.map toProductFree) (toProductFree A)

def translatedProve2 (toProductFree : α → Tp) (Γ : List α) (A : α) : Bool :=
  prove2 (Γ.map toProductFree) (toProductFree A)

lemma translatedProveAux_mono
    (toProductFree : α → Tp)
    {n : Nat} {Γ : List α} {A : α}
    (h : translatedProveAux toProductFree n Γ A) :
    translatedProveAux toProductFree (n + 1) Γ A := by
  simpa [translatedProveAux] using
    (proveAux_mono (Γ := Γ.map toProductFree) (A := toProductFree A) h)

lemma translatedProveAux_mono_le
    (toProductFree : α → Tp)
    {n m : Nat} {Γ : List α} {A : α}
    (h : n ≤ m) (hp : translatedProveAux toProductFree n Γ A) :
    translatedProveAux toProductFree m Γ A := by
  simpa [translatedProveAux] using
    (proveAux_mono_le (Γ := Γ.map toProductFree) (A := toProductFree A) h hp)

lemma translatedProveAux_sound
    (toProductFree : α → Tp)
    {n : Nat} {Γ : List α} {A : α}
    (h : translatedProveAux toProductFree n Γ A) :
    translatedProve1 toProductFree Γ A := by
  simpa [translatedProve1, translatedProveAux] using
    (proveAux_sound (Γ := Γ.map toProductFree) (A := toProductFree A) h)

lemma translatedProveAux_complete
    (toProductFree : α → Tp)
    {Γ : List α} {A : α}
    (h : translatedProve1 toProductFree Γ A) :
    translatedProve2 toProductFree Γ A := by
  simpa [translatedProve1, translatedProve2] using
    (proveAux_complete (Γ := Γ.map toProductFree) (A := toProductFree A) h)

lemma translatedProve1_iff_Prove2
    (toProductFree : α → Tp)
    {Γ : List α} {A : α} :
    translatedProve1 toProductFree Γ A ↔ translatedProve2 toProductFree Γ A := by
  simpa [translatedProve1, translatedProve2] using
    (prove1_iff_prove2 (Γ := Γ.map toProductFree) (A := toProductFree A))

lemma translatedProve1_sound
    (toProductFree : α → Tp)
    {Γ : List α} {A : α}
    (h : translatedProve1 toProductFree Γ A) :
    Sequent (Γ.map toProductFree) (toProductFree A) := by
  simpa [translatedProve1] using
    (prove1_sound (Γ := Γ.map toProductFree) (A := toProductFree A) h)

lemma translatedProve1_complete
    (toProductFree : α → Tp)
    {Γ : List α} {A : α}
    (h : Sequent (Γ.map toProductFree) (toProductFree A)) :
    translatedProve1 toProductFree Γ A := by
  simpa [translatedProve1] using
    (prove1_complete (Γ := Γ.map toProductFree) (A := toProductFree A) h)

lemma translatedProve1_iff_Sequent
    (toProductFree : α → Tp)
    {Γ : List α} {A : α} :
    translatedProve1 toProductFree Γ A ↔ Sequent (Γ.map toProductFree) (toProductFree A) := by
  constructor
  · exact translatedProve1_sound toProductFree
  · exact translatedProve1_complete toProductFree

theorem translatedProve2_iff_Sequent
    (toProductFree : α → Tp)
    {Γ : List α} {A : α} :
    translatedProve2 toProductFree Γ A ↔ Sequent (Γ.map toProductFree) (toProductFree A) := by
  rw [← translatedProve1_iff_Prove2, translatedProve1_iff_Sequent]

end Mathling.Lambek.ProductFree
