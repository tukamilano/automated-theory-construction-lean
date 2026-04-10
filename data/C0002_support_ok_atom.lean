import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0001_singleton_sequent_atom

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

/-- Atomic sequents are singleton axioms or decompose through a candidate. -/
theorem thm_atom_goal_candidate_cases_000007 : ∀ (Γ : List Tp) (s : String), (Γ ⇒ # s) → Γ = [# s] ∨ ∃ c : Cand, c ∈ candidates Γ ∧ match c with | Cand.rdiv L B A Δ Λ => (Δ ⇒ A) ∧ (L ++ [B] ++ Λ ⇒ # s) | Cand.ldiv Gamma1 Δ A B R => (Δ ⇒ A) ∧ (Gamma1 ++ [B] ++ R ⇒ # s) := by
  intro Γ s h
  cases h with
  | ax =>
      exact Or.symm (Or.inr rfl)
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      right
      refine ⟨Cand.rdiv Γ₁ B A Δ Λ, ?_, ?_⟩
      · exact candidates_rdiv_mem Γ₁ Δ Λ A B
      · exact ⟨d_arg, d_main⟩
  | ldiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      right
      refine ⟨Cand.ldiv Γ₁ Δ A B Λ, ?_, ?_⟩
      · exact candidates_ldiv_mem Γ₁ Δ Λ A B
      · exact ⟨d_arg, d_main⟩


def occurs_atom (t : String) : Tp → Prop
  | Tp.atom name => name = t
  | Tp.ldiv A B => occurs_atom t A ∨ occurs_atom t B
  | Tp.rdiv A B => occurs_atom t A ∨ occurs_atom t B

/-- Any atom occurring in a derived type already occurs in the context. -/
theorem thm_occurs_atom_from_context_000021_is_false : ¬(∀ {Γ : List Tp} {A : Tp} {t : String}, (Γ ⇒ A) → occurs_atom t A → ∃ B ∈ Γ, occurs_atom t B) := by
  intro h
  let p : Tp := #"p"
  let q : Tp := #"q"
  let bad : Tp := q ⧸ (p ⧹ q)
  have hp : [p] ⇒ p := Sequent.ax
  have hq : [q] ⇒ q := Sequent.ax
  have hldiv : [p, p ⧹ q] ⇒ q := by
    simpa [p, q] using
      (Sequent.ldiv_l (Δ := [p]) (A := p) (Γ := []) (B := q) (Λ := []) (C := q) hp hq)
  have hseq : [p] ⇒ bad := by
    have hne : [p] ≠ [] := nonempty_premises hp
    simpa [bad, p, q] using
      (Sequent.rdiv_r (Γ := [p]) (A := p ⧹ q) (B := q) hne hldiv)
  have hocc : occurs_atom "q" bad := by
    simp [occurs_atom, bad, p, q]
  rcases h (Γ := [p]) (A := bad) (t := "q") hseq hocc with ⟨B, hB, hBt⟩
  simp [p] at hB
  subst hB
  simp [occurs_atom] at hBt


def support_ok (Γ : List Tp) : Tp → Prop
  | Tp.atom s => ∃ B ∈ Γ, occurs_atom s B
  | Tp.ldiv B C => Γ ≠ [] ∧ support_ok ([B] ++ Γ) C
  | Tp.rdiv C B => Γ ≠ [] ∧ support_ok (Γ ++ [B]) C

lemma support_ok_replace
    {Γ L R Λ : List Tp} {B B' C : Tp}
    (hocc : ∀ s : String, occurs_atom s B → occurs_atom s B')
    (h : support_ok (Γ ++ [B] ++ Λ) C) :
    support_ok (Γ ++ L ++ [B'] ++ R ++ Λ) C := by
  induction C generalizing Γ L R Λ with
  | atom s =>
      rcases h with ⟨X, hX, hXocc⟩
      simp at hX
      rcases hX with hX | rfl | hX
      · refine ⟨X, ?_, hXocc⟩
        simp [hX]
      · refine ⟨B', ?_, hocc s hXocc⟩
        simp
      · refine ⟨X, ?_, hXocc⟩
        exact List.mem_append_right (Γ ++ L ++ [B'] ++ R) hX
  | ldiv D C ihD ihC =>
      rcases h with ⟨_, hC⟩
      constructor
      · simp
      · simpa [List.append_assoc] using
          ihC (Γ := [D] ++ Γ) (L := L) (R := R) (Λ := Λ) (by simpa [List.append_assoc] using hC)
  | rdiv C D ihC ihD =>
      rcases h with ⟨_, hC⟩
      constructor
      · simp
      · simpa [List.append_assoc] using
          ihC (Γ := Γ) (L := L) (R := R) (Λ := Λ ++ [D]) (by simpa [List.append_assoc] using hC)

lemma support_ok_self_singleton (A : Tp) : support_ok [A] A := by
  induction A with
  | atom s =>
      refine ⟨# s, List.mem_singleton.mpr rfl, by simp [occurs_atom]⟩
  | ldiv B C ihB ihC =>
      constructor
      · exact List.cons_ne_nil (B \ C) []
      · simpa using
          (support_ok_replace
            (Γ := []) (L := [B]) (R := []) (Λ := [])
            (B := C) (B' := B ⧹ C) (C := C)
            (fun s hs => by simp [occurs_atom, hs]) ihC)
  | rdiv C B ihC ihB =>
      constructor
      · exact List.cons_ne_nil (C / B) []
      · simpa using
          (support_ok_replace
            (Γ := []) (L := []) (R := [B]) (Λ := [])
            (B := C) (B' := C ⧸ B) (C := C)
            (fun s hs => by simp [occurs_atom, hs]) ihC)

/-- Every derivable sequent satisfies the recursive support predicate. -/
theorem thm_derivable_support_ok_000032 : ∀ {Γ : List Tp} {A : Tp}, (Γ ⇒ A) → support_ok Γ A := by
  intro Γ A h
  induction h with
  | ax =>
      (expose_names; exact support_ok_self_singleton A_1)
  | rdiv_r hne hBA ih =>
      exact ⟨hne, ((fun a => ih) ∘ fun a => Γ) Γ⟩
  | ldiv_r hne hAB ih =>
      exact ⟨hne, ((fun a => ih) ∘ fun a => Γ) Γ⟩
  | rdiv_l d_arg d_main ih_arg ih_main =>
      rename_i Δ A' Γ' B Λ C
      simpa [List.append_assoc] using
        (support_ok_replace
          (Γ := Γ') (L := []) (R := Δ) (Λ := Λ)
          (B := B) (B' := B ⧸ A') (C := C)
          (fun s hs => by simp [occurs_atom, hs]) ih_main)
  | ldiv_l d_arg d_main ih_arg ih_main =>
      rename_i Δ A' Γ' B Λ C
      simpa [List.append_assoc] using
        (support_ok_replace
          (Γ := Γ') (L := Δ) (R := []) (Λ := Λ)
          (B := B) (B' := A' ⧹ B) (C := C)
          (fun s hs => by simp [occurs_atom, hs]) ih_main)


inductive AtomicCandidateTree : List Tp → String → Prop where
  | base (s : String) :
      AtomicCandidateTree [# s] s
  | step_rdiv (Γ L Δ Λ : List Tp) (A B : Tp) (s : String)
      (hc : Cand.rdiv L B A Δ Λ ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : AtomicCandidateTree (L ++ [B] ++ Λ) s) :
      AtomicCandidateTree Γ s
  | step_ldiv (Γ Γ₁ Δ R : List Tp) (A B : Tp) (s : String)
      (hc : Cand.ldiv Γ₁ Δ A B R ∈ candidates Γ)
      (harg : Δ ⇒ A)
      (hrec : AtomicCandidateTree (Γ₁ ++ [B] ++ R) s) :
      AtomicCandidateTree Γ s

/-- Atomic candidate trees characterize atomic sequents. -/
theorem thm_atomic_candidate_tree_iff_sequent_000030 : ∀ (Γ : List Tp) (s : String), AtomicCandidateTree Γ s ↔ (Γ ⇒ # s) := by
  intro Γ s
  constructor
  · intro h
    induction h with
    | base s =>
        exact thm_singleton_atomic_sequent_iff_000011.mpr rfl
    | step_rdiv Γ L Δ Λ A B s hc harg hrec ih =>
        have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
        subst Γ
        exact Sequent.rdiv_l harg ih
    | step_ldiv Γ Γ₁ Δ R A B s hc harg hrec ih =>
        have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
          symm
          simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
        subst Γ
        exact Sequent.ldiv_l harg ih
  · have hcomplete : ∀ (Γ : List Tp) (s : String), (Γ ⇒ # s) → AtomicCandidateTree Γ s := by
      intro Γ s
      let n := list_degree Γ
      have hmain : ∀ n (Γ : List Tp) (s : String), list_degree Γ = n → (Γ ⇒ # s) → AtomicCandidateTree Γ s := by
        intro n
        refine Nat.strong_induction_on n ?_
        intro n ih Γ s hdeg h
        rcases thm_atom_goal_candidate_cases_000007 Γ s h with rfl | ⟨c, hc, hcases⟩
        · exact AtomicCandidateTree.base s
        · cases c with
          | rdiv L B A Δ Λ =>
              rcases hcases with ⟨harg, hrec⟩
              have hlt : list_degree (L ++ [B] ++ Λ) < n := by
                have hΓ : Γ = L ++ [B ⧸ A] ++ Δ ++ Λ := by
                  symm
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.rdiv L B A Δ Λ) hc)
                rw [hΓ] at hdeg
                rw [← hdeg]
                simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
                omega
              exact
                AtomicCandidateTree.step_rdiv Γ L Δ Λ A B s hc harg
                  (ih (list_degree (L ++ [B] ++ Λ)) hlt (L ++ [B] ++ Λ) s rfl hrec)
          | ldiv Γ₁ Δ A B R =>
              rcases hcases with ⟨harg, hrec⟩
              have hlt : list_degree (Γ₁ ++ [B] ++ R) < n := by
                have hΓ : Γ = Γ₁ ++ Δ ++ [A ⧹ B] ++ R := by
                  symm
                  simpa using (candidates_list_degree (Γ := Γ) (c := Cand.ldiv Γ₁ Δ A B R) hc)
                rw [hΓ] at hdeg
                rw [← hdeg]
                simp [list_degree_traversible, List.append_assoc, list_degree, tp_degree]
                omega
              exact
                AtomicCandidateTree.step_ldiv Γ Γ₁ Δ R A B s hc harg
                  (ih (list_degree (Γ₁ ++ [B] ++ R)) hlt (Γ₁ ++ [B] ++ R) s rfl hrec)
      exact hmain n Γ s rfl
    exact hcomplete Γ s


inductive SupportClosure : List Tp → Tp → Prop where
  | self (A : Tp) :
      SupportClosure [A] A
  | ldiv_r (Γ : List Tp) (B C : Tp)
      (hΓ : Γ ≠ [])
      (h : SupportClosure ([B] ++ Γ) C) :
      SupportClosure Γ (B ⧹ C)
  | rdiv_r (Γ : List Tp) (C B : Tp)
      (hΓ : Γ ≠ [])
      (h : SupportClosure (Γ ++ [B]) C) :
      SupportClosure Γ (C ⧸ B)
  | replace (Γ L R Λ : List Tp) (B B' C : Tp)
      (hocc : ∀ s : String, occurs_atom s B → occurs_atom s B')
      (h : SupportClosure (Γ ++ [B] ++ Λ) C) :
      SupportClosure (Γ ++ L ++ [B'] ++ R ++ Λ) C

/-- The inductive support closure coincides with support_ok. -/
theorem thm_support_closure_matches_support_ok_000036 : ∀ (Γ : List Tp) (A : Tp), SupportClosure Γ A ↔ support_ok Γ A := by
  intro Γ A
  constructor
  · intro h
    induction h with
    | self A =>
        exact support_ok_self_singleton A
    | ldiv_r Γ B C hΓ h ih =>
        exact ⟨hΓ, by simpa using ih⟩
    | rdiv_r Γ C B hΓ h ih =>
        exact ⟨hΓ, by simpa using ih⟩
    | replace Γ L R Λ B B' C hocc h ih =>
        exact support_ok_replace hocc ih
  · revert Γ
    induction A with
    | atom s =>
        intro Γ h
        rcases h with ⟨B, hB, hocc⟩
        have hsplit : ∃ L R, Γ = L ++ [B] ++ R := by
          induction Γ with
          | nil =>
              cases hB
          | cons X Γ ih =>
              simp at hB
              rcases hB with rfl | hB
              · exact ⟨[], Γ, by simp⟩
              · rcases ih hB with ⟨L, R, hLR⟩
                exact ⟨X :: L, R, by simp [hLR]⟩
        rcases hsplit with ⟨L, R, rfl⟩
        simpa [List.append_assoc] using
          (SupportClosure.replace
            (Γ := []) (L := L) (R := R) (Λ := [])
            (B := # s) (B' := B) (C := # s)
            (fun t ht => by
              simp [occurs_atom] at ht
              exact (Eq.to_iff (congrFun (congrArg occurs_atom (id (Eq.symm ht))) B)).mpr hocc)
            (SupportClosure.self (# s)))
    | ldiv B C ihB ihC =>
        intro Γ h
        rcases h with ⟨hΓ, hC⟩
        exact SupportClosure.ldiv_r Γ B C hΓ (ihC ([B] ++ Γ) hC)
    | rdiv C B ihC ihB =>
        intro Γ h
        rcases h with ⟨hΓ, hC⟩
        exact SupportClosure.rdiv_r Γ C B hΓ (ihC (Γ ++ [B]) hC)


theorem supportClosure_atom_iff_occurs_in_context (Γ : List Tp) (s : String) :
    SupportClosure Γ (# s) ↔ ∃ B ∈ Γ, occurs_atom s B := by
  simpa [support_ok] using
    (thm_support_closure_matches_support_ok_000036 Γ (# s))

end AutomatedTheoryConstruction
