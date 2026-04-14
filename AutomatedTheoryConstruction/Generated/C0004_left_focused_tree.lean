import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Generated.C0003_derivation_uniform_rep

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

/-- Left-focused trees exactly characterize left-only derivable sequents. -/
theorem thm_left_focused_tree_iff_left_only_000071 : ∀ (Γ : List Tp) (A : Tp), (∃ n : Nat, LeftFocusedTree n Γ A) ↔ ((LeftOnlyNode Γ A) ∧ Γ ⇒ A) := by
  intro Γ A
  constructor
  · rintro ⟨n, hTree⟩
    have hForget :
        ∀ {n : Nat} {Γ : List Tp} {A : Tp},
          LeftFocusedTree n Γ A → LeftOnlyNode Γ A ∧ FocusedTree n Γ A := by
      intro n
      induction n with
      | zero =>
          intro Γ A h
          cases h
      | succ n ih =>
          intro Γ A h
          cases A with
          | atom s =>
              rcases h with ⟨hLeft, hTree⟩
              refine ⟨hLeft, ?_⟩
              rcases hTree with rfl | ⟨c, hc, hcTree⟩
              · exact Or.inl rfl
              · refine Or.inr ⟨c, hc, ?_⟩
                cases c with
                | rdiv L B A Δ Λ =>
                    rcases hcTree with ⟨h1, h2⟩
                    exact ⟨(ih h1).2, (ih h2).2⟩
                | ldiv Γ₁ Δ A B R =>
                    rcases hcTree with ⟨h1, h2⟩
                    exact ⟨(ih h1).2, (ih h2).2⟩
          | ldiv A B =>
              rcases h with ⟨hLeft, hNe, hSub⟩
              exact ⟨hLeft, ⟨hNe, (ih hSub).2⟩⟩
          | rdiv B A =>
              rcases h with ⟨hLeft, hNe, hSub⟩
              exact ⟨hLeft, ⟨hNe, (ih hSub).2⟩⟩
    have hRoot := hForget hTree
    exact ⟨hRoot.1, (thm_sequent_iff_focused_tree_000023 (Γ := Γ) (A := A)).2 ⟨n, hRoot.2⟩⟩
  · exact fun a => thm_left_only_focused_tree_000062 Γ A a

/-- Right-focused trees exactly characterize right-only derivable sequents. -/
theorem thm_right_focused_tree_iff_000075 : ∀ (Γ : List Tp) (A : Tp), (∃ n : Nat, RightFocusedTree n Γ A) ↔ ((RightOnlyNode Γ A) ∧ Γ ⇒ A) := by
  intro Γ A
  constructor
  · rintro ⟨n, htree⟩
    have hforget : ∀ {n : Nat} {Γ : List Tp} {A : Tp}, RightFocusedTree n Γ A → FocusedTree n Γ A := by
      intro n
      induction n with
      | zero =>
          intro Γ A h
          cases h
      | succ n ih =>
          intro Γ A h
          cases A with
          | atom s =>
              rcases h with ⟨_, h'⟩
              rcases h' with rfl | ⟨c, hc, hcTree⟩
              · exact Or.inl rfl
              · rcases c with ⟨L, B, A, Δ, Λ⟩ | ⟨Γ₁, Δ, A, B, R⟩
                · right
                  refine ⟨Cand.rdiv L B A Δ Λ, hc, ?_⟩
                  exact And.imp ih ih hcTree
                · right
                  refine ⟨Cand.ldiv Γ₁ Δ A B R, hc, ?_⟩
                  exact And.imp ih ih hcTree
          | ldiv A B =>
              rcases h with ⟨_, hne, hsub⟩
              exact ⟨hne, ih hsub⟩
          | rdiv B A =>
              rcases h with ⟨_, hne, hsub⟩
              exact ⟨hne, ih hsub⟩
    have hright : RightOnlyNode Γ A := by
      cases n with
      | zero =>
          cases htree
      | succ n =>
          cases A with
          | atom s => exact htree.1
          | ldiv A B => exact htree.1
          | rdiv B A => exact htree.1
    refine ⟨hright, ?_⟩
    exact (thm_sequent_iff_focused_tree_000023 (Γ := Γ) (A := A)).2 ⟨n, hforget htree⟩
  · exact fun a => thm_right_only_focused_tree_000067 Γ A a

/-- Atomic left representability reduces to a singleton case or a left-division decomposition. -/
theorem thm_leftrep_atom_reduction_000072 : ∀ (Γ : List Tp) (s : String), LeftRep Γ (Tp.atom s) ↔ (Γ = [Tp.atom s] ∨ ∃ Pi : List Tp, ∃ Δ : List Tp, ∃ Λ : List Tp, ∃ A : Tp, ∃ B : Tp, Γ = Pi ++ Δ ++ [A ⧹ B] ++ Λ ∧ LeftRep Δ A ∧ LeftRep (Pi ++ [B] ++ Λ) (Tp.atom s)) := by
  intro Γ s
  constructor
  · intro h
    have hExact := (thm_left_oriented_derivation_exact_000058 Γ (Tp.atom s)).mp h
    rcases thm_atom_sequent_decompose_000009 hExact.2 with hAx | hRest
    · exact Or.symm (Or.inr hAx)
    · rcases hRest with ⟨Pi, B, A, Δ, Λ, hEq, hΔSeq, hMainSeq⟩ | ⟨Pi, Δ, A, B, Λ, hEq, hΔSeq, hMainSeq⟩
      · exfalso
        have hBad : LeftDivisionOnly (B ⧸ A) := by
          apply hExact.1
          rw [hEq]
          simp
        cases hBad
      · have hAB : LeftDivisionOnly A ∧ LeftDivisionOnly B := by
          have hSlash : LeftDivisionOnly (A ⧹ B) := by
            apply hExact.1
            rw [hEq]
            simp
          simpa [LeftDivisionOnly] using hSlash
        have hΔLeft : ∀ x ∈ A :: Δ, LeftDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hAB.1
          · apply hExact.1
            rw [hEq]
            simp [hx]
        have hMainLeft : ∀ x ∈ Tp.atom s :: (Pi ++ [B] ++ Λ), LeftDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hExact.1 _ (by exact List.mem_cons_self)
          · have hx' : x ∈ (Pi ++ [B]) ++ Λ := by simpa [List.append_assoc] using hx
            rcases List.mem_append.mp hx' with hxPiB | hxΛ
            · rcases List.mem_append.mp hxPiB with hxPi | hxB
              · exact hExact.1 _ (by rw [hEq]; simp [hxPi])
              · rcases List.mem_singleton.mp hxB with rfl
                exact (id (And.symm hAB)).left
            · exact hExact.1 _ (by rw [hEq]; simp [hxΛ])
        exact Or.inr ⟨Pi, Δ, Λ, A, B, hEq, (thm_left_oriented_derivation_exact_000058 Δ A).2 ⟨hΔLeft, hΔSeq⟩, (thm_left_oriented_derivation_exact_000058 (Pi ++ [B] ++ Λ) (Tp.atom s)).2 ⟨hMainLeft, hMainSeq⟩⟩
  · intro h
    rcases h with rfl | ⟨Pi, Δ, Λ, A, B, hEq, hΔ, hMain⟩
    · apply (thm_left_oriented_derivation_exact_000058 [Tp.atom s] (Tp.atom s)).2
      constructor
      · intro x hx
        simp at hx
        subst hx
        simp [LeftDivisionOnly]
      · exact thm_singleton_atom_iff_eq_000008.mpr rfl
    · have hΔExact := (thm_left_oriented_derivation_exact_000058 Δ A).mp hΔ
      have hMainExact := (thm_left_oriented_derivation_exact_000058 (Pi ++ [B] ++ Λ) (Tp.atom s)).mp hMain
      have hLeft : ∀ x ∈ Tp.atom s :: (Pi ++ Δ ++ [A ⧹ B] ++ Λ), LeftDivisionOnly x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hMainExact.1 _ (by exact List.mem_cons_self)
        · have hx' : x ∈ Pi ∨ x ∈ Δ ∨ x = A ⧹ B ∨ x ∈ Λ := by
            simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hx
          rcases hx' with hxPi | hxΔ | rfl | hxΛ
          · exact hMainExact.1 _ (by simp [hxPi])
          · exact hΔExact.1 _ (by exact List.mem_cons_of_mem A hxΔ)
          · have hA : LeftDivisionOnly A := hΔExact.1 _ (by exact List.mem_cons_self)
            have hB : LeftDivisionOnly B := hMainExact.1 _ (by simp)
            simpa [LeftDivisionOnly] using And.intro hA hB
          · exact hMainExact.1 _ (by simp [hxΛ])
      have hSeq : Pi ++ Δ ++ [A ⧹ B] ++ Λ ⇒ Tp.atom s := by
        simpa [List.append_assoc] using
          (Sequent.ldiv_l (Δ := Δ) (A := A) (Γ := Pi) (B := B) (Λ := Λ) (C := Tp.atom s) hΔExact.2 hMainExact.2)
      simpa [hEq] using (thm_left_oriented_derivation_exact_000058 (Pi ++ Δ ++ [A ⧹ B] ++ Λ) (Tp.atom s)).2 ⟨hLeft, hSeq⟩

/-- RightRep of an atom reduces to the singleton case or one right-division step. -/
theorem thm_rightrep_atom_reduction_000078 : ∀ (Γ : List Tp) (s : String), RightRep Γ (# s) ↔ (Γ = [# s] ∨ ∃ (pi delta lam : List Tp) (A B : Tp), Γ = pi ++ [B ⧸ A] ++ delta ++ lam ∧ RightRep delta A ∧ RightRep (pi ++ [B] ++ lam) (# s)) := by
  intro Γ s
  constructor
  · intro hRight
    have hExact := (thm_right_oriented_derivation_exact_000059 Γ (# s)).mp hRight
    rcases thm_atom_sequent_decompose_000009 (Γ := Γ) (s := s) hExact.2 with hAx | hCases
    · exact Or.symm (Or.inr hAx)
    · rcases hCases with ⟨pi, B, A, delta, lam, hΓ, hDeltaSeq, hMainSeq⟩ | ⟨pi, delta, A, B, lam, hΓ, hDeltaSeq, hMainSeq⟩
      · have hBA : RightDivisionOnly B ∧ RightDivisionOnly A := by
          have hDiv : RightDivisionOnly (B ⧸ A) := by
            exact hExact.1 _ (by simp [hΓ])
          simpa [RightDivisionOnly] using hDiv
        have hDeltaRight : ∀ x ∈ A :: delta, RightDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxDelta
          · exact (id (And.symm hBA)).left
          · exact hExact.1 x (by simp [hΓ, hxDelta])
        have hMainRight : ∀ x ∈ (# s) :: (pi ++ [B] ++ lam), RightDivisionOnly x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxMain
          · exact hExact.1 _ (by exact List.mem_cons_self)
          · have hxMain' : x ∈ pi ∨ x = B ∨ x ∈ lam := by
              simpa [List.mem_append, List.mem_singleton, or_assoc] using hxMain
            rcases hxMain' with hxPi | rfl | hxLam
            · exact hExact.1 x (by simp [hΓ, hxPi])
            · exact hBA.left
            · exact hExact.1 x (by simp [hΓ, hxLam])
        refine Or.inr ⟨pi, delta, lam, A, B, hΓ, ?_, ?_⟩
        · exact (thm_uniform_orientation_implies_oriented_derivation_000055 delta A).2 ⟨hDeltaRight, hDeltaSeq⟩
        · exact (thm_uniform_orientation_implies_oriented_derivation_000055 (pi ++ [B] ++ lam) (# s)).2 ⟨hMainRight, hMainSeq⟩
      · have hBad : RightDivisionOnly (A ⧹ B) := by
          exact hExact.1 _ (by simp [hΓ])
        simp [RightDivisionOnly] at hBad
  · rintro (rfl | ⟨pi, delta, lam, A, B, hΓ, hDeltaRight, hMainRight⟩)
    · refine (thm_uniform_orientation_implies_oriented_derivation_000055 [# s] (# s)).2 ?_
      constructor
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [RightDivisionOnly]
        · rcases List.mem_singleton.mp hx with rfl
          simp [RightDivisionOnly]
      · exact thm_singleton_atom_iff_eq_000008.mpr rfl
    · subst hΓ
      have hDeltaExact := (thm_right_oriented_derivation_exact_000059 delta A).mp hDeltaRight
      have hMainExact := (thm_right_oriented_derivation_exact_000059 (pi ++ [B] ++ lam) (# s)).mp hMainRight
      refine (thm_uniform_orientation_implies_oriented_derivation_000055 (pi ++ [B ⧸ A] ++ delta ++ lam) (# s)).2 ?_
      constructor
      · intro x hx
        have hx' : x = # s ∨ x ∈ pi ∨ x = B ⧸ A ∨ x ∈ delta ∨ x ∈ lam := by
          simpa [List.mem_cons, List.mem_append, List.mem_singleton, or_assoc, or_left_comm, or_comm] using hx
        rcases hx' with rfl | hxPi | rfl | hxDelta | hxLam
        · simp [RightDivisionOnly]
        · exact hMainExact.1 x (by simp [hxPi])
        · exact ⟨hMainExact.1 B (by simp), hDeltaExact.1 A (by exact List.mem_cons_self)⟩
        · exact hDeltaExact.1 x (by exact List.mem_cons_of_mem A hxDelta)
        · exact hMainExact.1 x (by simp [hxLam])
      · simpa [List.append_assoc] using
          (Mathling.Lambek.ProductFree.Sequent.rdiv_l
            (Δ := delta) (A := A) (Γ := pi) (B := B) (Λ := lam) (C := # s)
            hDeltaExact.2 hMainExact.2)

/-- RightRep is exactly the image of the pure right calculus. -/
theorem thm_rightrep_pure_right_exact_000080 : ∀ (Γ : List Tp) (A : Tp), RightRep Γ A ↔ ∃ ΓR : List Mathling.Lambek.ProductFree.Right.Tp, ∃ AR : Mathling.Lambek.ProductFree.Right.Tp, Γ = ΓR.map Mathling.Lambek.ProductFree.Right.Tp.toProductFree ∧ A = AR.toProductFree ∧ Mathling.Lambek.ProductFree.Right.Sequent ΓR AR := by
  intro Γ A
  constructor
  · intro h
    rcases h with ⟨ΓR, AR, hΓ, hA, hseq⟩
    refine ⟨ΓR, AR, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Right.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))
  · intro h
    rcases h with ⟨ΓR, AR, hΓ, hA, hseq⟩
    refine ⟨ΓR, AR, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Right.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))

/-- LeftRep is exactly the image of the pure left sequent calculus. -/
theorem thm_leftrep_iff_left_sequent_000086 : ∀ (Γ : List Tp) (A : Tp), LeftRep Γ A ↔ ∃ ΓL : List Mathling.Lambek.ProductFree.Left.Tp, ∃ AL : Mathling.Lambek.ProductFree.Left.Tp, Γ = ΓL.map Mathling.Lambek.ProductFree.Left.Tp.toProductFree ∧ A = AL.toProductFree ∧ Mathling.Lambek.ProductFree.Left.Sequent ΓL AL := by
  intro Γ A
  constructor
  · intro h
    rcases h with ⟨ΓL, AL, hΓ, hA, hseq⟩
    refine ⟨ΓL, AL, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Left.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))
  · intro h
    rcases h with ⟨ΓL, AL, hΓ, hA, hseq⟩
    refine ⟨ΓL, AL, ?_, ?_, hseq⟩
    · simpa [Mathling.Lambek.ProductFree.Left.ctxToProductFree] using hΓ.symm
    · exact ((fun a => a) ∘ fun a => a) (id (Eq.symm hA))

end AutomatedTheoryConstruction
