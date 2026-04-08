import Mathlib
import AutomatedTheoryConstruction.Theory

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

-- Verified theorems are appended here by scripts/append_derived.py.
-- Keep any short theorem docstrings/comments here instead of a separate metadata index.


/-- Contextual replacement for a derived left division. -/
theorem thm_ldiv_context_replacement_000005 : ∀ {Γ Δ Λ : List Tp} {A B C : Tp}, (Γ ⇒ (A ⧹ B)) → (Δ ++ [B] ++ Λ ⇒ C) → (Δ ++ [A] ++ Γ ++ Λ ⇒ C) := by
  intro Γ Δ Λ A B C h₁ h₂
  simpa [List.append_assoc] using cut_admissible (ldiv_invertible h₁) h₂


/-- Right-division contextual replacement. -/
theorem thm_rdiv_context_replacement_000006 : ∀ {Γ Δ Λ : List Mathling.Lambek.ProductFree.Tp} {A B C : Mathling.Lambek.ProductFree.Tp}, Mathling.Lambek.ProductFree.Sequent Γ (Mathling.Lambek.ProductFree.Tp.rdiv B A) → Mathling.Lambek.ProductFree.Sequent (Δ ++ [B] ++ Λ) C → Mathling.Lambek.ProductFree.Sequent (Δ ++ Γ ++ [A] ++ Λ) C := by
  intro Γ Δ Λ A B C hΓ hC
  have hB : Mathling.Lambek.ProductFree.Sequent (Γ ++ [A]) B :=
    Mathling.Lambek.ProductFree.rdiv_invertible hΓ
  simpa [List.append_assoc] using
    (Mathling.Lambek.ProductFree.cut_admissible hB hC)


/-- Applies a right division derivation to an appended argument derivation. -/
theorem thm_rdiv_append_application_000001 : ∀ {Γ Δ : List Tp} {A B : Tp}, Γ ⇒ (B ⧸ A) → Δ ⇒ A → Γ ++ Δ ⇒ B := by
  intro Γ Δ A B hΓ hΔ
  have hBA : Γ ++ [A] ⇒ B := rdiv_invertible hΓ
  have hcut : Γ ++ Δ ++ [] ⇒ B :=
    cut_admissible (Γ := Δ) (Δ := Γ) (Λ := []) hΔ (by simpa using hBA)
  simpa using hcut


/-- Applies a left division derivation to a derivation of its argument. -/
theorem thm_ldiv_application_concat_000002 : ∀ {Γ Δ : List Mathling.Lambek.ProductFree.Tp} {A B : Mathling.Lambek.ProductFree.Tp}, Mathling.Lambek.ProductFree.Sequent Γ (Mathling.Lambek.ProductFree.Tp.ldiv A B) → Mathling.Lambek.ProductFree.Sequent Δ A → Mathling.Lambek.ProductFree.Sequent (Δ ++ Γ) B := by
  intro Γ Δ A B hΓ hΔ
  have hcut : Mathling.Lambek.ProductFree.Sequent ([] ++ Δ ++ Γ) B :=
    Mathling.Lambek.ProductFree.cut_admissible (Γ := Δ) (Δ := []) (Λ := Γ) hΔ
      (by simpa using Mathling.Lambek.ProductFree.ldiv_invertible hΓ)
  simpa using hcut

end AutomatedTheoryConstruction
