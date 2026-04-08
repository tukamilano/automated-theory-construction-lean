import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_ldiv_application_concat_000002 : ∀ {Γ Δ : List Mathling.Lambek.ProductFree.Tp} {A B : Mathling.Lambek.ProductFree.Tp}, Mathling.Lambek.ProductFree.Sequent Γ (Mathling.Lambek.ProductFree.Tp.ldiv A B) → Mathling.Lambek.ProductFree.Sequent Δ A → Mathling.Lambek.ProductFree.Sequent (Δ ++ Γ) B := by
  intro Γ Δ A B hΓ hΔ
  have hcut : Mathling.Lambek.ProductFree.Sequent ([] ++ Δ ++ Γ) B :=
    Mathling.Lambek.ProductFree.cut_admissible (Γ := Δ) (Δ := []) (Λ := Γ) hΔ
      (by simpa using Mathling.Lambek.ProductFree.ldiv_invertible hΓ)
  simpa using hcut

end AutomatedTheoryConstruction
