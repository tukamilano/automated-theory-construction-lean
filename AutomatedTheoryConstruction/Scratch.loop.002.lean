import Mathlib
import Mathlib
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

theorem thm_boxk_orbit_repeat_fixpoint_000047 : ∀ {α : Type*} [ACR α] [ACR.Prov α] [ACR.Reft α] [ACR.APS α] (k : ℕ) {x : α} {m n : ℕ}, 0 < k → x ≤ ((fun z : α => □z)^[k]) x → m < n → ((((fun z : α => □z)^[k])^[m]) x ≐ (((fun z : α => □z)^[k])^[n]) x) → ∃ h : α, h ≐ ((fun z : α => □z)^[k]) h := by
  intro α _ _ _ _ k x m n _hk hx hmn hrepeat
  let f : α → α := ((fun z : α => □z)^[k])
  have hmonoBox : Monotone (fun z : α => □z) := by
    intro a b hab
    exact ACR.prov_mono hab
  have hmono : Monotone f := by
    simpa [f] using hmonoBox.iterate k
  have horbit : Monotone (fun t : ℕ => f^[t] x) :=
    Monotone.monotone_iterate_of_le_map hmono (by simpa [f] using hx)
  refine ⟨f^[m] x, ?_⟩
  constructor
  · simpa [f, Function.iterate_succ_apply'] using horbit (Nat.le_succ m)
  · have hle : f^[m + 1] x ≤ f^[n] x := horbit (Nat.succ_le_of_lt hmn)
    have hback : f^[n] x ≤ f^[m] x := by
      simpa [f] using hrepeat.2
    exact le_trans (by simpa [f, Function.iterate_succ_apply'] using hle) hback

end AutomatedTheoryConstruction
