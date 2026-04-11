import Mathlib
import AutomatedTheoryConstruction.Lambek
import AutomatedTheoryConstruction.Generated.Manifest
import AutomatedTheoryConstruction.Derived

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
open scoped Mathling.Lambek.ProductFree

theorem thm_atomic_residual_step_wellfounded_000078 : WellFounded (fun q p : AtomicResidualState => AtomicResidualGraphStep p q) := by
  refine Subrelation.wf ?_ (measure (fun p : AtomicResidualState => list_degree p.1)).wf
  intro q p hstep
  simpa using atomicResidualGraphStep_degree_lt hstep

end AutomatedTheoryConstruction
