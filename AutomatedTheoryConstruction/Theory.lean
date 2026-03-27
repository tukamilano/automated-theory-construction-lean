import AutomatedTheoryConstruction.Theory.Core
import AutomatedTheoryConstruction.Theory.PolynomialModel

/-!
# CCR Formalization
This entry module formalizes a minimal axiom system around creation/annihilation
operators (canonical commutation relations, CCR) in quantum mechanics.

## Structure
1. **Bosonic Core**: `AutomatedTheoryConstruction.Theory.Core`
2. **Polynomial Model**: `AutomatedTheoryConstruction.Theory.PolynomialModel`

## Key Insight
The Fock structure is **not axiomatic** here. It is reconstructed from CCR and
the vacuum alone. Everything else (number operator, ladder structure) follows.
-/
