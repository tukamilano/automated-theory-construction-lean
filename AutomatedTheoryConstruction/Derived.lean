import Mathlib
import AutomatedTheoryConstruction.Theory
import AutomatedTheoryConstruction.Product

set_option autoImplicit false

namespace AutomatedTheoryConstruction

open Mathling.Lambek.ProductFree
local prefix:65 "#" => Tp.atom
local infixr:60 " ⧹ " => Mathling.Lambek.ProductFree.Tp.ldiv
local infixl:60 " ⧸ " => Mathling.Lambek.ProductFree.Tp.rdiv

-- Newly verified staging theorems are appended here by scripts/append_derived.py.
-- Promote reviewed results into Product.lean and then reset this file.

end AutomatedTheoryConstruction
