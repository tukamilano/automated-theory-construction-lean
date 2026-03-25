import Lake
open Lake DSL

package «automated_Theory_Construction» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «AutomatedTheoryConstruction» {
  -- add any library configuration options here
}

lean_lib «AxiomaticThermoDynamics» where
  srcDir := "example"
