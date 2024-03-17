import Lake
open Lake DSL

package «pseudorandom» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require LeanAPAP from git
  "https://github.com/YaelDillies/LeanAPAP.git"


require PFR from git
  "https://github.com/teorth/pfr.git"

@[default_target]
lean_lib «Pseudorandom» {
  -- add any library configuration options here
}
