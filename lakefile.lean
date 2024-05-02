import Lake
open Lake DSL

package «pseudorandom» {
  leanOptions := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩]
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require LeanAPAP from git
  "https://github.com/YaelDillies/LeanAPAP.git"

@[default_target]
lean_lib «Pseudorandom» {
  -- add any library configuration options here
}

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
