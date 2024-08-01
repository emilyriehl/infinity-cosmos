import Lake
open Lake DSL

/- Define the package configuration for the project.
Includes options for Lean's pretty-printer and implicit argument settings. -/
package «infinity-cosmos» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,      -- Pretty-print `fun a ↦ b`
    ⟨`autoImplicit, false⟩,       -- Disable auto-implicit arguments
    ⟨`relaxedAutoImplicit, false⟩ -- Disable relaxed auto-implicit arguments
  ]

/- Specify external dependencies required for this project. -/
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

/- Define the default Lean library target for the project.
This can be customized with additional library configuration options.
-/
@[default_target]
lean_lib «infinity-cosmos» where
  -- Add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"