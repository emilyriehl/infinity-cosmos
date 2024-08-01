import Lake
open Lake DSL

/- Define the package configuration for the project.
Includes options for Lean's pretty-printer and implicit argument settings. -/
package «Project» where
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
lean_lib «Project» where
  -- Add any library configuration options here
