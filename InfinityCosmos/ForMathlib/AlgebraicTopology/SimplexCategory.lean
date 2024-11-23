import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Simplicial SimplexCategory Limits

namespace SimplexCategory

/-- The object `[0]` is terminal in `SimplexCategory`.-/
def isTerminalZero : IsTerminal ([0] : SimplexCategory) :=
  IsTerminal.ofUniqueHom (fun _ ↦ const _ [0] 0) (fun _ _ => eq_const_to_zero _)

end SimplexCategory
