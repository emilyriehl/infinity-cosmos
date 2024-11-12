import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal 

open CategoryTheory Simplicial SimplexCategory Limits

namespace SimplexCategory

def d0_terminal : IsTerminal ([0] : SimplexCategory) := by
  refine IsTerminal.ofUniqueHom (fun _ ↦ const _ [0] 0) ?_
  · apply eq_const_to_zero 


end SimplexCategory 