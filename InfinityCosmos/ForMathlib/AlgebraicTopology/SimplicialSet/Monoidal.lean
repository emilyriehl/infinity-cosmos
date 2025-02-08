import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

universe u

open CategoryTheory Limits Simplicial

namespace SSet

/-- The object `Δ[0]` is terminal in `SSet`.-/
def isTerminalDeltaZero : IsTerminal (Δ[0] : SSet.{u}) where
  lift S := { app := fun X _ => ULift.up <| SimplexCategory.isTerminalZero.from _ }
  uniq := by intros ; ext ; apply ULift.ext ; apply SimplexCategory.isTerminalZero.hom_ext

end SSet
