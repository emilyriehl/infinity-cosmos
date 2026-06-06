import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

universe u

open CategoryTheory Limits Simplicial

namespace SSet

/-- The object `Δ[0]` is terminal in `SSet`. -/
def isTerminalDeltaZero : IsTerminal (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀

end SSet
