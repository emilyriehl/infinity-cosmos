module

public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

@[expose] public section


universe u

open CategoryTheory Limits Simplicial

namespace SSet

/-- The object `Δ[0]` is terminal in `SSet`. -/
def isTerminalDeltaZero : IsTerminal (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀

end SSet
