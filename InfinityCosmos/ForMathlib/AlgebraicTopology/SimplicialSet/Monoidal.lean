import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory

def SSet.isTerminal : IsTerminal (Δ[0] : SSet.{u}) where
  lift S := { app := fun X _ => ULift.up <| SimplexCategory.isTerminalZero.from _ }
  uniq := by intros ; ext ; apply ULift.ext ; apply SimplexCategory.isTerminalZero.hom_ext
