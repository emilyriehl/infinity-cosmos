import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

universe u

open CategoryTheory
open Simplicial SimplicialObject SimplexCategory

namespace SSet.StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

lemma δ_one_spineToDiagonal (f : Path X n) :
    X.δ 1 (spineToDiagonal f) = f.vertex 0 := by
  simp only [spineToDiagonal, diagonal, SimplicialObject.δ]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have : δ 1 ≫ diag n = const [0] [n] 0 := by ext i; fin_cases i; rfl
  rw [this]
  rw [spineToSimplex_vertex]

lemma δ_zero_spineToDiagonal (f : Path X n) :
    X.δ 0 (spineToDiagonal f) = f.vertex n := by
  simp only [spineToDiagonal, diagonal, SimplicialObject.δ]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have : δ 0 ≫ diag n = const [0] [n] n := by ext i; fin_cases i; rfl
  rw [this]
  rw [spineToSimplex_vertex]

end SSet.StrictSegal
