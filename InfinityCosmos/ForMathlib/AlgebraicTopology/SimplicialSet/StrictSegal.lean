/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

universe u

open CategoryTheory SimplicialObject

namespace SSet.StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

lemma δ_one_spineToDiagonal (f : Path X n) :
    X.δ 1 (spineToDiagonal f) = f.vertex 0 := by
  simp only [spineToDiagonal, diagonal, SimplicialObject.δ]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [SimplexCategory.δ_one_diag]
  simp only [spineToSimplex_vertex]

lemma δ_zero_spineToDiagonal (f : Path X n) :
    X.δ 0 (spineToDiagonal f) = f.vertex n := by
  simp only [spineToDiagonal, diagonal, SimplicialObject.δ]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [SimplexCategory.δ_zero_diag]
  simp only [spineToSimplex_vertex]

end SSet.StrictSegal
