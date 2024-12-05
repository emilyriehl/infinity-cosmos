import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory

universe v u

namespace CategoryTheory.SimplicialObject
variable {C : Type u} [Category.{v} C] (X : SimplicialObject C)

lemma δ_one_zero : X.δ (n := 1) 0 = X.map (SimplexCategory.mkOfSucc 1).op := by
  simp only [δ, SimplexCategory.δ_one_zero]

lemma δ_one_one : X.δ (n := 1) 1 = X.diagonal := by
  simp only [δ, diagonal, SimplexCategory.δ_one_one]

lemma δ_one_two : X.δ (n := 1) 2 = X.map (SimplexCategory.mkOfSucc 0).op := by
  simp only [δ, SimplexCategory.δ_one_two]

end CategoryTheory.SimplicialObject
