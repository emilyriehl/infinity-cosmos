/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

universe u

open SSet StrictSegal Simplicial

namespace CategoryTheory.SSet

open Opposite in
instance (S : SSet.{u}) [StrictSegal S] : Category.{u} (OneTruncation S) where
  id := 𝟙rq
  comp {X Y Z} f g := by
    refine ⟨?_, ?_⟩
    · apply StrictSegal.spineToDiagonal (n := 2)
      exact {
        vertex := fun | 0 => X | 1 => Y | 2 => Z
        arrow := fun | 0 => f.val | 1 => g.val
        arrow_src := by
          intro i
          fin_cases i
          · exact f.property.left
          · exact g.property.left
        arrow_tgt := by
          intro i
          fin_cases i
          · exact f.property.right
          · exact g.property.right }
    · apply And.intro
      · unfold OneTruncation.src
        change S.δ 1 _ = X
        rw [δ_one_spineToDiagonal]
      · unfold OneTruncation.tgt
        change S.δ 0 _ = Z
        rw [δ_zero_spineToDiagonal]
  id_comp {X Y} f := by
    sorry
  comp_id {X Y} f := by
    sorry
  assoc {W X Y Z} f g h := by
    sorry

end CategoryTheory.SSet
