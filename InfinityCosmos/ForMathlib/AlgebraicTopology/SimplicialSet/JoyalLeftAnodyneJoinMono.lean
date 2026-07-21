/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinCore
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinTelescopeRight
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinCoproducts
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.JoyalJoinStarBase

/-!
# The Joyal pushout-product: left-anodyne ⋆̂ monomorphism is inner-anodyne

Assembles the headline of Layer A, the Joyal pushout-product `joyal_leftAnodyne_join_mono`: the
Leibniz join of a monomorphism `j` with a left-anodyne extension `i` is inner-anodyne. Wires the
reduction `satI_of_instances` (LeibnizJoinCore) against the four second-slot stability facts of
`leibImgR j` — cobase change and retracts (LeibnizJoinCore), coproducts (LeibnizJoinCoproducts),
transfinite composition (LeibnizJoinTelescopeRight) — together with the generators `satJ`
(JoyalJoinStarBase).
-/

open CategoryTheory Simplicial Limits MorphismProperty SmallObject

namespace SSet
universe u
noncomputable section

/-- **satI** (infinity-cosmos #117, second-slot saturation): for a monomorphism `j`, every
left-anodyne extension `i` lands in `leibImgR j`, i.e. `leibnizJoin j i` is inner-anodyne. -/
theorem satI {S T : SSet.{u}} (j : S ⟶ T) (hj : Mono j) :
    leftAnodyneExtensions.{u} ≤ leibImgR j :=
  satI_of_instances j hj
    (Coprod.leibImgR_coproducts j)
    (TwoC.leibImgR_isStableUnderTransfiniteComposition j)
    satJ

/-- **joyal_leftAnodyne_join_mono** (the Joyal pushout-product): the Leibniz join
of a monomorphism `j` with a left-anodyne extension `i` is inner-anodyne. -/
theorem joyal_leftAnodyne_join_mono {S T A B : SSet.{u}} (j : S ⟶ T) (hj : Mono j)
    (i : A ⟶ B) (hi : leftAnodyneExtensions.{u} i) :
    innerAnodyneExtensions (leibnizJoin j i) :=
  satI j hj i hi

end
end SSet
