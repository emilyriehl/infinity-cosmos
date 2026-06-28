/-
SatiAssembly.lean — end-to-end assembly of `satI` for infinity-cosmos #117 (second-slot saturation).

Wires the reduction `satI_of_instances` (SatiCore) against the four proven, axiom-clean
second-slot saturation facts of `leibImgR j` and the proven `satJ`:

  * IsStableUnderCobaseChange         — `leibImgR_cobase`                       (SatiCore)
  * IsStableUnderRetracts             — `leibImgR_isStableUnderRetracts`        (SatiCore)
  * IsStableUnderCoproducts           — `Coprod.leibImgR_coproducts`            (SatiCoprod)
  * IsStableUnderTransfiniteComposition
        — `TwoC.leibImgR_isStableUnderTransfiniteComposition`                   (SatiTC)
  * generators from satJ              — `satJ`                                  (Final / satJ infra)

`leibImgR` is the single shared definition from `SatiCore`; the transfinite (`TwoC`) and
coproduct (`Coprod`) bricks are namespaced only to keep their internal helper names
(`cornerMap`, the `aTel`/`G…` tower, …) from colliding with the satJ infrastructure (`Deps`).
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinCore
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinTelescopeRight
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinCoproducts
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.JoyalJoinStarBase

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

/-- **joyal_leftAnodyne_join_mono**: the Leibniz join of a monomorphism `j` with a
left-anodyne extension `i` is inner-anodyne. -/
theorem joyal_leftAnodyne_join_mono {S T A B : SSet.{u}} (j : S ⟶ T) (hj : Mono j)
    (i : A ⟶ B) (hi : leftAnodyneExtensions.{u} i) :
    innerAnodyneExtensions (leibnizJoin j i) :=
  satI j hj i hi

end
end SSet
