import InfinityCosmos.Mathlib.AlgebraicTopology.SimplexCategory
import InfinityCosmos.Mathlib.AlgebraicTopology.SimplicialSet
import InfinityCosmos.Mathlib.AlgebraicTopology.Nerve
import InfinityCosmos.Mathlib.AlgebraicTopology.Quasicategory

section preservesProducts

-- open Limits

-- /-- ER: This should be an instance of a theorem in mathlib about evaluation in functor categories preserving limits that exist. Statement has a universe level error.-/
-- -- def simplexBinaryProducts (X Y : SSet) (n : ℕ) : (X × Y) _[n] ≅ X _[n] × Y _[n] := by sorry

-- def hoFunctorPreservesExplicitBinaryProduct {X Y : SSet.{u}}
--     (s : BinaryFan X Y) (hyp : IsLimit s) :
--     IsLimit (BinaryFan.mk (SSet.hoFunctor.map (BinaryFan.fst s)) (SSet.hoFunctor.map (BinaryFan.snd s))) := by
--   have := limitObjIsoLimitCompEvaluation (pair X Y) (op [0])
--   simp at this
--   refine BinaryFan.isLimitMk ?lift ?fac_left ?fac_right ?uniq
--   · sorry
--   · sorry
--   · sorry
--   · sorry



-- def hoFunctorPreservesBinaryProduct {X Y : SSet.{u}} : PreservesLimit (pair X Y) SSet.hoFunctor where
--   preserves := by
--     intro c clim
--     sorry

-- def hoFunctorPreservesBinaryProducts :
--     PreservesLimitsOfShape (Discrete WalkingPair) SSet.hoFunctor where
--       preservesLimit := by
--         rintro K
--         have := diagramIsoPair K
--         sorry


-- end preservesProducts
