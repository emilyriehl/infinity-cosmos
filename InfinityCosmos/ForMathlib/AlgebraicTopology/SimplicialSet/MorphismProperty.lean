/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import InfinityCosmos.ForMathlib.CategoryTheory.MorphismProperty
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

namespace SSet

section trivialFibration

open CategoryTheory Simplicial MorphismProperty

/-- an inductive type defining boundary inclusions as a class of morphisms. Used to take advantage
  of the `MorphismProperty` API. -/
inductive BoundaryInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk n : BoundaryInclusion (boundaryInclusion n)

/-- The class of all boundary inclusions. -/
def BoundaryInclusions : MorphismProperty SSet := fun _ _ p ↦ BoundaryInclusion p

/-- a morphism of simplicial sets is a trivial fibration if it has the right lifting property wrt
  every boundary inclusion  `∂Δ[n] ⟶ Δ[n]`. -/
def trivialFibration : MorphismProperty SSet := fun _ _ p ↦ BoundaryInclusions.rlp p

end trivialFibration

end SSet
