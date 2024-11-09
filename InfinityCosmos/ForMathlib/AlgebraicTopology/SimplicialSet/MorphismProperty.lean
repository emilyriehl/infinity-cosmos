/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import InfinityCosmos.ForMathlib.CategoryTheory.MorphismProperty
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

namespace SSet

open CategoryTheory Simplicial MorphismProperty

section trivialFibration

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

/-- Definition of isofibration via inner fibrations -/
section isoFibration

/-- Inductive definition of inner horn inclusions Λ[n, i] ⟶ Δ[n] 
  by restricting general horn inclusions to 0 < i < n -/
inductive InnerInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (n i : ℕ) (low : 0 < i) (high : i < n) : InnerInclusion (hornInclusion n i)

/-- The class of inner horn inclusions as a MorphismProperty -/
def InnerInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerInclusion p

/-- Inductive definition of being equal to the coherent iso -/
inductive CoherentIsoInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk : CoherentIsoInclusion (coherentIso.pt .zero)

/-- The class of the inclusion into the coherent iso as a MorphismProperty -/
def IsCoherentIso : MorphismProperty SSet := fun _ _ p ↦ CoherentIsoInclusion p

/-- The union of inner horn inclusions and inclusion into coherent iso -/
def InnerIsoInclusion {X Y : SSet} (p : X ⟶ Y) : Prop :=
  (InnerInclusions p) ∨ IsCoherentIso p

/-- The union of the class of inner horn inclusions and the inclusion into coherent iso 
  as a MorphismProperty -/
def InnerIsoInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerIsoInclusion p

/-- Definition of isofibration: An isofibration of quasi-categories is a morphism that
has the rlp wrt inner horn inclusions and the inclusion into the walking coherent iso. -/
def isoFibration : MorphismProperty SSet := fun _ _ p ↦ InnerIsoInclusions.rlp p

end isoFibration

end SSet
