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

section morphismPropertyTargetQCat

/-- A variation of `MorphismProperty` which assumes the target is a quasicategory. -/
def QCatTargetMorphismProperty :=
  ∀ ⦃X Y : SSet⦄ (_ : X ⟶ Y) [Quasicategory Y], Prop

end morphismPropertyTargetQCat

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

section isoFibration

/-- Inductive definition of inner horn inclusions Λ[n, i] ⟶ Δ[n]
  by restricting general horn inclusions to 0 < i < n -/
inductive InnerHornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (n i : ℕ) (low : 0 < i) (high : i < n) : InnerHornInclusion (hornInclusion n i)

/-- The class of inner horn inclusions as a MorphismProperty -/
def InnerHornInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerHornInclusion p

/-- Inductive definition of being equal to the inclusion Δ[0]
  into coherent iso picking 0 -/
inductive ZeroCoherentIsoInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk : ZeroCoherentIsoInclusion (coherentIso.pt .zero)

/-- Inductive definition of being equal to the inclusion Δ[0]
  into coherent iso picking 1 -/
inductive OneCoherentIsoInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk : OneCoherentIsoInclusion (coherentIso.pt .one)

/-- The class of inclusions equal to the inclusion picking out zero in the
  coherent iso as a MorphismProperty -/
def IsZeroCoherentIsoInclusion : MorphismProperty SSet := fun _ _ p ↦ ZeroCoherentIsoInclusion p

/-- The class of inclusions equal to the inclusion picking out one in the
  coherent iso as a MorphismProperty -/
def IsOneCoherentIsoInclusion : MorphismProperty SSet := fun _ _ p ↦ OneCoherentIsoInclusion p

/-- The union of inner horn inclusions and the two inclusions into coherent iso -/
def InnerIsoInclusion {X Y : SSet} (p : X ⟶ Y) : Prop :=
  (InnerHornInclusions p) ∨ (IsZeroCoherentIsoInclusion p) ∨ (IsOneCoherentIsoInclusion p)

/-- The union of the class of inner horn inclusions and the inclusion into coherent iso
  as a MorphismProperty -/
def InnerIsoInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerIsoInclusion p

/-- Definition of isofibration: A morphism of simplicial sets with target a quasi-category 
  is an isofibration if it satisfies the rlp with wrt the inner horn inclusions and the two 
  endpoint inclusion into the walking coherent iso. -/
def isoFibration : QCatTargetMorphismProperty := fun _ _ p ↦ InnerIsoInclusions.rlp p

end isoFibration

end SSet
