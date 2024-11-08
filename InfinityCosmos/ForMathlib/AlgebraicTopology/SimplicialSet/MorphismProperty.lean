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

section isoFibration

inductive InnerInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (n i : ℕ) (low : 0 < i) (high : i < n) : InnerInclusion (hornInclusion n i)

def InnerInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerInclusion p

inductive CoherentIsoInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk : CoherentIsoInclusion (coherentIso.pt .zero)

def IsCoherentIso : MorphismProperty SSet := fun _ _ p ↦ CoherentIsoInclusion p

def InnerIsoInclusion {X Y : SSet} (p : X ⟶ Y) : Prop :=
  (InnerInclusions p) ∨ IsCoherentIso p

def InnerIsoInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerIsoInclusion p

def isoFibration : MorphismProperty SSet := fun _ _ p ↦ InnerIsoInclusions.rlp p

end isoFibration

end SSet
