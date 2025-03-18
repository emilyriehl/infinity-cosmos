/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.IsConicalLimit
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

/-!
# HasConicalLimits

This file contains different statements about the (non-constructive) existence of conical limits.

The main constructions are the following.

- `HasConicalLimit`: there exists a limit `cone` with `IsConicalLimit V cone`
- `HasConicalLimitsOfShape J`: All functors `F : J ⥤ C` have conical limits.
- `HasConicalLimitsOfSize.{v₁, u₁}`: For all small `J` all functors `F : J ⥤ C` have conical limits.
- `HasConicalLimits `: has all (small) conical limits.
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

namespace HasConicalLimit

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable {F : J ⥤ C} (c : Cone F)

variable (F) [HasConicalLimit V F]

/-- Use the axiom of choice to extract explicit `ConicalLimitCone F` from `HasConicalLimit F`. -/
noncomputable def getConicalLimitCone : ConicalLimitCone V F :=
  sorry -- Classical.choice <| HasConicalLimit.exists_conicalLimitCone

/-- An arbitrary choice of conical limit cone for a functor. -/
noncomputable def conicalLimitCone : ConicalLimitCone V F :=
  (getConicalLimitCone V F)

/-- An arbitrary choice of conical limit object of a functor. -/
noncomputable def conicalLimit := (conicalLimitCone V F).cone.pt

namespace conicalLimit

/-- The projection from the conical limit object to a value of the functor. -/
protected noncomputable def π (j : J) : conicalLimit V F ⟶ F.obj j :=
  (conicalLimitCone V F).cone.π.app j

@[reassoc (attr := simp)]
protected theorem w {j j' : J} (f : j ⟶ j') :
    conicalLimit.π V F j ≫ F.map f = conicalLimit.π V F j' := (conicalLimitCone V F).cone.w f

/-- Evidence that the arbitrary choice of cone provided by `(conicalLimitCone V F).cone` is a
conical limit cone. -/
noncomputable def isConicalLimit : IsConicalLimit V (conicalLimitCone V F).cone :=
  (getConicalLimitCone V F).isConicalLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
noncomputable def lift : c.pt ⟶ conicalLimit V F :=
  (conicalLimit.isConicalLimit V F).isLimit.lift c

@[reassoc (attr := simp)]
theorem lift_π (j : J) :
    conicalLimit.lift V F c ≫ conicalLimit.π V F j = c.π.app j :=
  IsLimit.fac _ c j

end conicalLimit

end HasConicalLimit

namespace HasConicalLimitsOfShape

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C)

variable [HasConicalLimitsOfShape J V C]

end HasConicalLimitsOfShape

namespace HasConicalLimitsOfSize

variable {J : Type u₁} [Category.{v₁} J]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

-- This is in PR #23042
/-- A category that has larger conical limits also has smaller conical limits. -/
theorem hasConicalLimitsOfSize_of_univLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [h : HasConicalLimitsOfSize.{v₁, u₁} V C] : HasConicalLimitsOfSize.{v₂, u₂} V C where
  hasConicalLimitsOfShape J := HasConicalLimitsOfShape.of_equiv V C
    ((ShrinkHoms.equivalence J).trans (Shrink.equivalence _)).inverse

-- This is in PR #23042
/-- `HasConicalLimitsOfSize.shrink.{v, u} C` tries to obtain `HasConicalLimitsOfSize.{v, u} C`
from some other `HasConicalLimitsOfSize.{v₁, u₁} C`.
-/
theorem shrink [HasConicalLimitsOfSize.{max v₁ v₂, max u₁ u₂} V C] :
    HasConicalLimitsOfSize.{v₁, u₁} V C :=
  hasConicalLimitsOfSize_of_univLE.{max v₁ v₂, max u₁ u₂} V C

end HasConicalLimitsOfSize
namespace HasConicalLimits

-- Note that `Category.{v, v} J` is deliberately chosen this way, see `HasConicalLimits`.
variable (J : Type v) [Category.{v} J]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable [HasConicalLimits V C]

-- This is in PR #23042
instance (priority := 100) hasSmallestConicalLimitsOfHasConicalLimits :
    HasConicalLimitsOfSize.{0, 0} V C :=
  HasConicalLimitsOfSize.shrink.{0, 0} V C

end HasConicalLimits

end CategoryTheory.Enriched
