/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Dagur Asgeirsson, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

section Definitions

variable {J : Type u₁} [Category.{v₁} J]
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/--
Mirrors `LimitCone F`.
-/
structure ConicalLimitCone (F : J ⥤ C) where
  limitCone : LimitCone F
  isConicalLimit (X : C) : IsLimit <| (eCoyoneda V X).mapCone limitCone.cone

end Definitions

section Results

variable {J : Type u₁} [Category.{v₁} J] {J' : Type u₂} [Category.{v₂} J']
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

namespace HasConicalLimit

variable {C} (F : J ⥤ C) [HasConicalLimit V F]

/-- ensure existence of a conical limit implies existence of a limit -/
example : HasLimit F := inferInstance

/-- Use the axiom of choice to extract explicit `ConicalLimitCone F` from `HasConicalLimit F`. -/
noncomputable def getConicalLimitCone : ConicalLimitCone V F where
  limitCone := getLimitCone F
  isConicalLimit X := Classical.choice <|
    (preservesLimit_eCoyoneda X).preserves (getLimitCone F).isLimit

/-- An arbitrary choice of conical limit cone for a functor. -/
noncomputable def conicalLimitCone : ConicalLimitCone V F := getConicalLimitCone V F

/-- An arbitrary choice of conical limit object of a functor. -/
noncomputable def conicalLimit : C := (conicalLimitCone V F).limitCone.cone.pt

namespace conicalLimit

/-- The projection from the conical limit object to a value of the functor. -/
protected noncomputable def π (j : J) : conicalLimit V F ⟶ F.obj j :=
  (conicalLimitCone V F).limitCone.cone.π.app j

@[reassoc (attr := simp)]
protected theorem w {j j' : J} (f : j ⟶ j') :
    conicalLimit.π V F j ≫ F.map f = conicalLimit.π V F j' :=
  (conicalLimitCone V F).limitCone.cone.w f

end conicalLimit

end HasConicalLimit

namespace HasConicalLimitsOfSize

/-- A category that has larger conical limits also has smaller conical limits. -/
lemma of_univLE [HasConicalLimitsOfSize.{v₁, u₁} V C] [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}] :
    HasConicalLimitsOfSize.{v₂, u₂} V C where
  hasConicalLimitsOfShape J :=
    HasConicalLimitsOfShape.of_equiv V C
      ((ShrinkHoms.equivalence.{v₁} J).trans (Shrink.equivalence _)).inverse

/-- `shrink.{v, u} C` tries to obtain `HasConicalLimitsOfSize.{v, u} C`
from some other `HasConicalLimitsOfSize.{v₁, u₁} C`.
-/
theorem shrink [HasConicalLimitsOfSize.{max v₁ v₂, max u₁ u₂} V C] :
    HasConicalLimitsOfSize.{v₁, u₁} V C :=
  of_univLE.{max v₁ v₂, max u₁ u₂} V C

end HasConicalLimitsOfSize

end Results

end CategoryTheory.Enriched
