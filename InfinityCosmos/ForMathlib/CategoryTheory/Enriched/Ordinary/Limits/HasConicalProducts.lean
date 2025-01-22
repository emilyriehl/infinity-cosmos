/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Ordinary.Limits.HasConicalLimits

/-!
TODO: module docstring
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C) (c : Cone F)

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalProduct {I : Type w} (f : I → C) := HasConicalLimit V (Discrete.functor f)

instance HasConicalProduct_hasProduct {I : Type w} (f : I → C) [HasConicalProduct V f] :
    HasProduct f := inferInstance

variable (C)

-- TODO: remove this. looks like an `abbrev` works just fine
-- The class needs `V` as `outParam`.
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V] in
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] (F : J ⥤ C) in

/-- Has conical products if all discrete diagrams of bounded size have conical products. -/
class HasConicalProducts : Prop where
  /-- All discrete diagrams of bounded size have conical products. -/
  hasConicalLimitsOfShape : ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) V C := by
    infer_instance

-- -- The class needs `V` as `outParam`.
-- variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V] in
-- variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] (F : J ⥤ C) in

-- abbrev HasConicalProducts := ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) V C

namespace HasConicalProducts

instance hasProducts [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasProducts.{w, v, u} C := by
  intro I
  constructor
  intro f
  have := hyp.hasConicalLimitsOfShape I
  have : HasConicalLimit V f := inferInstance
  infer_instance

end HasConicalProducts

end CategoryTheory.Enriched
