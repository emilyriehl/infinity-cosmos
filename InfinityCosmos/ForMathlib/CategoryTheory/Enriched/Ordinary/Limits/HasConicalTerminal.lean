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
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C)

variable [HasConicalLimit V F]

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

instance HasConicalTerminal_hasTerminal [hyp : HasConicalTerminal V C] : HasTerminal C :=
  inferInstance

end CategoryTheory.Enriched
