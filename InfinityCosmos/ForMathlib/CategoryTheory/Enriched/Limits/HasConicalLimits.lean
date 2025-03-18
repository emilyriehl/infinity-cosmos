/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
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
