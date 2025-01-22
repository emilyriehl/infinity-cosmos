/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Ordinary.Limits.HasConicalProducts
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Ordinary.Limits.IsConicalTerminal

/-!
TODO: module docstring
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C)

variable [HasConicalLimit V F]

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

instance HasConicalTerminal_hasTerminal [hyp : HasConicalTerminal V C] : HasTerminal C :=
  inferInstance

namespace HasConicalTerminal

variable [HasConicalTerminal V C]

variable (C) in
noncomputable def conicalTerminal : C := conicalLimit V (Functor.empty.{0} C)

noncomputable def conicalTerminalIsConicalTerminal :
    IsConicalTerminal V (conicalTerminal V C) :=
  conicalLimit.isConicalLimit V _ |>.ofIso <| Cones.ext (by rfl) (by simp)

noncomputable def terminalIsConicalTerminal {T : C} (hT : IsTerminal T) :
    IsConicalTerminal V T := by
  let TT := conicalLimit V (Functor.empty.{0} C)
  let slim : IsConicalTerminal V TT := conicalTerminalIsConicalTerminal V
  let lim : IsTerminal TT := IsConicalTerminal.isTerminal V slim
  exact IsConicalTerminal.ofIso slim (hT.uniqueUpToIso lim).symm

end HasConicalTerminal

namespace HasConicalProducts

instance hasConicalTerminal [hyp : HasConicalProducts.{0, v', v, u} V C] :
    HasConicalTerminal V C := by
      exact hyp.hasConicalLimitsOfShape PEmpty.{1}

instance hasConicalTerminal' [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasConicalTerminal V C := by
  have inst := hyp.hasConicalLimitsOfShape PEmpty
  exact hasConicalLimitsOfShape_of_equivalence V (J := Discrete PEmpty.{w + 1}) emptyEquivalence

end HasConicalProducts

end CategoryTheory.Enriched
