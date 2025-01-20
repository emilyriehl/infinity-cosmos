/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dagur Asgeirsson, Jon Eugster
-/
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Ordinary.Limits

namespace CategoryTheory

namespace EnrichedOrdinaryCategory

universe v' v u u'

open Limits

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V] [HasTerminal V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- `X` is conical terminal if the cone it induces on the empty diagram is a conical limit cone. -/
abbrev IsConicalTerminal (T : C) := IsConicalLimit V (asEmptyCone T)

/-- A conical terminal object is also terminal.-/
def IsConicalTerminal.isTerminal {T : C} (hT : IsConicalTerminal V T) : IsTerminal T := hT.isLimit

/-- The defining universal property of a conical terminal object gives an isomorphism of homs.-/
noncomputable def IsConicalTerminal.eHomIso {T : C} (hT : IsConicalTerminal V T)
    (X : C) : (X ⟶[V] T) ≅ ⊤_ V :=
  IsConicalLimit.limitComparisonIso _ X hT ≪≫
    HasLimit.isoOfEquivalence (by rfl) (Functor.emptyExt _ _)

variable {V} in

/-- Transport a term of type `IsConicalTerminal` across an isomorphism. -/
noncomputable def IsConicalTerminal.ofIso {Y Z : C} (hY : IsConicalTerminal V Y)
    (i : Y ≅ Z) : IsConicalTerminal V Z :=
  IsConicalLimit.ofIso hY <| Cones.ext i (by simp)

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

end EnrichedOrdinaryCategory

end CategoryTheory
