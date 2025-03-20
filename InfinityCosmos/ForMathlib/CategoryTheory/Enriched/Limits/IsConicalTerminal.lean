/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.IsConicalLimit
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.HasConicalTerminal

/-!
# Conical terminal objects in enriched ordinary categories

An object `T` in an enriched ordinary category `C` is a conical terminal object if the empty cone
with summit `T` is a conical limit cone. By `IsConicalTerminal.isTerminal` this implies that `T` is
a terminal object in the underlying ordinary category of `C`. When the ambient enriching category
`V` has a terminal object, this provides a natural family of isomorphisms:

`IsConicalTerminal.eHomIso {T : C} (hT : IsConicalTerminal V T) (X : C) : (X ⟶[V] T) ≅ ⊤_ V`

In general the universal property of being terminal is weaker than the universal property of being
conical terminal, but if `HasConicalTerminal V C` any terminal object in `C` is conical terminal:

`terminalIsConicalTerminal {T : C} (hT : IsTerminal T) : IsConicalTerminal V T `.

TODO: Develop similar API for other conical limit and colimit shapes.
-/

namespace CategoryTheory.Enriched

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
  IsConicalLimit.limitComparisonIso hT X ≪≫
    HasLimit.isoOfEquivalence (by rfl) (Functor.emptyExt _ _)

variable {V} in

/-- Transport a term of type `IsConicalTerminal` across an isomorphism. -/
noncomputable def IsConicalTerminal.of_iso {Y Z : C} (hY : IsConicalTerminal V Y)
    (i : Y ≅ Z) : IsConicalTerminal V Z :=
  IsConicalLimit.of_iso hY <| Cones.ext i (by simp)

namespace HasConicalTerminal

variable [HasConicalTerminal V C]

open HasConicalLimit

variable (C) in
noncomputable def conicalTerminal : C := conicalLimit V (Functor.empty.{0} C)

noncomputable def conicalTerminalIsConicalTerminal :
    IsConicalTerminal V (conicalTerminal V C) :=
  conicalLimit.isConicalLimit V _ |>.of_iso <| Cones.ext (by rfl) (by simp)

noncomputable def isTerminalIsConicalTerminal {T : C} (hT : IsTerminal T) :
    IsConicalTerminal V T := by
  let TT := conicalLimit V (Functor.empty.{0} C)
  let slim : IsConicalTerminal V TT := conicalTerminalIsConicalTerminal V
  let lim : IsTerminal TT := IsConicalTerminal.isTerminal V slim
  exact IsConicalTerminal.of_iso slim (hT.uniqueUpToIso lim).symm

-- note: `V` implicit because of how this is used in practise, see `Isofibrations.lean`
variable {V} in

/-- The terminal object is a conical terminal object. -/
noncomputable def terminalIsConicalTerminal : IsConicalTerminal V (⊤_ C) :=
  isTerminalIsConicalTerminal V terminalIsTerminal

end HasConicalTerminal

end CategoryTheory.Enriched
