import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Limits

namespace CategoryTheory

namespace SimplicialCategory

universe u v

open Limits

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- `X` is conical terminal if the cone it induces on the empty diagram is a conical limit cone. -/
abbrev IsConicalTerminal (T : C) := IsSLimit (asEmptyCone T)

/-- A conical terminal object is also terminal.-/
def IsConicalTerminal.isTerminal {T : C} (hT : IsConicalTerminal T) : IsTerminal T := hT.isLimit

/-- The defining universal property of a conical terminal object gives an isomorphism of homs.-/
noncomputable def IsConicalTerminal.sHomIso {T : C} (hT : IsConicalTerminal T)
    (X : C) : sHom X T ≅ ⊤_ SSet :=
  limitComparisonIso _ X hT ≪≫
    HasLimit.isoOfEquivalence (by rfl) (Functor.emptyExt _ _)

/-- Transport a term of type `IsConicalTerminal` across an isomorphism. -/
noncomputable def IsConicalTerminal.ofIso {Y Z : C} (hY : IsConicalTerminal Y)
    (i : Y ≅ Z) : IsConicalTerminal Z :=
  hY.ofIsoSLimit <| Cones.ext i (by simp)

namespace HasConicalTerminal
variable [HasConicalTerminal C]

variable (C) in
noncomputable def conicalTerminal : C := conicalLimit (Functor.empty.{0} C)

noncomputable def conicalTerminalIsConicalTerminal :
    IsConicalTerminal (conicalTerminal C) :=
  conicalLimit.isConicalLimit _ |>.ofIsoSLimit <| Cones.ext (by rfl) (by simp)

noncomputable def terminalIsConicalTerminal {T : C} (hT : IsTerminal T) :
    IsConicalTerminal T := by
  let TT := conicalLimit (Functor.empty.{0} C)
  let slim : IsConicalTerminal TT := conicalTerminalIsConicalTerminal
  let lim : IsTerminal TT := IsConicalTerminal.isTerminal slim
  exact IsConicalTerminal.ofIso slim (hT.uniqueUpToIso lim).symm

end HasConicalTerminal

end SimplicialCategory

end CategoryTheory
