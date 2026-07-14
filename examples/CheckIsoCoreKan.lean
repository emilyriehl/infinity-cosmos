import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCoreKan

open CategoryTheory Simplicial

namespace SSet

#check IsoCoreOuterHornFiller
#check kanComplex_isoCore
#check coherentIso.lift_of_isoCore_outerHornFiller

example {A : SSet} [Quasicategory A] (hOuter : IsoCoreOuterHornFiller A) :
    KanComplex (isoCore A : SSet) :=
  kanComplex_isoCore hOuter

end SSet
