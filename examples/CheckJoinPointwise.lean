import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join

open CategoryTheory Simplicial Opposite Limits

universe u

namespace SSet

example (X Y : SSet.{u}) (n : ℕ) : joinDiagram' X Y n = joinDiagram X Y n := rfl

#check colimitJoinIso
#check joinObjEquiv
#check joinObjMap_injective
#check join_mono_of_joinObjEquiv
#check hcompat
#check join_mono
#check leibnizJoin_mono_of_pullback

#print axioms SSet.colimitJoinIso
#print axioms SSet.joinObjEquiv
#print axioms SSet.joinObjMap_injective
#print axioms SSet.join_mono_of_joinObjEquiv
#print axioms SSet.hcompat
#print axioms SSet.join_mono
#print axioms SSet.leibnizJoin_mono_of_pullback

end SSet
