import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso

open CategoryTheory Simplicial

universe u

def map1 : (Δ[1] ⟶ Δ[2] : Type u) :=
  SSet.yonedaEquiv Δ[2] [1] |>.invFun
   (SSet.standardSimplex.edge 2 1 2
     (by simp only [Nat.reduceAdd, Fin.isValue, Fin.reduceLE]))

def map2 : (Δ[1] ⟶ Δ[2] : Type u) :=
  SSet.yonedaEquiv Δ[2] [1] |>.invFun
   (SSet.standardSimplex.edge 2 0 1
     (by simp only [Nat.reduceAdd, Fin.isValue, Fin.reduceLE]))

noncomputable def Sq := Limits.pushout map1 map2

#check Limits.coprod.desc

open Limits in
noncomputable def map_on_components {C} [Category C] {X Y Z W : C} [HasColimits C] (f : X ⟶ Z) (g : Y ⟶ W)
    : (X ⨿ Y ⟶ Z ⨿ W : Type u) := coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr)

#check CategoryTheory.opOp_obj
#check SSet.standardSimplex.objEquiv [1] (Opposite.op [0]) |>.toFun (SSet.standardSimplex.const 1 0 (Opposite.op [0]))

def asdfasdf {n m : ℕ} (map_on_fin : Fin (m + 1) →o Fin (n + 1)) : ([m] : SimplexCategory) ⟶ [n] := SimplexCategory.mkHom map_on_fin

#check SSet.asOrderHom

def simplex_from_map {n m : ℕ} (map : ([m] : SimplexCategory) ⟶ [n]) : Δ[n] _[m] := by
  refine SSet.standardSimplex.objMk ?_
  refine ?f.toOrdHom
  unfold SimplexCategory.smallCategory at map
  unfold SimplexCategory.Hom at map
  simp at map
  exact map

def map_from_simplex {n m : ℕ} (simplex : Δ[n] _[m]) : Δ[m] ⟶ Δ[n] := SSet.yonedaEquiv Δ[n] [m] |>.invFun simplex

#check SSet.standardSimplex.const 0 0

#check SSet.standardSimplex.prod'

noncomputable def map3 : (Δ[1] ⨿ Δ[1] ⟶ Δ[0] ⨿ Δ[0] : Type u) := by
  refine map_on_components ?_ ?_
  · sorry
  · sorry

#check Limits.pushout

open Limits in
noncomputable def map4 : (Δ[1] ⨿ Δ[1] ⟶ Sq : Type u) := by
  refine coprod.desc ?_ ?_
  · unfold Sq
    sorry
  · sorry

noncomputable def Iso' := Limits.pushout map3 map4

#check Limits.coprod Δ[1] Δ[1]

open SimplexCategory

#check SSet.yonedaEquiv Δ[2] [1] |>.invFun (SSet.standardSimplex.edge 2 1 2 (by simp only [Nat.reduceAdd,
  Fin.isValue, Fin.reduceLE]))
-- #check yoneda.map (SSet.standardSimplex.edge 2 1 2 (by simp only [Nat.reduceAdd, Fin.isValue, Fin.reduceLE]))

#check SSet.yonedaEquiv
#check SSet.standardSimplex.map_id
