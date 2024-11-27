import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

open CategoryTheory Simplicial

universe u

def chain12 : Δ[1] ⟶ Δ[2] :=
  SSet.yonedaEquiv Δ[2] [1] |>.invFun
   (SSet.standardSimplex.edge 2 1 2
     (by decide))

def chain01 : Δ[1] ⟶ Δ[2] :=
  SSet.yonedaEquiv Δ[2] [1] |>.invFun
   (SSet.standardSimplex.edge 2 0 1
     (by decide))

noncomputable def Sq := Limits.pushout chain12 chain01

#check Limits.coprod.desc

open Limits in
noncomputable def map_on_components {C} [Category C] {X Y Z W : C} [HasColimits C] (f : X ⟶ Z) (g : Y ⟶ W)
    : (X ⨿ Y ⟶ Z ⨿ W : Type u) := coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr)

#check CategoryTheory.opOp_obj
#check SSet.standardSimplex.objEquiv [1] (Opposite.op [0]) |>.toFun (SSet.standardSimplex.const 1 0 (Opposite.op [0]))

def simplexmap_from_fin {n m : ℕ} (map_on_fin : Fin (m + 1) →o Fin (n + 1)) : ([m] : SimplexCategory) ⟶ [n] := SimplexCategory.mkHom map_on_fin

#check SSet.asOrderHom

def simplex_from_map {n m : ℕ} (map : ([m] : SimplexCategory) ⟶ [n]) : Δ[n] _[m] := by
  refine SSet.standardSimplex.objMk ?_
  refine ?f.toOrdHom
  unfold SimplexCategory.smallCategory at map
  unfold SimplexCategory.Hom at map
  simp at map
  exact map

#check SSet

def map_from_simplex {n m : ℕ} (simplex : Δ[n] _[m]) : Δ[m] ⟶ Δ[n] := SSet.yonedaEquiv Δ[n] [m] |>.invFun simplex

#check SSet.standardSimplex.const 0 0

#check SSet.standardSimplex.prod'

#check OrderHom.const (Fin 1) (β := Fin 0) ⟨0, _⟩

noncomputable def map00p00 : (Δ[1] ⨿ Δ[1] ⟶ Δ[0] ⨿ Δ[0] : Type u) := by
  refine map_on_components ?_ ?_
  · refine map_from_simplex ?_
    refine simplex_from_map ?_
    refine simplexmap_from_fin ?_
    exact OrderHom.const (Fin 2) ⟨0, by decide⟩
  · refine map_from_simplex ?_
    refine simplex_from_map ?_
    refine simplexmap_from_fin ?_
    exact OrderHom.const (Fin 2) ⟨0, by decide⟩

#check Limits.pushout

#check SSet.yonedaEquiv Sq [1] |>.invFun

#check evaluation

#check Limits.colimit

open Limits in
noncomputable def map4 : (Δ[1] ⨿ Δ[1] ⟶ Sq : Type u) := by
  refine coprod.desc ?_ ?_
  · refine SSet.yonedaEquiv Sq [1] |>.invFun ?_
    refine CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation (Limits.span chain12 chain01) (Opposite.op [1]) |>.toEquiv |>.invFun ?_
    let asdf := CategoryTheory.Limits.Types.colimitEquivQuot (span chain12 chain01 ⋙ evaluation SimplexCategoryᵒᵖ (Type u) _[1])
    refine asdf.invFun ?_
    apply Quot.mk
    refine ⟨.some .left, ?_⟩
    exact SSet.standardSimplex.edge 2 0 1 (by decide)

  · refine SSet.yonedaEquiv Sq [1] |>.invFun ?_
    refine CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation (Limits.span chain12 chain01) (Opposite.op [1]) |>.toEquiv |>.invFun ?_
    let asdf := CategoryTheory.Limits.Types.colimitEquivQuot (span chain12 chain01 ⋙ evaluation SimplexCategoryᵒᵖ (Type u) _[1])
    refine asdf.invFun ?_
    apply Quot.mk
    refine ⟨.some .right, ?_⟩
    exact SSet.standardSimplex.edge 2 1 2 (by decide)

open Limits
#check CategoryTheory.Limits.Types.colimitEquivQuot (span chain12 chain01 ⋙ evaluation SimplexCategoryᵒᵖ (Type u) _[1])
#check Types.Quot
#check WalkingSpan
#check Sigma
#check SSet.standardSimplex.edge

noncomputable def Iso' := Limits.pushout map00p00 map4

#check Limits.coprod Δ[1] Δ[1]

open SimplexCategory

#check SSet.yonedaEquiv Δ[2] [1] |>.invFun (SSet.standardSimplex.edge 2 1 2 (by simp only [Nat.reduceAdd,
  Fin.isValue, Fin.reduceLE]))
-- #check yoneda.map (SSet.standardSimplex.edge 2 1 2 (by simp only [Nat.reduceAdd, Fin.isValue, Fin.reduceLE]))

#check SSet.yonedaEquiv
#check SSet.standardSimplex.map_id

#check Limits.cospan
#check CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation (Limits.cospan chain12 chain01) (Opposite.op [1]) |>.toEquiv |>.invFun
