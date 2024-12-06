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

-- This seems to be the direct definition so does that really need a separate def?
def simplexmap_from_fin {n m : ℕ} (map_on_fin : Fin (m + 1) →o Fin (n + 1)) : ([m] : SimplexCategory) ⟶ [n] := SimplexCategory.mkHom map_on_fin

#check SSet.asOrderHom

#check ULift
-- I would have expected this to be around , but also didn't find it.
-- I think if it really merits a proof, it shouldn't be here and in fact could be a lemma?
def simplex_from_map {n m : ℕ} (map : ([m] : SimplexCategory) ⟶ [n]) : Δ[n] _[m] := .up map

#check SSet

-- This definition again feels like overkill to me?
def map_from_simplex {n m : ℕ} (simplex : Δ[n] _[m]) : Δ[m] ⟶ Δ[n] := SSet.yonedaEquiv Δ[n] [m] |>.invFun simplex

#check SSet.standardSimplex.const 0 0

#check SSet.standardSimplex.prod'

#check OrderHom.const (Fin 1) (β := Fin 0) ⟨0, _⟩

-- map00p00 should probably better be map00plus00
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
noncomputable def map4 : (Δ[1] ⨿ Δ[1] ⟶ Sq : Type u) :=
  coprod.desc (chain01 ≫ (Limits.pushout.inl chain12 chain01)) (chain01 ≫ (Limits.pushout.inr chain12 chain01))

def chain0 : Δ[0] ⟶ Δ[1] :=
  SSet.yonedaEquiv Δ[1] [0] |>.invFun
   (SSet.standardSimplex.const 1 0 (Opposite.op [0]))

def chain1 : Δ[0] ⟶ Δ[1] :=
  SSet.yonedaEquiv Δ[1] [0] |>.invFun
   (SSet.standardSimplex.const 1 1 (Opposite.op [0]))

noncomputable def firstEquiv := Limits.pushout map4 map00p00

#check Limits.WidePullbackShape.wideCospan

abbrev J := Fin 3

noncomputable def Cospan00 := Limits.pushout chain0 chain0

noncomputable def Cospan0011 := Limits.pushout (chain1 ≫ (Limits.pushout.inl chain0 chain0)) chain1


#check chain1 ≫ (Limits.pushout.inl chain0 chain0)

-- Need to find an effective way to define this.
open Limits in
noncomputable def map5 : (Cospan0011 ⟶ Δ[3] : Type u) := by
  refine pushout.desc ?_ ?_ ?_
  · refine pushout.desc ?_ ?_ ?_
    · exact SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.edge 3 1 2 (by decide))
    · exact SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.edge 3 1 3 (by decide))
    · rfl
  · exact SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.edge 3 0 2 (by decide))
  · ext
    aesop_cat

open Limits in
noncomputable def map6 : (Cospan0011 ⟶ Δ[1] : Type u) := by
  refine pushout.desc ?_ ?_ ?_
  · refine pushout.desc ?_ ?_ ?_
    · exact SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.edge 1 0 1 (by decide))
    · exact SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.edge 1 0 0 (by decide))
    · rfl
  · exact SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.edge 1 1 1 (by decide))
  · ext
    aesop_cat

noncomputable def secondEquiv := Limits.pushout map5 map6

open Limits in
noncomputable def someMap : secondEquiv ⟶ SSet.coherentIso := by
-- Why do the following four lines generate an error?
  refine pushout.desc ?_ ?_ ?_
  · sorry
  · sorry
  · sorry

open Limits in
noncomputable def someMap' : firstEquiv ⟶ secondEquiv := by
refine pushout.desc ?_ ?_ ?_
· refine pushout.desc ?_ ?_ ?_
  · exact (SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.triangle 0 1 2 (by decide) (by decide))) ≫ (Limits.pushout.inl map5 map6)
  · exact (SSet.yonedaEquiv _ _ |>.invFun (SSet.standardSimplex.triangle 1 2 3 (by decide) (by decide))) ≫ (Limits.pushout.inl map5 map6)
  · sorry --tried aeasop_cat didn't work
· refine coprod.desc ?_ ?_
  · exact ((SSet.yonedaEquiv Δ[3] [0] |>.invFun (SSet.standardSimplex.const 3 1 (Opposite.op [0]))) ≫ (Limits.pushout.inl map5 map6))
  · exact ((SSet.yonedaEquiv Δ[3] [0] |>.invFun (SSet.standardSimplex.const 3 2 (Opposite.op [0]))) ≫ (Limits.pushout.inl map5 map6))
· sorry


#check evaluation

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
