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

def map3'_1 : ([1] : SimplexCategory) ⟶ [0] := SimplexCategory.const [1] [0] 0
def map3'_1' : Δ[1] ⟶ Δ[0] := SSet.standardSimplex.map map3'_1
def map3'_2 : Δ[0] ⟶ Δ[0] ⨿ Δ[0] := sorry

def map3' : Δ[1] ⟶ Δ[0] ⨿ Δ[0] := by sorry
def map3'' : Δ[1] ⟶ Δ[0] ⨿ Δ[0] := by sorry

noncomputable def map3 : (Δ[1] ⨿ Δ[1] ⟶ Δ[0] ⨿ Δ[0] : Type u) :=
  Limits.coprod.desc map3' map3''

def map4 : (Δ[1] ⨿ Δ[1] ⟶ Sq : Type u) := by sorry

noncomputable def Iso' := Limits.pushout map3 map4

#check Limits.coprod Δ[1] Δ[1]

open SimplexCategory

#check SSet.yonedaEquiv Δ[2] [1] |>.invFun (SSet.standardSimplex.edge 2 1 2 (by simp only [Nat.reduceAdd,
  Fin.isValue, Fin.reduceLE]))
-- #check yoneda.map (SSet.standardSimplex.edge 2 1 2 (by simp only [Nat.reduceAdd, Fin.isValue, Fin.reduceLE]))

#check SSet.yonedaEquiv
#check SSet.standardSimplex.map_id
