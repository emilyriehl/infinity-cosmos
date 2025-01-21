import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso

open CategoryTheory Simplicial SSet standardSimplex Limits

universe u

/-- Defines a map between standard simplices by using the definin property of -/
def mapFromSimplex {n m : ℕ} (simplex : Δ[n] _[m]) : Δ[m] ⟶ Δ[n] :=
    SSet.yonedaEquiv Δ[n] [m] |>.invFun simplex

/-- The edge in Δ[2] from vertex 1 to 2 -/
def chain12 : Δ[1] ⟶ Δ[2] := mapFromSimplex (edge 2 1 2 (by decide))

/-- The edge in Δ[2] from vertex 0 to 1 -/
def chain01 : Δ[1] ⟶ Δ[2] := mapFromSimplex (edge 2 0 1 (by decide))

/-- The pushout of the diagram
  Δ[1] --> Δ[2]
   |        |
   |        |
   v        v
  Δ[2] -->  Sq
representing commutative squares -/
noncomputable def Sq := pushout chain12 chain01

/-- The map X ⨿ Y ⟶ Z ⨿ W defined by maps X ⟶ Z and Y ⟶ W -/
noncomputable def mapOnComponents {C} [Category C] {X Y Z W : C} [HasColimits C] (f : X ⟶ Z) (g : Y ⟶ W)
    : (X ⨿ Y ⟶ Z ⨿ W : Type u) := coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr)

/-- the constant map of any Δ[n] into Δ[0] corresponding to the unique degenerate n-simplex -/
def constantMap (n : ℕ) : Δ[n] ⟶ Δ[0] := mapFromSimplex (const 0 0 _)

noncomputable def map0Plus0 : (Δ[1] ⨿ Δ[1] ⟶ Δ[0] ⨿ Δ[0] : Type u) :=
  mapOnComponents (constantMap 1) (constantMap 1)

/--
The map Δ[1] ⨿ Δ[1] defined by the the maps

     chain01          ι₁
Δ[1] -------> Δ[2] -------> Sq

     chain01          ι₂
Δ[1] -------> Δ[2] -------> Sq
-/
noncomputable def map1 : (Δ[1] ⨿ Δ[1] ⟶ Sq : Type u) :=
    coprod.desc (chain01 ≫ (pushout.inl chain12 chain01)) (chain01 ≫ (pushout.inr chain12 chain01))

/-- The 0-simplex at vertex 0 of Δ[1] -/
def chain0 : Δ[0] ⟶ Δ[1] := mapFromSimplex (const 1 0 (Opposite.op [0]))

/-- The 0-simplex at vertex 1 of Δ[1] -/
def chain1 : Δ[0] ⟶ Δ[1] := mapFromSimplex (const 1 1 (Opposite.op [0]))

/--
The pushout of the diagram

                      map4
      Δ[1] ⨿ Δ[1] ---------> Sq
           |                 |
 map0Plus0 |                 |
           v                 v
      Δ[0] ⨿ Δ[0] -----> firstEquiv

-/
noncomputable def firstEquiv := pushout map1 map0Plus0

/--
The pushout of the diagram

    Δ[0] -----> Δ[1]
     |           |
     |           |
     v           v
    Δ[1] ---> Cospan00
-/
noncomputable def Cospan00 := pushout chain0 chain0

/--
The pushout of the diagram

        ι₁
  Δ[0] ---> Δ[1] --> Cospan00
   |                    |
   |                    |
   v                    v
  Δ[1] ------------> Cospan0011

-/
noncomputable def Cospan0011 := pushout (chain1 ≫ (pushout.inl chain0 chain0)) chain1

/--
The map Cospan00 ----> Δ[3] defined by the map on component

edge₁₂ : Δ[1] -----> Δ[3]

edge₁₃ : Δ[1] -----> Δ[3]
-/
noncomputable def map2 : (Cospan00 ⟶ Δ[3]: Type u) :=
  pushout.desc (mapFromSimplex (edge 3 1 2 (by decide))) (mapFromSimplex (edge 3 1 3 (by decide))) rfl

/--
The map Cospan0011 ⟶ Δ[3] defined by the map on components

map3 : Cospan00 -----> Δ[3]

edge₀₂ : Δ[1] -------> Δ[3]
-/
noncomputable def map3 : (Cospan0011 ⟶ Δ[3] : Type u) :=
  pushout.desc map2 (mapFromSimplex (edge 3 0 2 (by decide))) (by ext; unfold map2; aesop_cat)

/--
The map Cospan00 ⟶ Δ[1] defined by the map on components

edge₀₁: Δ[1] ----> Δ[1]
edge₀₀: Δ[1] ----> Δ[1]
-/
noncomputable def map4 : (Cospan00 ⟶ Δ[1] : Type u) :=
  pushout.desc (mapFromSimplex (edge 1 0 1 (by decide))) (mapFromSimplex (edge 1 0 0 (by decide))) rfl

/--
The map Cospan0011 ⟶ Δ[1] defined by the map on components

map4: Cospan00 -----> Δ[1]
edge₁₁: Δ[1] ------> Δ[1] -- TODO: Is this right? This seems like a degenerate edge
-/
noncomputable def map5 : (Cospan0011 ⟶ Δ[1] : Type u) :=
  pushout.desc map4 (mapFromSimplex (edge 1 1 1 (by decide))) (by ext; unfold map4; aesop_cat)

/--
The pushout of the diagram

             map3
  Cospan0011 ----> Δ[3]
     |              |
map6 |              |
     |              |
     v              v
    Δ[1] -----> secondEquiv
-/
noncomputable def secondEquiv := pushout map3 map5

noncomputable def someMap : secondEquiv ⟶ coherentIso :=
  pushout.desc
  -- Δ[3] ---> coherentIso
  (yonedaEquiv _ _ |>.invFun {
      obj := λ
      | 0 => WalkingIso.one
      | 1 => WalkingIso.zero
      | 2 => WalkingIso.one
      | 3 => WalkingIso.zero
      map := λ _ => Unit.unit
      map_comp := λ _  _ => rfl
      map_id := λ _ => rfl })
  -- Δ[1] ---> coherentIso
  (yonedaEquiv _ _ |>.invFun {
      obj := λ
        | 0 => WalkingIso.zero
        | 1 => WalkingIso.one
      map := fun _ => Unit.unit
      map_comp := λ _ _ => rfl
      map_id := λ _ => rfl })
  (by
    apply CategoryTheory.Limits.colimit.hom_ext
    intro j
    rcases j with (_ | (_ | _)) <;> simp [map1, map2, map3, map4, map5, chain1, SSet.coherentIso]
    -- none
    · rfl
    -- left
    · apply CategoryTheory.Limits.colimit.hom_ext
      intros j
      rcases j with (_ | (_ | _))
      · aesop
      · apply (SSet.coherentIso.yonedaEquiv [1]).injective
        sorry
      · sorry
    -- right
    · apply (SSet.yonedaEquiv SSet.coherentIso [1]).injective
      sorry)

noncomputable def someMap' : firstEquiv ⟶ secondEquiv :=
  pushout.desc
    -- chain01 ---> secondEquiv
    (pushout.desc
      -- Δ[2] ---> secondEquiv
      ((yonedaEquiv _ _ |>.invFun (triangle 0 1 2 (by decide) (by decide))) ≫ (pushout.inl map3 map5))
      -- Δ[2] ---> secondEquiv
      ((yonedaEquiv _ _ |>.invFun (triangle 1 2 3 (by decide) (by decide))) ≫ (pushout.inl map3 map5))
      (sorry))
    -- Δ[0] ⨿ Δ[0] ---> seconEquiv
    (coprod.desc
      -- Δ[0] ---> secondEquiv
     ((yonedaEquiv Δ[3] [0] |>.invFun (const 3 1 (Opposite.op [0]))) ≫ (pushout.inl map3 map5))
      -- Δ[0] ---> secondEquiv
     ((yonedaEquiv Δ[3] [0] |>.invFun (const 3 2 (Opposite.op [0]))) ≫ (pushout.inl map3 map5)))
   (sorry)
    -- apply CategoryTheory.Limits.colimit.hom_ext
    -- intro j
    -- simp [map3, map5]
    -- aesop_cat)
