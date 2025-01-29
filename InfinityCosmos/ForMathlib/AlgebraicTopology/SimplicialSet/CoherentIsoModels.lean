import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso

open CategoryTheory Simplicial SSet stdSimplex Limits

universe u


-- We work in the simplex category Δ.
-- By the Yoneda lemma every morphism Δ[m] ⟶ Δ[n] uniquely corresponds to an ordered map
-- [m] ⟶ [n], which is uniquely determined by a chain of integers 0 ≤ i₀ < i₁ < ... < iₘ ≤ n.
-- We denote the induced map deltai₀i₁ ... iₘ:Δ[m] ⟶ Δ[n].

/-- Defines a map between standard simplices by using the defining property of representable functors -/
def mapFromSimplex {n m : ℕ} (simplex : Δ[n] _[m]) : Δ[m] ⟶ Δ[n] :=
    SSet.yonedaEquiv Δ[n] [m] |>.invFun simplex

/-- The edge in Δ[2] from vertex 1 to 2 -/
def delta12 : Δ[1] ⟶ Δ[2] := mapFromSimplex (edge 2 1 2 (by decide))
def delta12' : Δ[1] ⟶ Δ[2] := stdSimplex.δ 0 --TODO: Figure out if this is a better way to define

/-- The edge in Δ[2] from vertex 0 to 1 -/
def delta01 : Δ[1] ⟶ Δ[2] := mapFromSimplex (edge 2 0 1 (by decide))
def delta01' : Δ[1] ⟶ Δ[2] := stdSimplex.δ 2 --TODO: Figure out if this is a better way to define

/-- The pushout of the diagram
  Δ[1] --> Δ[2]
   |        |
   |        |
   v        v
  Δ[2] -->  Sq
representing the following square shaped diagram:
   0  -----> 1
   |      /  |
   |     /   |
   |    /    |
   |   /     |
   |  /      |
   v L       v
   2 ------> 3
 -/
noncomputable def Sq := pushout delta12 delta01
noncomputable def Sq' := pushout (stdSimplex.δ 0 : Δ[1] ⟶ Δ[2]) (stdSimplex.δ 2 : Δ[1] ⟶ Δ[2])

/-- The map X ⨿ Y ⟶ Z ⨿ W defined by maps X ⟶ Z and Y ⟶ W -/
noncomputable def mapOnComponents {C} [Category C] {X Y Z W : C} [HasColimits C] (f : X ⟶ Z) (g : Y ⟶ W)
    : (X ⨿ Y ⟶ Z ⨿ W : Type u) := coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr)

/-- The constant map of any Δ[n] into Δ[0] corresponding to the unique degenerate n-simplex -/
def constantMap (n : ℕ) : Δ[n] ⟶ Δ[0] := mapFromSimplex (const 0 0 _)
def constantMap' (n : ℕ) : Δ[n] ⟶ Δ[0] := stdSimplex.map (SimplexCategory.const _ _ 0)

noncomputable def map0Coprod0 : (Δ[1] ⨿ Δ[1] ⟶ Δ[0] ⨿ Δ[0] : Type u) :=
  mapOnComponents (constantMap 1) (constantMap 1)
noncomputable def map0Coprod0' : (Δ[1] ⨿ Δ[1] ⟶ Δ[0] ⨿ Δ[0] : Type u) :=
  coprod.map
    (stdSimplex.map (SimplexCategory.const _ _ 0)) (stdSimplex.map (SimplexCategory.const _ _ 0))

/--
The map Δ[1] ⨿ Δ[1] defined by the two maps

     delta01          ι₁
Δ[1] -------> Δ[2] -------> Sq

     delta12          ι₂
Δ[1] -------> Δ[2] -------> Sq
-/
-- ER: Warning: this is wrong: replace the lefthand instances of delta01 with delta02!
noncomputable def map01Coprod34 : (Δ[1] ⨿ Δ[1] ⟶ Sq : Type u) :=
  coprod.desc (delta01 ≫ (pushout.inl delta12 delta01)) (delta01 ≫ (pushout.inr delta12 delta01))
noncomputable def map01Coprod34' : (Δ[1] ⨿ Δ[1] ⟶ Sq' : Type u) :=
  coprod.desc
    ((stdSimplex.δ 1) ≫ (pushout.inl (stdSimplex.δ 0) (stdSimplex.δ 2)))
    ((stdSimplex.δ 1) ≫ (pushout.inr (stdSimplex.δ 0) (stdSimplex.δ 2)))

/--
The pushout of the diagram

                 map01Coprod34
      Δ[1] ⨿ Δ[1] ---------> Sq
           |                 |
 map0Plus0 |                 |
           v                 v
      Δ[0] ⨿ Δ[0] ---> Model2dCoherentIso
which we can visualize as the following square
   0  -----> 1
  ||      /  ||
  ||     /   ||
  ||    /    ||
  ||   /     ||
  ||  /      ||
   v L       v
   2 ------> 3
   meaning we can recognize the map from 1 to 2 having a left and right inverse.
-/
noncomputable def Model2dCoherentIso := pushout map01Coprod34 map0Coprod0
noncomputable def Model2dCoherentIso' := pushout map01Coprod34' map0Coprod0'

noncomputable def map2dModel'toCoherentIso : Model2dCoherentIso' ⟶ coherentIso := by
  refine pushout.desc ?_ ?_ ?_
  · refine pushout.desc ?_ ?_ ?_
    · exact (coherentIso.twoSimplex WalkingIso.zero WalkingIso.one WalkingIso.zero)
    · exact (coherentIso.twoSimplex WalkingIso.one WalkingIso.zero WalkingIso.one)
    · rw [coherentIso.twoSimplex_δ0 WalkingIso.zero WalkingIso.one WalkingIso.zero]
      rw [← coherentIso.twoSimplex_δ2 WalkingIso.one WalkingIso.zero WalkingIso.one]
  · exact coprod.desc (coherentIso.pt WalkingIso.zero) (coherentIso.pt WalkingIso.one)
  · unfold map0Coprod0' map01Coprod34'
    apply coprod.hom_ext
    · simp only [coprod.desc_comp, Category.assoc, colimit.ι_desc, PushoutCocone.mk_pt,
        PushoutCocone.mk_ι_app, BinaryCofan.ι_app_left, BinaryCofan.mk_inl, coprod.map_desc]
      rw [coherentIso.twoSimplex_δ1 _ _ _, ← coherentIso.oneSimplex_const]
    · simp only [coprod.desc_comp, Category.assoc, colimit.ι_desc,
        PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
        BinaryCofan.mk_pt, BinaryCofan.ι_app_right, BinaryCofan.mk_inr, coprod.map_desc]
      rw [coherentIso.twoSimplex_δ1 _ _ _, ← coherentIso.oneSimplex_const]

/-- The 0-simplex at vertex 0 of Δ[1] -/
def delta0 : Δ[0] ⟶ Δ[1] := mapFromSimplex (const 1 0 (Opposite.op [0]))
def delta0' : Δ[0] ⟶ Δ[1] := stdSimplex.δ 1

/-- The 0-simplex at vertex 1 of Δ[1] -/
def delta1 : Δ[0] ⟶ Δ[1] := mapFromSimplex (const 1 1 (Opposite.op [0]))
def delta1' : Δ[0] ⟶ Δ[1] := stdSimplex.δ 0

/--
The pushout of the diagram

            delta0
       Δ[0] -----> Δ[1]
        |           |
 delta0 |           |
        v           v
       Δ[1] ---> Cospan00
representing the diagram
   1 <--- 0 ---> 1
-/
noncomputable def Cospan00 := pushout delta0 delta0
noncomputable def Cospan00' := pushout delta0' delta0'

/--
The pushout of the diagram

            delta1     ι₁
        Δ[0] ---> Δ[1] --> Cospan00
         |                    |
  delta1 |                    |
         v                    v
        Δ[1] ------------> Cospan0011
representing the diagram
   1 <--- 0 ---> 1 <--- 0
-/
noncomputable def Cospan0011 := pushout (delta1 ≫ (pushout.inl delta0 delta0)) delta1

/--
The map Cospan00 ----> Δ[3] defined by the map on component

delta12 : Δ[1] -----> Δ[3]

delta13 : Δ[1] -----> Δ[3]

It corresponds to the diagram
    3 <--- 1 ---> 2
inside Δ[3]
-/
noncomputable def map12Coprod13 : (Cospan00 ⟶ Δ[3]: Type u) :=
  pushout.desc (mapFromSimplex (edge 3 1 2 (by decide))) (mapFromSimplex (edge 3 1 3 (by decide))) rfl

/--
The map Cospan0011 ⟶ Δ[3] defined by the map on components

map12Coprod13 : Cospan00 -----> Δ[3]

delta02 : Δ[1] -------> Δ[3]

It corresponds to the diagram
    3 <--- 1 ---> 2 <--- 0
inside Δ[3]
-/
noncomputable def map12Coprod13Coprod02 : (Cospan0011 ⟶ Δ[3] : Type u) :=
  pushout.desc map12Coprod13 (mapFromSimplex (edge 3 0 2 (by decide))) (by ext; unfold map12Coprod13; aesop_cat)

/--
The map Cospan00 ⟶ Δ[1] defined by the map on components

delta01: Δ[1] ----> Δ[1]
delta00: Δ[1] ----> Δ[1]

It corresponds to the diagram
    0 <--- 0 ---> 1
inside Δ[1]
-/
noncomputable def map01Coprod00 : (Cospan00 ⟶ Δ[1] : Type u) :=
  pushout.desc (mapFromSimplex (edge 1 0 1 (by decide))) (mapFromSimplex (edge 1 0 0 (by decide))) rfl

/--
The map Cospan0011 ⟶ Δ[1] defined by the map on components

map01Coprod00: Cospan00 -----> Δ[1]
delta11: Δ[1] ------> Δ[1]

It corresponds to the diagram
    0 <-=- 0 ---> 1 <-=- 1
inside Δ[1]
-/
noncomputable def map01Coprod00Coprod11 : (Cospan0011 ⟶ Δ[1] : Type u) :=
  pushout.desc map01Coprod00 (mapFromSimplex (edge 1 1 1 (by decide))) (by ext; unfold map01Coprod00; aesop_cat)

/--
The pushout of the diagram

                         map12Coprod13Coprod02
                   Cospan0011 ----------> Δ[3]
                      |                     |
map01Coprod00Coprod11 |                     |
                      |                     |
                      v                     v
                     Δ[1] -----------> secondEquiv
-/
noncomputable def Model3dCoherentIso := pushout map12Coprod13Coprod02 map01Coprod00Coprod11

noncomputable def map3dModeltoCoherentIso : Model3dCoherentIso ⟶ coherentIso :=
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
    rcases j with (_ | (_ | _)) <;> simp [map01Coprod34, map12Coprod13, map12Coprod13Coprod02, map01Coprod00, map01Coprod00Coprod11, delta1, SSet.coherentIso]
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

noncomputable def map2dModelto3dModel : Model2dCoherentIso ⟶ Model3dCoherentIso :=
  pushout.desc
    -- Δ[1] ---> Model3dCoherentIso
    (pushout.desc
      -- Δ[2] ---> Model3dCoherentIso
      ((yonedaEquiv _ _ |>.invFun (triangle 0 1 2 (by decide) (by decide))) ≫ (pushout.inl map12Coprod13Coprod02 map01Coprod00Coprod11))
      -- Δ[2] ---> Model3dCoherentIso
      ((yonedaEquiv _ _ |>.invFun (triangle 1 2 3 (by decide) (by decide))) ≫ (pushout.inl map12Coprod13Coprod02 map01Coprod00Coprod11))
      (sorry))
    -- Δ[0] ⨿ Δ[0] ---> Model3dCoherentIso
    (coprod.desc
      -- Δ[0] ---> Model3dCoherentIso
     ((yonedaEquiv Δ[3] [0] |>.invFun (const 3 1 (Opposite.op [0]))) ≫ (pushout.inl map12Coprod13Coprod02 map01Coprod00Coprod11))
      -- Δ[0] ---> Model3dCoherentIso
     ((yonedaEquiv Δ[3] [0] |>.invFun (const 3 2 (Opposite.op [0]))) ≫ (pushout.inl map12Coprod13Coprod02 map01Coprod00Coprod11)))
   (sorry)
    -- apply CategoryTheory.Limits.colimit.hom_ext
    -- intro j
    -- simp [map3, map5]
    -- aesop_cat)
