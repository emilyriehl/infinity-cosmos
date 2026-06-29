/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Cotensors

/-!
# Naturality of the simplicial cotensor comparison isomorphism

This file records the zero-simplex calculations and naturality squares for the cotensor comparison
isomorphism `cotensor.iso` and its underlying bijection `cotensor.iso.underlying`, together with the
enriched-hom bookkeeping lemmas they rest on. These results are infrastructure shared by the
cosmos-level developments built on the simplicial cotensor; they are separated from the cotensor
definitions in `Cotensors` so that each downstream module imports only the comparison-isomorphism
lemmas it needs.

The two sections below mirror the instance assumptions under which the lemmas are stated: the first
works with an explicit `HasCotensor U A` where one is required, while the second assumes
`HasCotensors K` and concerns the covariant and contravariant cotensor maps.
-/

namespace CategoryTheory

open SimplicialCategory MonoidalCategory BraidedCategory MonoidalClosed

universe v v₁ v₂ u u₁ u₂

namespace SimplicialCategory

open Enriched

section
variable {K : Type u} [Category.{v} K] [SimplicialCategory K]

/-- Ordinary composition, transported to zero-simplices of the enriched hom. -/
lemma homEquiv'_comp {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv' X Z (f ≫ g) =
      ((sHomWhiskerRight f Z).app (Opposite.op (SimplexCategory.mk 0)))
        (homEquiv' Y Z g) := by
  simp [homEquiv', sHomWhiskerRight, eHomEquiv_comp, eHomWhiskerRight, SSet.unitHomEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary composition in the right variable, transported to enriched morphisms. -/
lemma eHomEquiv_comp_eHomWhiskerRight {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet g ≫ eHomWhiskerRight SSet f Z = eHomEquiv SSet (f ≫ g) := by
  apply (SSet.unitHomEquiv (sHom X Z)).injective
  change ((sHomWhiskerRight f Z).app (Opposite.op (SimplexCategory.mk 0)))
      (homEquiv' Y Z g) = homEquiv' X Z (f ≫ g)
  rw [homEquiv'_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Enriched composition is natural in its middle variable. -/
lemma eComp_eHomWhisker_middle {X Y Y' Z : K} (g : Y ⟶ Y') :
    eHomWhiskerLeft SSet X g ▷ sHom Y' Z ≫ eComp SSet X Y' Z =
      sHom X Y ◁ eHomWhiskerRight SSet g Z ≫ eComp SSet X Y Z := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  simp [e_assoc]

/-- The identity morphism, transported to zero-simplices of the enriched hom. -/
lemma homEquiv'_id (X : K) :
    homEquiv' X X (𝟙 X) = ((eId SSet X).app ⟨SimplexCategory.mk 0⟩) PUnit.unit := by
  simp [homEquiv', SSet.unitHomEquiv]

/-- The zero-simplex form of `cotensor.iso.underlying`. -/
lemma cotensor_underlying_homEquiv (U : SSet.{v}) (A X : K) [HasCotensor U A]
    (h : X ⟶ U ⋔ A) :
    homEquiv' U (sHom X A) ((cotensor.iso.underlying U A X) h) =
      (((evaluation SimplexCategoryᵒᵖ (Type v)).obj ⟨SimplexCategory.mk 0⟩).map
        (cotensor.iso U A X).hom) (homEquiv' X (U ⋔ A) h) := by
  change homEquiv' U (sHom X A)
      ((homEquiv' U (sHom X A)).symm
        ((((evaluation SimplexCategoryᵒᵖ (Type v)).obj ⟨SimplexCategory.mk 0⟩).mapIso
          (cotensor.iso U A X)).toEquiv (homEquiv' X (U ⋔ A) h))) =
      (((evaluation SimplexCategoryᵒᵖ (Type v)).obj ⟨SimplexCategory.mk 0⟩).map
        (cotensor.iso U A X).hom) (homEquiv' X (U ⋔ A) h)
  simp

/-- Composition in `SSet`, expressed through the closed structure. -/
lemma homEquiv'_comp_sset_ihom {U V W : SSet.{v}} (i : U ⟶ V) (f : V ⟶ W) :
    homEquiv' U W (i ≫ f) =
      ((eHomEquiv SSet i ≫ (ihom U).map f).app ⟨SimplexCategory.mk 0⟩) PUnit.unit := by
  change (((curry' (i ≫ f)).app ⟨SimplexCategory.mk 0⟩) PUnit.unit) =
    (((curry' i ≫ (ihom U).map f).app ⟨SimplexCategory.mk 0⟩) PUnit.unit)
  rw [curry'_ihom_map]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of a cotensor cone in the representing object. -/
lemma cotensor_coneNatTrans_naturality_left {U : SSet.{v}} {A X Y : K}
    (ux : Cotensor U A) (h : X ⟶ Y) :
    eHomWhiskerRight SSet h ux.obj ≫ ux.coneNatTrans X =
      ux.coneNatTrans Y ≫ (ihom U).map (eHomWhiskerRight SSet h A) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  rw [ux.coneNatTrans_eq, ux.coneNatTrans_eq]
  simp only [Category.assoc]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  rw [← eComp_eHomWhiskerRight]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating a cotensor cone at the identity of its representing object recovers the cone. -/
lemma cotensor_coneNatTrans_eId {U : SSet.{v}} {A : K} (ux : Cotensor U A) :
    eId SSet ux.obj ≫ ux.coneNatTrans ux.obj = curry' ux.cone := by
  apply uncurry'_injective
  change (ρ_ U).inv ≫ uncurry (eId SSet ux.obj ≫ ux.coneNatTrans ux.obj) = ux.cone
  rw [uncurry_natural_left, ux.coneNatTrans_eq]
  rw [braiding_naturality_right_assoc, braiding_tensorUnit_right_assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  rw [e_id_comp, Category.comp_id]

/-- The zero-simplex form of `cotensor_coneNatTrans_eId`. -/
lemma cotensor_coneNatTrans_id {U : SSet.{v}} (A : K) [HasCotensor U A] :
    ((getCotensor U A).coneNatTrans (U ⋔ A)).app ⟨SimplexCategory.mk 0⟩
      (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _)) =
    homEquiv' U (sHom (U ⋔ A) A) (getCotensor U A).cone := by
  rw [homEquiv'_id]
  change (((eId SSet (getCotensor U A).obj ≫
    (getCotensor U A).coneNatTrans (getCotensor U A).obj).app
    ⟨SimplexCategory.mk 0⟩) PUnit.unit) = _
  have h := congrArg (fun f : 𝟙_ SSet ⟶ (ihom U).obj (sHom (U ⋔ A) A) =>
      f.app ⟨SimplexCategory.mk 0⟩ PUnit.unit)
    (cotensor_coneNatTrans_eId (getCotensor U A))
  exact h.trans (by rfl)

/-- The underlying map of a cotensor isomorphism is represented by the chosen cotensor cone. -/
lemma cotensor_iso_underlying_eq_cone {U : SSet.{v}} (A X : K) [HasCotensor U A]
    (h : X ⟶ U ⋔ A) :
    (cotensor.iso.underlying U A X) h =
      (getCotensor U A).cone ≫ eHomWhiskerRight SSet h A := by
  apply (homEquiv' U (sHom X A)).injective
  rw [cotensor_underlying_homEquiv]
  change (((getCotensor U A).coneNatTrans X).app ⟨SimplexCategory.mk 0⟩
      (homEquiv' X (U ⋔ A) h)) =
    ((sHomWhiskerLeft U (eHomWhiskerRight SSet h A)).app ⟨SimplexCategory.mk 0⟩)
      (homEquiv' U (sHom (U ⋔ A) A) (getCotensor U A).cone)
  conv_lhs => rw [← Category.comp_id h, homEquiv'_comp]
  rw [← cotensor_coneNatTrans_id]
  have hn := congrArg
    (fun f : sHom (U ⋔ A) (U ⋔ A) ⟶ (ihom U).obj (sHom X A) =>
      f.app ⟨SimplexCategory.mk 0⟩ (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _)))
    (cotensor_coneNatTrans_naturality_left (getCotensor U A) h)
  change (((eHomWhiskerRight SSet h (getCotensor U A).obj ≫
      (getCotensor U A).coneNatTrans X).app ⟨SimplexCategory.mk 0⟩)
      (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _))) =
    (((getCotensor U A).coneNatTrans (U ⋔ A) ≫
      (ihom U).map (eHomWhiskerRight SSet h A)).app ⟨SimplexCategory.mk 0⟩)
      (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _))
  exact hn

end

section
variable {K : Type u} [Category.{v} K] [SimplicialCategory K] [HasCotensors K]

/-- The zero-simplex corresponding to a contravariant cotensor map. -/
lemma homEquiv'_cotensorContraMap {U V : SSet.{v}} (i : U ⟶ V) (A : K) :
    homEquiv' (V ⋔ A) (U ⋔ A) (cotensorContraMap i A) =
      ((eHomEquiv SSet i ≫
        Cotensor.EhomPrecompose SSet (getCotensor U A) (getCotensor V A)).app
        ⟨SimplexCategory.mk 0⟩) PUnit.unit := by
  change (((eHomEquiv SSet) (cotensorPrecompose (getCotensor U A)
    (getCotensor V A) i)).app ⟨SimplexCategory.mk 0⟩) PUnit.unit = _
  rw [cotensorPrecompose_homEquiv]

/-- The chosen cotensor cone is natural with respect to contravariant cotensor maps. -/
lemma cotensor_contraMap_cone {U V : SSet.{v}} (i : U ⟶ V) (A : K) :
    (getCotensor U A).cone ≫ eHomWhiskerRight SSet (cotensorContraMap i A) A =
      i ≫ (getCotensor V A).cone := by
  rw [← cotensor_iso_underlying_eq_cone]
  apply (homEquiv' U (sHom (V ⋔ A) A)).injective
  rw [cotensor_underlying_homEquiv]
  change (((getCotensor U A).coneNatTrans (V ⋔ A)).app ⟨SimplexCategory.mk 0⟩
      (homEquiv' (V ⋔ A) (U ⋔ A) (cotensorContraMap i A))) =
    homEquiv' U (sHom (V ⋔ A) A) (i ≫ (getCotensor V A).cone)
  rw [homEquiv'_comp_sset_ihom, homEquiv'_cotensorContraMap]
  change (((eHomEquiv SSet i ≫
      Cotensor.EhomPrecompose SSet (getCotensor U A) (getCotensor V A) ≫
      (getCotensor U A).coneNatTrans (V ⋔ A)).app ⟨SimplexCategory.mk 0⟩) PUnit.unit) = _
  have hpre : eHomEquiv SSet i ≫
      Cotensor.EhomPrecompose SSet (getCotensor U A) (getCotensor V A) ≫
      (getCotensor U A).coneNatTrans (V ⋔ A) =
      eHomEquiv SSet i ≫ (ihom U).map (getCotensor V A).cone :=
    (Category.assoc _ _ _).trans
      (whisker_eq (eHomEquiv SSet i)
        (Cotensor.EhomPrecompose_coneNatTrans_eq SSet (getCotensor U A) (getCotensor V A)))
  rw [hpre]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chosen cotensor cone is natural with respect to covariant cotensor maps. -/
lemma cotensorPostcompose_cone {U : SSet.{v}} {A B : K} (f : A ⟶ B) :
    (getCotensor U B).cone ≫
      eHomWhiskerRight SSet
        (cotensorPostcompose (getCotensor U A) (getCotensor U B) f) B =
        (getCotensor U A).cone ≫
          eHomWhiskerLeft SSet (getCotensor U A).obj f := by
  calc
    (getCotensor U B).cone ≫
        eHomWhiskerRight SSet
          (cotensorPostcompose (getCotensor U A) (getCotensor U B) f) B =
      (λ_ U).inv ≫ ((eHomEquiv SSet) f ▷ U) ≫
        (Cotensor.postcompose SSet (getCotensor U A) (getCotensor U B) ▷ U) ≫
        (_ ◁ (getCotensor U B).cone) ≫
        eComp SSet (getCotensor U A).obj (getCotensor U B).obj B := by
        dsimp [eHomWhiskerRight]
        rw [cotensorPostcompose_homEquiv]
        rw [leftUnitor_inv_naturality_assoc]
        rw [MonoidalCategory.comp_whiskerRight_assoc]
        rw [MonoidalCategory.whisker_exchange_assoc]
        rw [MonoidalCategory.whisker_exchange_assoc]
    _ = (λ_ U).inv ≫ ((eHomEquiv SSet) f ▷ U) ≫
        (β_ (A ⟶[SSet] B) U).hom ≫
        ((getCotensor U A).cone ▷ (A ⟶[SSet] B)) ≫
        eComp SSet (getCotensor U A).obj A B := by
        rw [Cotensor.postcompose_selfEval_comp_eq]
    _ = (getCotensor U A).cone ≫
        eHomWhiskerLeft SSet (getCotensor U A).obj f := by
        dsimp [eHomWhiskerLeft]
        rw [braiding_naturality_left_assoc]
        rw [braiding_tensorUnit_left_assoc]
        rw [Iso.inv_hom_id_assoc]
        rw [MonoidalCategory.whisker_exchange_assoc]
        rw [← rightUnitor_inv_naturality_assoc]

/-- Naturality of `cotensor.iso` under precomposition in the simplicial-set variable. -/
lemma cotensor_iso_hom_naturality_precompose {U V : SSet.{v}} (i : U ⟶ V) (A X : K) :
    eHomWhiskerLeft SSet X (cotensorContraMap i A) ≫ (cotensor.iso U A X).hom =
      (cotensor.iso V A X).hom ≫ (MonoidalClosed.pre i).app (sHom X A) := by
  change eHomWhiskerLeft SSet X (cotensorPrecompose (getCotensor U A) (getCotensor V A) i) ≫
      (getCotensor U A).coneNatTrans X =
    (getCotensor V A).coneNatTrans X ≫ (MonoidalClosed.pre i).app (sHom X A)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  change U ◁ eHomWhiskerLeft SSet X (cotensorPrecompose (getCotensor U A)
      (getCotensor V A) i) ≫ MonoidalClosed.uncurry ((getCotensor U A).coneNatTrans X) =
    (i ▷ (X ⟶[SSet] (getCotensor V A).obj)) ≫
      MonoidalClosed.uncurry ((getCotensor V A).coneNatTrans X)
  rw [(getCotensor U A).toPrecotensor.coneNatTrans_eq]
  rw [(getCotensor V A).toPrecotensor.coneNatTrans_eq]
  rw [braiding_naturality_left_assoc]
  rw [braiding_naturality_right_assoc]
  apply (Iso.cancel_iso_hom_left
    (β_ U (X ⟶[SSet] (getCotensor V A).obj)) _ _).mpr
  rw [← whisker_exchange_assoc]
  rw [eComp_eHomWhisker_middle]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  change (X ⟶[SSet] (getCotensor V A).obj) ◁
      ((getCotensor U A).cone ≫ eHomWhiskerRight SSet (cotensorContraMap i A) A) ≫
    eComp SSet X (getCotensor V A).obj A = _
  rw [cotensor_contraMap_cone i A]
  change ((X ⟶[SSet] (getCotensor V A).obj) ◁ i ≫
      (X ⟶[SSet] (getCotensor V A).obj) ◁ (getCotensor V A).cone) ≫
    eComp SSet X (getCotensor V A).obj A = _
  rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `cotensor.iso` under postcomposition in the cotensored object. -/
lemma cotensor_iso_hom_naturality_postcompose {U : SSet.{v}} {A B : K}
    (f : A ⟶ B) (X : K) :
    eHomWhiskerLeft SSet X (cotensorCovMap U f) ≫ (cotensor.iso U B X).hom =
      (cotensor.iso U A X).hom ≫ (ihom U).map (eHomWhiskerLeft SSet X f) := by
  change eHomWhiskerLeft SSet X
      (cotensorPostcompose (getCotensor U A) (getCotensor U B) f) ≫
      (getCotensor U B).coneNatTrans X =
    (getCotensor U A).coneNatTrans X ≫
      (ihom U).map (eHomWhiskerLeft SSet X f)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_natural_right
    ((getCotensor U A).coneNatTrans X) (eHomWhiskerLeft SSet X f)]
  rw [(getCotensor U B).toPrecotensor.coneNatTrans_eq]
  rw [(getCotensor U A).toPrecotensor.coneNatTrans_eq]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  simp only [Category.assoc]
  rw [eComp_eHomWhiskerLeft]
  rw [eComp_eHomWhisker_middle]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [cotensorPostcompose_cone f]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]

/-- Naturality of `cotensor.iso.underlying` under precomposition in the simplicial-set variable. -/
lemma cotensor_iso_underlying_precompose {U V : SSet.{v}} (i : U ⟶ V) (A X : K)
    (g : X ⟶ V ⋔ A) :
    (cotensor.iso.underlying U A X) (g ≫ cotensorContraMap i A) =
      i ≫ (cotensor.iso.underlying V A X) g := by
  rw [cotensor_iso_underlying_eq_cone, cotensor_iso_underlying_eq_cone]
  rw [eHomWhiskerRight_comp]
  change (((getCotensor U A).cone ≫ eHomWhiskerRight SSet (cotensorContraMap i A) A) ≫
      eHomWhiskerRight SSet g A) =
    ((i ≫ (getCotensor V A).cone) ≫ eHomWhiskerRight SSet g A)
  exact congrArg (fun f => f ≫ eHomWhiskerRight SSet g A) (cotensor_contraMap_cone i A)

end

end SimplicialCategory

end CategoryTheory
