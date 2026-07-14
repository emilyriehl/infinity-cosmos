/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.CotensorIso

open scoped Simplicial

/-!
# The point cotensor `Δ[0] ⋔ B ≅ B`

This file develops the point-cotensor comparison: cotensoring an object `B` of an ∞-cosmos with the
point `Δ[0]` recovers `B`, via an explicit isomorphism `cotensorPointIso : Δ[0] ⋔ₛ B ≅ B`. The map
`cotensorPointMap` names an ordinary morphism inside the point cotensor, `cotensorPointIsoHom` is
the comparison in the other direction, and the two are mutually inverse.

The lemma `representableMap_cotensorPointIsoHom` records how the comparison interacts with covariant
representables `Fun(X, -)`: it evaluates the cotensor comparison isomorphism at the unique point of
`Δ[0]`. This identification is the infrastructure on which the endpoint evaluations of a
coherent-isomorphism cotensor are built, used by the equivalence/homotopy-equivalence development.
-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos
open HasConicalTerminal
open MonoidalCategory BraidedCategory

local notation3:1024 U:1024 " ⋔ₛ " A:1024 =>
  CategoryTheory.SimplicialCategory.cotensor.obj U A

variable {K : Type u} [Category.{v} K] [InfinityCosmos.{0} K]

/-- The map into the point cotensor corresponding to an ordinary morphism. -/
noncomputable def cotensorPointMap {A B : K} (f : A ⟶ B) : A ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B :=
  (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A).symm
    (SSet.pointIsUnit.hom ≫
      (eHomEquiv SSet f : MonoidalCategoryStruct.tensorUnit SSet ⟶ sHom A B))

/-- The map from the point cotensor to the underlying object, inverse to `cotensorPointMap (𝟙 B)`. -/
noncomputable def cotensorPointIsoHom (B : K) : (Δ[0] : SSet.{v}) ⋔ₛ B ⟶ B :=
  (eHomEquiv SSet).symm (SSet.pointIsUnit.inv ≫ cotensor.cone (Δ[0] : SSet.{v}) B)

/-- The enriched morphism corresponding to `cotensorPointIsoHom`. -/
lemma cotensorPointIsoHom_homEquiv (B : K) :
    eHomEquiv SSet (cotensorPointIsoHom B) =
      SSet.pointIsUnit.inv ≫ cotensor.cone (Δ[0] : SSet.{v}) B := by
  simp [cotensorPointIsoHom]

/-- The underlying map represented by `cotensorPointMap`. -/
lemma cotensorPointMap_underlying {A B : K} (f : A ⟶ B) :
    (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A) (cotensorPointMap f) =
      SSet.pointIsUnit.hom ≫ eHomEquiv SSet f := by
  simp [cotensorPointMap]

/-- Composing a point-cotensor map with the point-cotensor comparison recovers the original map. -/
lemma cotensorPointMap_comp_cotensorPointIsoHom {A B : K} (f : A ⟶ B) :
    cotensorPointMap f ≫ cotensorPointIsoHom B = f := by
  apply (eHomEquiv SSet).injective
  rw [← eHomEquiv_comp_eHomWhiskerRight]
  rw [cotensorPointIsoHom_homEquiv]
  rw [Category.assoc]
  have hmap := cotensorPointMap_underlying f
  rw [cotensor_iso_underlying_eq_cone] at hmap
  change SSet.pointIsUnit.inv ≫
      ((getCotensor (Δ[0] : SSet.{v}) B).cone ≫
        eHomWhiskerRight SSet (cotensorPointMap f) B) =
    (eHomEquiv SSet) f
  rw [hmap]
  rw [← Category.assoc, SSet.pointIsUnit.inv_hom_id, Category.id_comp]

/-- One inverse identity for the point-cotensor comparison. -/
lemma cotensorPointIso_hom_inv_id (B : K) :
    cotensorPointIsoHom B ≫ cotensorPointMap (𝟙 B) = 𝟙 ((Δ[0] : SSet.{v}) ⋔ₛ B) := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B ((Δ[0] : SSet.{v}) ⋔ₛ B)).injective
  rw [cotensor_iso_underlying_eq_cone]
  rw [cotensor_iso_underlying_eq_cone]
  rw [eHomWhiskerRight_comp]
  change (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      (eHomWhiskerRight SSet (cotensorPointMap (𝟙 B)) B ≫
        eHomWhiskerRight SSet (cotensorPointIsoHom B) B) =
    (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eHomWhiskerRight SSet (𝟙 ((Δ[0] : SSet.{v}) ⋔ₛ B)) B
  rw [← Category.assoc]
  have hmap := cotensorPointMap_underlying (𝟙 B)
  rw [cotensor_iso_underlying_eq_cone] at hmap
  rw [hmap, Category.assoc, eHomEquiv_comp_eHomWhiskerRight, Category.comp_id,
    cotensorPointIsoHom_homEquiv]
  rw [← Category.assoc, SSet.pointIsUnit.hom_inv_id, Category.id_comp, eHomWhiskerRight_id]
  change (getCotensor (Δ[0] : SSet.{v}) B).cone =
    (getCotensor (Δ[0] : SSet.{v}) B).cone ≫ 𝟙 _
  rw [Category.comp_id]

/-- The other inverse identity for the point-cotensor comparison. -/
lemma cotensorPointIso_inv_hom_id (B : K) :
    cotensorPointMap (𝟙 B) ≫ cotensorPointIsoHom B = 𝟙 B :=
  cotensorPointMap_comp_cotensorPointIsoHom (𝟙 B)

/-- The point cotensor is isomorphic to the original object. -/
noncomputable def cotensorPointIso (B : K) : (Δ[0] : SSet.{v}) ⋔ₛ B ≅ B where
  hom := cotensorPointIsoHom B
  inv := cotensorPointMap (𝟙 B)
  hom_inv_id := cotensorPointIso_hom_inv_id B
  inv_hom_id := cotensorPointIso_inv_hom_id B

set_option backward.isDefEq.respectTransparency false in
/-- On representables, the point-cotensor comparison evaluates the cotensor isomorphism at the
unique point of `Δ[0]`. -/
lemma representableMap_cotensorPointIsoHom {B : K} (X : K) :
    representableMap X (cotensorPointIsoHom B) =
      (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫ (sHom X B).expPointIsoSelf.hom := by
  change eHomWhiskerLeft SSet X (cotensorPointIsoHom B) =
    (getCotensor (Δ[0] : SSet.{v}) B).coneNatTrans X ≫
      (sHom X B).expPointIsoSelf.hom
  let point : SSet.{v} := Δ[0]
  let Cobj : K := (getCotensor point B).obj
  let Y : SSet.{v} := sHom X Cobj
  let cone := (getCotensor point B).cone
  let H := (β_ point Y).hom ≫ (Y ◁ cone) ≫ eComp SSet X Cobj B
  have hcone : (getCotensor point B).coneNatTrans X =
      MonoidalClosed.curry H := by
    apply MonoidalClosed.uncurry_injective (A := point)
    dsimp [H]
    rw [(getCotensor point B).toPrecotensor.coneNatTrans_eq]
    rw [MonoidalClosed.uncurry_curry]
  rw [hcone]
  rw [SSet.curry_expPointIsoSelf_hom]
  dsimp [H]
  change eHomWhiskerLeft SSet X (cotensorPointIsoHom B) =
    (λ_ (sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj)).inv ≫
      (SSet.pointIsUnit.inv ▷ sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj) ≫
      (β_ (Δ[0] : SSet.{v}) (sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj)).hom ≫
      (sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj) ◁
        (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B
  dsimp [eHomWhiskerLeft]
  rw [cotensorPointIsoHom_homEquiv]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  let Y : SSet.{v} := sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj
  change ((ρ_ Y).inv ≫ Y ◁ SSet.pointIsUnit.inv) ≫
      Y ◁ (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B =
    ((λ_ Y).inv ≫ SSet.pointIsUnit.inv ▷ Y ≫
      (β_ (Δ[0] : SSet.{v}) Y).hom) ≫
      Y ◁ (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ Y ◁ (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B)
    (SSet.rightUnitor_inv_pointIsUnit_inv Y)

set_option backward.isDefEq.respectTransparency false in
/-- On representables, `cotensorPointMap` is the original map followed by the inverse
point-evaluation isomorphism. -/
lemma representableMap_cotensorPointMap_hom {A B : K} (f : A ⟶ B) (X : K) :
    representableMap X (cotensorPointMap f) ≫ (cotensor.iso (Δ[0] : SSet.{v}) B X).hom =
      representableMap X f ≫ (sHom X B).expPointIsoSelf.inv := by
  apply (cancel_mono (sHom X B).expPointIsoSelf.hom).mp
  calc
    (representableMap X (cotensorPointMap f) ≫
        (cotensor.iso (Δ[0] : SSet.{v}) B X).hom) ≫
        (sHom X B).expPointIsoSelf.hom =
      representableMap X (cotensorPointMap f) ≫ representableMap X (cotensorPointIsoHom B) := by
        rw [Category.assoc, representableMap_cotensorPointIsoHom]
    _ = representableMap X (cotensorPointMap f ≫ cotensorPointIsoHom B) := by
        rw [representableMap_comp]
    _ = representableMap X f := by
        rw [cotensorPointMap_comp_cotensorPointIsoHom]
    _ = (representableMap X f ≫ (sHom X B).expPointIsoSelf.inv) ≫
        (sHom X B).expPointIsoSelf.hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end InfinityCosmos
