/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.Monoidal

/-!
# Cartesian closed strict bicategories

A cartesian monoidal strict bicategory `C` is *cartesian closed* if its underlying category is
monoidal closed and the closed structure is 2-categorical: for all objects `X Y Z` the canonical
comparison functor `(Y ⟶ (X ⟶[C] Z)) ⥤ (X ⊗ Y ⟶ Z)`, sending `d` to `(X ◁ d) ≫ ev`, is an
isomorphism of categories `uncurryIso`.

## Main definitions

* `CategoryTheory.Bicategory.Strict.CartesianClosed`: the typeclass of cartesian closed strict
  bicategories.
* `CategoryTheory.Bicategory.Strict.CartesianClosed.uncurryIso`: the uncurry isomorphism of
  hom-categories `(Y ⟶ (X ⟶[C] Z)) ≅ (X ⊗ Y ⟶ Z)`.
* `CategoryTheory.Bicategory.Strict.CartesianClosed.ihomPseudofunctor`: the internal hom
  `ihom J` as a strict pseudofunctor `C ⥤ C`; its action `ihomMap₂` on 2-cells is obtained
  by transporting whiskering with the evaluation 1-cell along the uncurry isomorphism.
* `CategoryTheory.Bicategory.Strict.CartesianClosed.ihomMapAdjunction`: `ihom J` carries
  adjunctions to adjunctions ([RV] Proposition 2.1.7).

## References
* [E. Riehl and D. Verity, *Elements of ∞-Category Theory*][RiehlVerity2022]
-/

universe w v u

namespace CategoryTheory.Bicategory

open MonoidalCategory MonoidalClosed Strict.CartesianMonoidal

variable (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C]

/-- A cartesian monoidal strict bicategory is *cartesian closed* if its underlying category is
monoidal closed and the currying bijections extend to isomorphisms of hom-categories. -/
class Strict.CartesianClosed extends Strict.CartesianMonoidal C, MonoidalClosed C where
  /-- The comparison functor `(Y ⟶ (X ⟶[C] Z)) ⥤ (X ⊗ Y ⟶ Z)`, sending `d` to
  `(X ◁ d) ≫ ev`, is an isomorphism of categories. -/
  tensorIhomHomEquiv (X Y Z : C) : Functor.IsIsomorphism <|
    tensorLeftMap₂Functor X Y (X ⟶[C] Z) ⋙ postcomp (X ⊗ Y) ((ihom.ev X).app Z)

variable {C}

/-- `precomp` is functorial in the precomposed morphism (contravariantly). -/
lemma precomp_comp {X X' X'' : C} (g : X ⟶ X') (f : X' ⟶ X'') (A : C) :
    precomp A (g ≫ f) = precomp A f ⋙ precomp A g :=
  Functor.ext (fun h => by simp) fun h h' φ => by
    simp only [Functor.comp_map, precomp_map, comp_whiskerLeft, Strict.associator_eqToIso,
      eqToIso.hom, eqToIso.inv]
    rfl

/-- Precomposing by an identity is the identity functor on the hom-category. -/
lemma precomp_id (X A : C) : precomp A (𝟙 X) = 𝟭 (X ⟶ A) :=
  Functor.ext (fun h => by simp) fun h h' φ => by simp [precomp, Strict.leftUnitor_eqToIso]

/-- Precomposition by an isomorphism `e : X ≅ X'` of objects of `C` induces an isomorphism of
hom-categories `(X ⟶ A) ≅ (X' ⟶ A)`. -/
def homPrecomposeIso {X X' : C} (e : X ≅ X') (A : C) : IsoCat (X ⟶ A) (X' ⟶ A) where
  functor := precomp A e.inv
  inverse := precomp A e.hom
  unitIso := by rw [← precomp_comp, e.hom_inv_id, precomp_id]
  counitIso := by rw [← precomp_comp, e.inv_hom_id, precomp_id]

namespace Strict.CartesianClosed

variable [Strict.CartesianClosed C]

/-- The uncurry isomorphism of hom-categories `(Y ⟶ X ⟶[C] Z) ≅ (X ⊗ Y ⟶ Z)`,
coming from the bicategorical closed structure. -/
noncomputable def uncurryIso (X Y Z : C) : IsoCat (Y ⟶ X ⟶[C] Z) (X ⊗ Y ⟶ Z) :=
  haveI := tensorIhomHomEquiv X Y Z
  (tensorLeftMap₂Functor X Y (X ⟶[C] Z) ⋙ postcomp (X ⊗ Y) ((ihom.ev X).app Z)).asIsomorphism

/-- Transposing the two curried variables across the braiding: an isomorphism of
hom-categories `(Y ⟶ (X ⟶[C] Z)) ≅ (X ⟶ (Y ⟶[C] Z))`. -/
noncomputable def transposeIso (X Y Z : C) : IsoCat (Y ⟶ X ⟶[C] Z) (X ⟶ Y ⟶[C] Z) :=
  haveI : BraidedCategory C := .ofCartesianMonoidalCategory
  (uncurryIso X Y Z).trans ((homPrecomposeIso (β_ X Y) Z).trans (uncurryIso Y X Z).symm)

/-!
### `ihom J` as a strict pseudofunctor, and preservation of adjunctions

We extend the internal-hom functor `ihom J : C ⥤ C` to a strict pseudofunctor: its action on
2-cells is obtained by transporting whiskering with the evaluation 1-cell along the uncurry
isomorphism of hom-categories. As a consequence, `ihom J` carries adjunctions to adjunctions
(`Strict.CartesianClosed.ihomMapAdjunction`).
-/

section IhomPseudofunctor

set_option backward.isDefEq.respectTransparency false

/-- Naturality of the evaluation: `ev` intertwines `J ◁ (ihom J).map u` and `u`. -/
lemma ev_naturality (J : C) {A B : C} (u : A ⟶ B) :
    J ◁ (ihom J).map u ≫ (ihom.ev J).app B = (ihom.ev J).app A ≫ u :=
  (ihom.ev J).naturality u

/-- The uncurry functor computes on objects as `d ↦ (J ◁ d) ≫ ev`. -/
lemma uncurryIso_functor_obj {J Y Z : C} (d : Y ⟶ (J ⟶[C] Z)) :
    (uncurryIso J Y Z).functor.obj d = J ◁ d ≫ (ihom.ev J).app Z := by
  show (tensorLeftMap₂Functor J Y (J ⟶[C] Z)).obj d ≫ (ihom.ev J).app Z = _
  rw [tensorLeftMap₂Functor_obj]

/-- The uncurry functor computes on `(ihom J).map u` as the conjugate of `u` by the
evaluation. -/
lemma uncurryIso_functor_obj_ihom_map (J : C) {A B : C} (u : A ⟶ B) :
    (uncurryIso J (J ⟶[C] A) B).functor.obj ((ihom J).map u) = (ihom.ev J).app A ≫ u := by
  rw [uncurryIso_functor_obj, ev_naturality]

/-- The uncurry functor acts on 2-cells by `tensorLeftMap₂` followed by whiskering with the
evaluation. -/
lemma uncurryIso_functor_map {J Y Z : C} {d d' : Y ⟶ (J ⟶[C] Z)} (θ : d ⟶ d') :
    (uncurryIso J Y Z).functor.map θ =
      eqToHom (uncurryIso_functor_obj d) ≫ tensorLeftMap₂ J θ ▷ (ihom.ev J).app Z ≫
        eqToHom (uncurryIso_functor_obj d').symm := by
  show (tensorLeftMap₂Functor J Y (J ⟶[C] Z)).map θ ▷ (ihom.ev J).app Z = _
  rw [show (tensorLeftMap₂Functor J Y (J ⟶[C] Z)).map θ =
      eqToHom (tensorLeftMap₂Functor_obj J d) ≫ tensorLeftMap₂ J θ ≫
        eqToHom (tensorLeftMap₂Functor_obj J d').symm by simp [tensorLeftMap₂]]
  simp only [comp_whiskerRight, eqToHom_whiskerRight]

variable (J : C) {A B : C}

/-- The action of `ihom J` on 2-cells, transporting whiskering with the evaluation along the
uncurry isomorphism of hom-categories. -/
noncomputable def ihomMap₂ {u v : A ⟶ B} (η : u ⟶ v) : (ihom J).map u ⟶ (ihom J).map v :=
  (uncurryIso J (J ⟶[C] A) B).functor.preimage
    (eqToHom (uncurryIso_functor_obj_ihom_map J u) ≫ (ihom.ev J).app A ◁ η ≫
      eqToHom (uncurryIso_functor_obj_ihom_map J v).symm)

/-- The defining property of `ihomMap₂`: uncurrying it gives whiskering with the evaluation. -/
lemma uncurryIso_functor_map_ihomMap₂ {u v : A ⟶ B} (η : u ⟶ v) :
    (uncurryIso J (J ⟶[C] A) B).functor.map (ihomMap₂ J η) =
      eqToHom (uncurryIso_functor_obj_ihom_map J u) ≫ (ihom.ev J).app A ◁ η ≫
        eqToHom (uncurryIso_functor_obj_ihom_map J v).symm :=
  Functor.map_preimage _ _

/-- `tensorLeftMap₂` of `ihomMap₂`, whiskered with the evaluation, recovers whiskering of the
original 2-cell. -/
lemma tensorLeftMap₂_ihomMap₂_whiskerRight_ev {u v : A ⟶ B} (η : u ⟶ v) :
    tensorLeftMap₂ J (ihomMap₂ J η) ▷ (ihom.ev J).app B =
      eqToHom (ev_naturality J u) ≫ (ihom.ev J).app A ◁ η ≫
        eqToHom (ev_naturality J v).symm := by
  have h := uncurryIso_functor_map_ihomMap₂ J η
  rw [uncurryIso_functor_map, eqToHom_comp_iff, ← Category.assoc, comp_eqToHom_iff] at h
  simpa using h

/-- Compatibility of `ihomMap₂` with left whiskering. -/
lemma ihomMap₂_whiskerLeft {A' : C} (w : A' ⟶ A) {u v : A ⟶ B} (η : u ⟶ v) :
    ihomMap₂ J (w ◁ η) =
      eqToHom ((ihom J).map_comp w u) ≫ (ihom J).map w ◁ ihomMap₂ J η ≫
        eqToHom ((ihom J).map_comp w v).symm := by
  apply (uncurryIso J (J ⟶[C] A') B).functor.map_injective
  rw [uncurryIso_functor_map_ihomMap₂]
  simp only [Functor.map_comp, eqToHom_map]
  rw [uncurryIso_functor_map, tensorLeftMap₂_whiskerLeft]
  simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
  rw [whisker_assoc_strict, tensorLeftMap₂_ihomMap₂_whiskerRight_ev]
  simp only [whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc]
  rw [whiskerLeft_whiskerLeft_strict, whiskerLeft_whiskerLeft_strict,
    congr_whiskerLeft (ev_naturality J w) η]
  simp

/-- Compatibility of `ihomMap₂` with right whiskering. -/
lemma ihomMap₂_whiskerRight {u u' : A ⟶ B} (η : u ⟶ u') {B' : C} (w : B ⟶ B') :
    ihomMap₂ J (η ▷ w) =
      eqToHom ((ihom J).map_comp u w) ≫ ihomMap₂ J η ▷ (ihom J).map w ≫
        eqToHom ((ihom J).map_comp u' w).symm := by
  apply (uncurryIso J (J ⟶[C] A) B').functor.map_injective
  rw [uncurryIso_functor_map_ihomMap₂]
  simp only [Functor.map_comp, eqToHom_map]
  rw [uncurryIso_functor_map, tensorLeftMap₂_whiskerRight]
  simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
  rw [whiskerRight_whiskerRight_strict, whiskerRight_congr (ev_naturality J w),
    whiskerRight_comp_strict, tensorLeftMap₂_ihomMap₂_whiskerRight_ev]
  simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
  rw [whisker_assoc_strict]
  simp

/-- `ihom J` as the data of a strict pseudofunctor `C ⥤ C`: it acts on objects by `J ⟶[C] ·`,
on 1-cells by `(ihom J).map`, and on 2-cells by `ihomMap₂`. -/
noncomputable def ihomPreCore : StrictPseudofunctorPreCore C C where
  obj A := J ⟶[C] A
  map := (ihom J).map
  map₂ := ihomMap₂ J
  map₂_id u := by
    apply (uncurryIso J _ _).functor.map_injective
    simp [uncurryIso_functor_map_ihomMap₂]
  map₂_comp η θ := by
    apply (uncurryIso J _ _).functor.map_injective
    simp [uncurryIso_functor_map_ihomMap₂]
  map_id := (ihom J).map_id
  map_comp := (ihom J).map_comp
  map₂_whisker_left := ihomMap₂_whiskerLeft J
  map₂_whisker_right η w := ihomMap₂_whiskerRight J η w

/-- `ihom J` as a strict pseudofunctor `C ⥤ C`, induced by the data of `ihomPreCore J`. -/
noncomputable def ihomPseudofunctor : StrictPseudofunctor C C :=
  .mk'' (ihomPreCore J)

/-- In a cartesian closed strict bicategory, the internal hom `ihom J` carries adjunctions to
adjunctions: if `f ⊣ u`, then `(ihom J).map f ⊣ (ihom J).map u`. -/
noncomputable def ihomMapAdjunction {f : A ⟶ B} {u : B ⟶ A} (adj : f ⊣ u) :
    (ihom J).map f ⊣ (ihom J).map u :=
  (ihomPseudofunctor J).mapAdjunction adj

end IhomPseudofunctor

end Strict.CartesianClosed

end CategoryTheory.Bicategory
