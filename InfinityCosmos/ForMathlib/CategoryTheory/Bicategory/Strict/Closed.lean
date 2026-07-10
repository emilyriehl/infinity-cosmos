import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.CartesianMonoidal

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

noncomputable section

variable (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C]

variable {C} in
def uncurryFunctor [Strict.CartesianMonoidal C] [MonoidalClosed C] (X Y Z : C) :
    (Y ⟶ X ⟶[C] Z) ⥤ (X ⊗ Y ⟶ Z) :=
  tensorLeftHomFunctor X Y (X ⟶[C] Z) ⋙ postcomp (X ⊗ Y) ((ihom.ev X).app Z)

variable {C} in
@[simp]
lemma uncurryFunctor_obj [Strict.CartesianMonoidal C] [MonoidalClosed C] (X Y Z : C)
    (f : Y ⟶ X ⟶[C] Z) :
  (uncurryFunctor X Y Z).obj f = X ◁ f ≫ (ihom.ev X).app Z := rfl

variable {C} in
/-- The uncurry functor acts on 2-cells by `tensorLeftHomFunctor`'s map followed by whiskering
with the evaluation. -/
lemma uncurryFunctor_map [Strict.CartesianMonoidal C] [MonoidalClosed C]
    {J Y Z : C} {d d' : Y ⟶ (J ⟶[C] Z)} (θ : d ⟶ d') :
    (uncurryFunctor J Y Z).map θ =
      (tensorLeftHomFunctor J Y (J ⟶[C] Z)).map θ ▷ (ihom.ev J).app Z :=
  rfl

variable {C} in
/-- The uncurry functor computes on `(ihom J).map u` as the conjugate of `u` by the
evaluation. -/
lemma uncurryFunctor_obj_ihom_map [Strict.CartesianMonoidal C] [MonoidalClosed C]
    (J : C) {A B : C} (u : A ⟶ B) :
    (uncurryFunctor J (J ⟶[C] A) B).obj ((ihom J).map u) = (ihom.ev J).app A ≫ u := by
  rw [uncurryFunctor_obj]
  exact (ihom.ev J).naturality u

/-- A cartesian monoidal strict bicategory is *cartesian closed* if its underlying category is
monoidal closed and the currying bijections extend to isomorphisms of hom-categories. -/
class Strict.CartesianClosed extends Strict.CartesianMonoidal C, MonoidalClosed C where
  /-- The comparison functor `(Y ⟶ (X ⟶[C] Z)) ⥤ (X ⊗ Y ⟶ Z)`, sending `d` to
  `(X ◁ d) ≫ ev`, is an isomorphism of categories. -/
  uncurryFunctor_isIso (X Y Z : C) : (uncurryFunctor X Y Z).IsIsomorphism

attribute [instance] Strict.CartesianClosed.uncurryFunctor_isIso

variable {C}

namespace Strict.CartesianClosed

variable [Strict.CartesianClosed C]

def curryFunctor' (X Y Z : C) : (X ⊗ Y ⟶ Z) ⥤ (Y ⟶ X ⟶[C] Z) :=
  (uncurryFunctor X Y Z).asIsomorphism.inverse

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma currFunctor'_obj (X Y Z : C) (f : X ⊗ Y ⟶ Z) :
    (curryFunctor' X Y Z).obj f = curry f := by
  apply (uncurryFunctor_isIso X Y Z).bijectiveOnObjects.injective
  have : (uncurryFunctor X Y Z).obj ((curryFunctor' X Y Z).obj f) = f :=
    Functor.congr_obj (uncurryFunctor X Y Z).asIsomorphism.counitIso f
  rw [this]
  simp [uncurryFunctor]

def curryFunctor (X Y Z : C) : (X ⊗ Y ⟶ Z) ⥤ (Y ⟶ X ⟶[C] Z) :=
  (curryFunctor' X Y Z).copyObj (fun f ↦ curry f) (fun η ↦ eqToIso (by simp))

lemma curryFunctor_eq_curryFunctor' (X Y Z : C) :
    curryFunctor X Y Z = curryFunctor' X Y Z :=
  Functor.ext (fun f ↦ by simp [curryFunctor]) (fun _ _ η ↦ by simp [curryFunctor, Functor.copyObj])

/-- The uncurry isomorphism of hom-categories `(Y ⟶ X ⟶[C] Z) ≅ (X ⊗ Y ⟶ Z)`,
coming from the bicategorical closed structure. -/
def uncurryIso (X Y Z : C) : IsoCat (Y ⟶ X ⟶[C] Z) (X ⊗ Y ⟶ Z) where
  functor := uncurryFunctor X Y Z
  inverse := curryFunctor X Y Z
  unitIso := by
    rw [curryFunctor_eq_curryFunctor']
    exact ((uncurryFunctor X Y Z).asIsomorphism).unitIso
  counitIso := by
    rw [curryFunctor_eq_curryFunctor']
    exact ((uncurryFunctor X Y Z).asIsomorphism).counitIso

/-- Transposing the two curried variables across the braiding: an isomorphism of
hom-categories `(Y ⟶ (X ⟶[C] Z)) ≅ (X ⟶ (Y ⟶[C] Z))`. -/
def transposeIso (X Y Z : C) : IsoCat (Y ⟶ X ⟶[C] Z) (X ⟶ Y ⟶[C] Z) :=
  have : BraidedCategory C := .ofCartesianMonoidalCategory
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

variable (J : C) {A B : C}

def ihomHomFunctor : (A ⟶ B) ⥤ ((J ⟶[C] A) ⟶ (J ⟶[C] B)) :=
  precomp B ((ihom.ev J).app A) ⋙ curryFunctor J (J ⟶[C] A) B

/-- The action of `ihom J` on 2-cells, transporting whiskering with the evaluation along the
uncurry isomorphism of hom-categories. -/
def ihomMap₂ {u v : A ⟶ B} (η : u ⟶ v) : (ihom J).map u ⟶ (ihom J).map v :=
  (uncurryFunctor J (J ⟶[C] A) B).preimage
    (eqToHom (uncurryFunctor_obj_ihom_map J u) ≫ (ihom.ev J).app A ◁ η ≫
      eqToHom (uncurryFunctor_obj_ihom_map J v).symm)

/-- The defining property of `ihomMap₂`: uncurrying it gives whiskering with the evaluation. -/
lemma uncurryFunctor_map_ihomMap₂ {u v : A ⟶ B} (η : u ⟶ v) :
    (uncurryFunctor J (J ⟶[C] A) B).map (ihomMap₂ J η) =
      eqToHom (uncurryFunctor_obj_ihom_map J u) ≫ (ihom.ev J).app A ◁ η ≫
        eqToHom (uncurryFunctor_obj_ihom_map J v).symm :=
  Functor.map_preimage _ _

/-- `tensorLeftHomFunctor`'s map of `ihomMap₂`, whiskered with the evaluation, recovers whiskering
of the original 2-cell. -/
lemma tensorLeftHomFunctor_map_ihomMap₂_whiskerRight_ev {u v : A ⟶ B} (η : u ⟶ v) :
    (tensorLeftHomFunctor J (J ⟶[C] A) (J ⟶[C] B)).map (ihomMap₂ J η) ▷ (ihom.ev J).app B =
      eqToHom (ev_naturality J u) ≫ (ihom.ev J).app A ◁ η ≫
        eqToHom (ev_naturality J v).symm := by
  have h := uncurryFunctor_map_ihomMap₂ J η
  rw [uncurryFunctor_map] at h
  simpa using h

/-- Compatibility of `ihomMap₂` with left whiskering. -/
lemma ihomMap₂_whiskerLeft {A' : C} (w : A' ⟶ A) {u v : A ⟶ B} (η : u ⟶ v) :
    ihomMap₂ J (w ◁ η) =
      eqToHom ((ihom J).map_comp w u) ≫ (ihom J).map w ◁ ihomMap₂ J η ≫
        eqToHom ((ihom J).map_comp w v).symm := by
  apply (uncurryFunctor J (J ⟶[C] A') B).map_injective
  rw [uncurryFunctor_map_ihomMap₂]
  simp only [Functor.map_comp, eqToHom_map, uncurryFunctor_map,
    tensorLeftHomFunctor_map_whiskerLeft, comp_whiskerRight,
    whisker_assoc_strict, tensorLeftHomFunctor_map_ihomMap₂_whiskerRight_ev, whiskerLeft_comp,
    whiskerLeft_whiskerLeft_strict, congr_whiskerLeft (ev_naturality J w) η]
  simp

/-- Compatibility of `ihomMap₂` with right whiskering. -/
lemma ihomMap₂_whiskerRight {u u' : A ⟶ B} (η : u ⟶ u') {B' : C} (w : B ⟶ B') :
    ihomMap₂ J (η ▷ w) =
      eqToHom ((ihom J).map_comp u w) ≫ ihomMap₂ J η ▷ (ihom J).map w ≫
        eqToHom ((ihom J).map_comp u' w).symm := by
  apply (uncurryFunctor J (J ⟶[C] A) B').map_injective
  rw [uncurryFunctor_map_ihomMap₂]
  simp only [Functor.map_comp, eqToHom_map, uncurryFunctor_map,
    tensorLeftHomFunctor_map_whiskerRight, comp_whiskerRight,
    whiskerRight_whiskerRight_strict, whiskerRight_congr (ev_naturality J w), whiskerRight_comp_strict,
    tensorLeftHomFunctor_map_ihomMap₂_whiskerRight_ev, whisker_assoc_strict]
  simp

/-- `ihom J` as a strict pseudofunctor `C ⥤ C`, induced by the data of `ihomPreCore J`. -/
def ihomPseudofunctor : StrictPseudofunctor C C :=
  .mk'' {
    obj A := J ⟶[C] A
    map := (ihom J).map
    map₂ := ihomMap₂ J
    map₂_id u := by
      apply (uncurryFunctor J _ _).map_injective
      simp [uncurryFunctor_map_ihomMap₂]
    map₂_comp η θ := by
      apply (uncurryFunctor J _ _).map_injective
      simp [uncurryFunctor_map_ihomMap₂]
    map_id := (ihom J).map_id
    map_comp := (ihom J).map_comp
    map₂_whisker_left := ihomMap₂_whiskerLeft J
    map₂_whisker_right η w := ihomMap₂_whiskerRight J η w
  }

/-- In a cartesian closed strict bicategory, the internal hom `ihom J` carries adjunctions to
adjunctions: if `f ⊣ u`, then `(ihom J).map f ⊣ (ihom J).map u`. -/
def ihomMapAdjunction {f : A ⟶ B} {u : B ⟶ A} (adj : f ⊣ u) :
    (ihom J).map f ⊣ (ihom J).map u :=
  (ihomPseudofunctor J).mapAdjunction adj

end IhomPseudofunctor

end Strict.CartesianClosed

end

end CategoryTheory.Bicategory
