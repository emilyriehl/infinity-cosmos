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
  `ihom J` as a strict pseudofunctor `C ⥤ C`; its hom-functors `ihomHomFunctor J` act on 2-cells
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

variable (C : Type u)

variable {C} in
set_option backward.isDefEq.respectTransparency false in
/-- Currying the composite of an evaluation `ev` with `u` recovers the internal-hom functor's
action on `u`. -/
@[simp]
lemma curry_ev_app_comp [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (J : C) {A B : C} (u : A ⟶ B) :
    curry ((ihom.ev J).app A ≫ u) = (ihom J).map u := by
  rw [← uncurry_ihom_map, curry_uncurry]

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

def ihomHomFunctor (A B : C) : (A ⟶ B) ⥤ ((J ⟶[C] A) ⟶ (J ⟶[C] B)) :=
  precomp B ((ihom.ev J).app A) ⋙ curryFunctor J (J ⟶[C] A) B

lemma ihomHomFunctor_obj (u : A ⟶ B) :
    (ihomHomFunctor J A B).obj u = curry ((ihom.ev J).app A ≫ u) :=
  rfl

@[simp]
lemma ihomHomFunctor_obj_eq_ihom_map (u : A ⟶ B) :
    (ihomHomFunctor J A B).obj u = (ihom J).map u := by
  rw [ihomHomFunctor_obj, curry_ev_app_comp]

/-- Uncurrying `ihomHomFunctor`'s action on a 2-cell recovers whiskering by the evaluation. -/
lemma uncurryFunctor_map_ihomHomFunctor {u v : A ⟶ B} (η : u ⟶ v) :
    (uncurryFunctor J (J ⟶[C] A) B).map ((ihomHomFunctor J A B).map η) =
      eqToHom (uncurry_curry _) ≫ (ihom.ev J).app A ◁ η ≫ eqToHom (uncurry_curry _).symm :=
  Functor.congr_hom (uncurryIso J (J ⟶[C] A) B).counitIso _

/-- `tensorLeftHomFunctor`'s map of `ihomHomFunctor`'s 2-cell action, whiskered with the
evaluation, recovers whiskering of the original 2-cell. -/
lemma tensorLeftHomFunctor_map_ihomHomFunctor_whiskerRight_ev {u v : A ⟶ B} (η : u ⟶ v) :
    (tensorLeftHomFunctor J (J ⟶[C] A) (J ⟶[C] B)).map ((ihomHomFunctor J A B).map η) ▷
        (ihom.ev J).app B =
      eqToHom (uncurry_curry _) ≫ (ihom.ev J).app A ◁ η ≫ eqToHom (uncurry_curry _).symm := by
  have h := uncurryFunctor_map_ihomHomFunctor J η
  rw [uncurryFunctor_map] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of `ihomHomFunctor`'s 2-cell action with left whiskering. -/
lemma ihomHomFunctor_map_whiskerLeft {A' : C} (w : A' ⟶ A) {u v : A ⟶ B} (η : u ⟶ v) :
    (ihomHomFunctor J A' B).map (w ◁ η) =
      eqToHom (by simp) ≫ (ihomHomFunctor J A' A).obj w ◁ (ihomHomFunctor J A B).map η ≫
        eqToHom (by simp) := by
  apply (uncurryFunctor J (J ⟶[C] A') B).map_injective
  rw [uncurryFunctor_map_ihomHomFunctor]
  have h : J ◁ curry ((ihom.ev J).app A' ≫ w) ≫ (ihom.ev J).app A = (ihom.ev J).app A' ≫ w :=
    (uncurry_eq _).symm.trans (uncurry_curry _)
  simp [Functor.map_comp, eqToHom_map, uncurryFunctor_map, ihomHomFunctor_obj,
    tensorLeftHomFunctor_map_whiskerLeft, Strict.associator_eqToIso,
    tensorLeftHomFunctor_map_ihomHomFunctor_whiskerRight_ev,
    whiskerLeft_whiskerLeft_strict, congr_whiskerLeft h η,
    -comp_whiskerLeft, -tensorLeftHomFunctor_map]

/-- Compatibility of `ihomHomFunctor`'s 2-cell action with right whiskering. -/
lemma ihomHomFunctor_map_whiskerRight {u u' : A ⟶ B} (η : u ⟶ u') {B' : C} (w : B ⟶ B') :
    (ihomHomFunctor J A B').map (η ▷ w) =
      eqToHom (by simp) ≫ (ihomHomFunctor J A B).map η ▷ (ihomHomFunctor J B B').obj w ≫
        eqToHom (by simp) := by
  apply (uncurryFunctor J (J ⟶[C] A) B').map_injective
  rw [uncurryFunctor_map_ihomHomFunctor]
  have h : J ◁ curry ((ihom.ev J).app B ≫ w) ≫ (ihom.ev J).app B' = (ihom.ev J).app B ≫ w :=
    (uncurry_eq _).symm.trans (uncurry_curry _)
  simp [Functor.map_comp, eqToHom_map, uncurryFunctor_map, ihomHomFunctor_obj,
    tensorLeftHomFunctor_map_whiskerRight, comp_whiskerRight, Strict.associator_eqToIso,
    tensorLeftHomFunctor_map_ihomHomFunctor_whiskerRight_ev,
    whiskerRight_whiskerRight_strict, whiskerRight_congr h,
    -tensorLeftHomFunctor_map]

/-- `ihom J` as a strict pseudofunctor `C ⥤ C`, with hom-functors given by `ihomHomFunctor J`. -/
def ihomPseudofunctor : StrictPseudofunctor C C := .mk'' {
    toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun A => J ⟶[C] A) (ihomHomFunctor J)
    map_id _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
    map_comp _ _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
    map₂_whisker_left := ihomHomFunctor_map_whiskerLeft J
    map₂_whisker_right η w := ihomHomFunctor_map_whiskerRight J η w
  }

@[simp]
lemma ihomPseudofunctor_map {u : A ⟶ B} : (ihomPseudofunctor J).map u = (ihom J).map u :=
  ihomHomFunctor_obj_eq_ihom_map J u

/-- In a cartesian closed strict bicategory, the internal hom `ihom J` carries adjunctions to
adjunctions: if `f ⊣ u`, then `(ihom J).map f ⊣ (ihom J).map u`. -/
def ihomMapAdjunction {f : A ⟶ B} {u : B ⟶ A} (adj : f ⊣ u) :
    (ihom J).map f ⊣ (ihom J).map u := by
  rw [← ihomPseudofunctor_map, ← ihomPseudofunctor_map]
  exact (ihomPseudofunctor J).mapAdjunction adj

end IhomPseudofunctor

end Strict.CartesianClosed

end

end CategoryTheory.Bicategory
