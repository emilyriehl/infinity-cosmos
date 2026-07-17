import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.CartesianMonoidal

/-!
# Cartesian closed strict bicategories
-/

universe w v u

namespace CategoryTheory.Bicategory

open MonoidalCategory MonoidalClosed Strict.CartesianMonoidal

noncomputable section

variable (C : Type u)

variable {C} in
set_option backward.isDefEq.respectTransparency false in
/-- Currying the composite of an evaluation `ev` with `f` recovers the internal-hom functor's
action on `f`. -/
@[simp]
lemma curry_ev_app_comp [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (J : C) {X Y : C} (f : X ⟶ Y) :
    curry ((ihom.ev J).app X ≫ f) = (ihom J).map f := by
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
    {X Y Z : C} {f g : Y ⟶ (X ⟶[C] Z)} (η : f ⟶ g) :
    (uncurryFunctor X Y Z).map η =
      (tensorLeftHomFunctor X Y (X ⟶[C] Z)).map η ▷ (ihom.ev X).app Z :=
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

/-- The curry functor `(X ⊗ Y ⟶ Z) ⥤ (Y ⟶ X ⟶[C] Z)` for a cartesian closed strict bicategory.
This one, however, does not have the right definitional action on objects `f : X ⊗ Y ⟶ Z`. Hence,
we later define `curryFunctor` with the correct computational behaviour. -/
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
  simp

/-- The curry functor `(X ⊗ Y ⟶ Z) ⥤ (Y ⟶ X ⟶[C] Z)` for a cartesian closed strict bicategory, with
correct computational behaviour on objects `f : X ⊗ Y ⟶ Z`. -/
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

section IhomPseudofunctor

set_option backward.isDefEq.respectTransparency false

variable (J : C) {X Y : C}

/-- The action of `ihom J` on hom-categories, defined by currying precomposition with the
evaluation. However, the action on objects is only propositionally equal to `(ihom J).map`, so we
later define `ihomHomFunctor`, with the correct computation on objects. -/
def ihomHomFunctor' (X Y : C) : (X ⟶ Y) ⥤ ((J ⟶[C] X) ⟶ (J ⟶[C] Y)) :=
  precomp Y ((ihom.ev J).app X) ⋙ curryFunctor J (J ⟶[C] X) Y

@[simp]
lemma ihomHomFunctor'_obj (f : X ⟶ Y) :
    (ihomHomFunctor' J X Y).obj f = curry ((ihom.ev J).app X ≫ f) :=
  rfl

/-- The action of `ihom J` on hom-categories, satisfying
`(ihomHomFunctor J X Y).obj f = (ihom J).map f` definitionally. -/
def ihomHomFunctor (X Y : C) : (X ⟶ Y) ⥤ ((J ⟶[C] X) ⟶ (J ⟶[C] Y)) :=
  (ihomHomFunctor' J X Y).copyObj (fun f ↦ (ihom J).map f) (fun f ↦ eqToIso (by simp))

@[simp]
lemma ihomHomFunctor_obj (f : X ⟶ Y) :
    (ihomHomFunctor J X Y).obj f = (ihom J).map f :=
  rfl

lemma ihomHomFunctor_map {f g : X ⟶ Y} (η : f ⟶ g) :
    (ihomHomFunctor J X Y).map η =
      eqToHom (by simp) ≫ (ihomHomFunctor' J X Y).map η ≫ eqToHom (by simp) :=
  rfl

lemma ihomHomFunctor_eq_ihomHomFunctor' (X Y : C) :
    ihomHomFunctor J X Y = ihomHomFunctor' J X Y :=
  Functor.ext (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [ihomHomFunctor_map])

-- TODO: Generalize this to the corresponding fact about adjunctions between bicategories.
@[simp]
lemma uncurryFunctor_map_ihomHomFunctor_map {f g : X ⟶ Y} (η : f ⟶ g) :
    (uncurryFunctor J (J ⟶[C] X) Y).map ((ihomHomFunctor J X Y).map η) =
      eqToHom (by simp) ≫ (ihom.ev J).app X ◁ η ≫ eqToHom (by simp) := by
  have h := Functor.congr_hom (uncurryIso J (J ⟶[C] X) Y).counitIso
    ((precomp Y ((ihom.ev J).app X)).map η)
  simp only [uncurryIso, Functor.comp_map, precomp_map] at h
  simp [ihomHomFunctor_map, ihomHomFunctor', eqToHom_map, h]

/-- Another version of `uncurryFunctor_map_ihomHomFunctor_map` with `uncurryFunctor` unfolded. -/
@[simp]
lemma tensorLeftHomFunctor_map_ihomHomFunctor_whiskerRight_ev {f g : X ⟶ Y} (η : f ⟶ g) :
    (tensorLeftHomFunctor J (J ⟶[C] X) (J ⟶[C] Y)).map ((ihomHomFunctor J X Y).map η) ▷
        (ihom.ev J).app Y =
      eqToHom (by simp) ≫ (ihom.ev J).app X ◁ η ≫ eqToHom (by simp) :=
  uncurryFunctor_map_ihomHomFunctor_map J η

set_option backward.isDefEq.respectTransparency false in
lemma ihomHomFunctor_map_whiskerLeft {X' : C} (f : X' ⟶ X) {g g' : X ⟶ Y} (η : g ⟶ g') :
    (ihomHomFunctor J X' Y).map (f ◁ η) =
      eqToHom (by simp) ≫ (ihomHomFunctor J X' X).obj f ◁ (ihomHomFunctor J X Y).map η ≫
        eqToHom (by simp) := by
  apply (uncurryFunctor J (J ⟶[C] X') Y).map_injective
  rw [uncurryFunctor_map_ihomHomFunctor_map]
  simp [eqToHom_map, uncurryFunctor_map, tensorLeftHomFunctor_map_whiskerLeft,
    Strict.associator_eqToIso, whiskerLeft_whiskerLeft_strict,
    congr_whiskerLeft (ihom.ev_naturality J f) η, -comp_whiskerLeft, -tensorLeftHomFunctor_map]

lemma ihomHomFunctor_map_whiskerRight {f f' : X ⟶ Y} (η : f ⟶ f') {Y' : C} (g : Y ⟶ Y') :
    (ihomHomFunctor J X Y').map (η ▷ g) =
      eqToHom (by simp) ≫ (ihomHomFunctor J X Y).map η ▷ (ihomHomFunctor J Y Y').obj g ≫
        eqToHom (by simp) := by
  apply (uncurryFunctor J (J ⟶[C] X) Y').map_injective
  rw [uncurryFunctor_map_ihomHomFunctor_map]
  simp [eqToHom_map, uncurryFunctor_map, tensorLeftHomFunctor_map_whiskerRight,
    Strict.associator_eqToIso, whiskerRight_whiskerRight_strict,
    whiskerRight_congr (ihom.ev_naturality J g), -tensorLeftHomFunctor_map]

/-- `ihom J` as a strict pseudofunctor `C ⥤ C`, with hom-functors given by `ihomHomFunctor J`. -/
def ihomPseudofunctor : StrictPseudofunctor C C := .mk'' {
    toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun X => J ⟶[C] X) (ihomHomFunctor J)
    map_id _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
    map_comp _ _ := by simp [PrelaxFunctor.mkOfHomFunctors]
    map₂_whisker_left := ihomHomFunctor_map_whiskerLeft J
    map₂_whisker_right η g := ihomHomFunctor_map_whiskerRight J η g
  }

@[simp]
lemma ihomPseudofunctor_map {f : X ⟶ Y} : (ihomPseudofunctor J).map f = (ihom J).map f :=
  rfl

lemma ihomPseudofunctor_map₂ {f g : X ⟶ Y} (η : f ⟶ g) :
    (ihomPseudofunctor J).map₂ η = (ihomHomFunctor J X Y).map η :=
  rfl

end IhomPseudofunctor

variable {J : C}

-- TODO: Once we have strict natural transformations, `const` should be made into one, with this
-- lemma as one of the fields.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 2-naturality of the transformation `const J : 𝟭 C ⟶ ihom J`. -/
lemma const_naturality₂ {X Y : C} {f g : X ⟶ Y} (η : f ⟶ g) :
    (const J).app X ◁ (ihomPseudofunctor J).map₂ η =
      eqToHom (by simp) ≫ η ▷ (const J).app Y ≫ eqToHom (by simp) := by
  rw [ihomPseudofunctor_map₂]
  apply (uncurryFunctor J X Y).map_injective
  simp [eqToHom_map, uncurryFunctor_map, tensorLeftHomFunctor_map_whiskerLeft,
    tensorLeftHomFunctor_map_whiskerRight, Strict.associator_eqToIso,
    whiskerLeft_whiskerLeft_strict, congr_whiskerLeft (whiskerLeft_const_ev X) η,
    whiskerRight_whiskerRight_strict, whiskerRight_congr (whiskerLeft_const_ev Y),
    tensorLeftHomFunctor_map_whiskerRight_snd, -tensorLeftHomFunctor_map]

end Strict.CartesianClosed

end

end CategoryTheory.Bicategory
