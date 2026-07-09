import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.IsoCat

/-!
# Cartesian monoidal strict bicategories

A strict bicategory `C` whose underlying category is cartesian monoidal is *cartesian monoidal*
as a bicategory if its products are 2-categorical (conical) products, i.e. if for every object
`Z` the hom functor `(Z ⟶ ·) : C ⥤ Cat` is monoidal; equivalently, the canonical comparison
functor `(Z ⟶ x ⊗ y) ⥤ (Z ⟶ x) × (Z ⟶ y)` is an isomorphism of categories.

## Main definitions

* `CategoryTheory.Bicategory.Strict.CartesianMonoidal`: the typeclass of cartesian monoidal
  strict bicategories.
* `CategoryTheory.Bicategory.Strict.CartesianMonoidal.homTensorIsoProd`: the isomorphism of
  categories `(a ⟶ x ⊗ y) ≅ (a ⟶ x) × (a ⟶ y)`.
* `CategoryTheory.Bicategory.Strict.CartesianMonoidal.tensorLeft`: tensoring on the left
  `a ⊗ ·` as the data of a strict pseudofunctor `C ⥤ C`. Its action on a 2-cell `η : f ⟶ g`
  is `(tensorLeftHomFunctor a x y).map η : a ◁ f ⟶ a ◁ g`, obtained by transporting `η` along
  `homTensorIsoProd`.
-/

universe w v u

namespace CategoryTheory.Bicategory

open Opposite MonoidalCategory CartesianMonoidalCategory

-- Some needed simp lemmas
@[simp]
lemma Cat.fst_toFunctor_obj {X Y : Cat} (p : ↥(X ⊗ Y)) : (fst X Y).toFunctor.obj p = p.1 := rfl

@[simp]
lemma Cat.snd_toFunctor_obj {X Y : Cat} (p : ↥(X ⊗ Y)) : (snd X Y).toFunctor.obj p = p.2 := rfl

universe v₁ u₁

/-- An isomorphism `e : X ≅ Y` in `Cat` gives an isomorphism of categories between the
underlying categories of `X` and `Y`. -/
def IsoCat.ofIso {X Y : Cat.{v₁, u₁}} (e : X ≅ Y) : IsoCat X Y where
  functor := e.hom.toFunctor
  inverse := e.inv.toFunctor
  unitIso := congr(($(e.hom_inv_id)).toFunctor).symm
  counitIso := congr(($(e.inv_hom_id)).toFunctor)

section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

@[simp]
lemma lift_eq_whiskerLeft  {a x y : C} (f : x ⟶ y) :
    lift (fst a x) (snd a x ≫ f) = a ◁ f := by
  ext <;> simp

@[simp]
lemma lift_eq_whiskerRight  {x y a : C} (f : x ⟶ y) :
    lift (fst x a ≫ f) (snd x a) = f ▷ a := by
  ext <;> simp

end

variable (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C]

/-- A strict bicategory is *cartesian monoidal* if its underlying category is cartesian monoidal
and, for every object `Z`, the hom functor `(Z ⟶ ·) : C ⥤ Cat` is monoidal. The latter condition
says that the canonical functor `(Z ⟶ x ⊗ y) ⥤ (Z ⟶ x) × (Z ⟶ y)` is an isomorphism of
categories, i.e. that `x ⊗ y` is a 2-categorical (conical) product. -/
class Strict.CartesianMonoidal extends CartesianMonoidalCategory C where
  /-- For every object `Z`, the hom functor `(Z ⟶ ·) : C ⥤ Cat` is monoidal. -/
  isMonoidal (Z : C) : ((homFunctor C).obj (op Z)).Monoidal

attribute [reducible, instance] Strict.CartesianMonoidal.isMonoidal

namespace Strict.CartesianMonoidal

variable {C} [Strict.CartesianMonoidal C]


noncomputable def homTensorIsoProd_func (a x y : C) : (a ⟶ x ⊗ y) ⥤ ((a ⟶ x) × (a ⟶ y)) :=
  (prodComparison ((homFunctor C).obj (op a)) x y).toFunctor

lemma homTensorIsoProd_func_obj (a x y : C) (f : a ⟶ x ⊗ y) :
    (homTensorIsoProd_func a x y).obj f = (f ≫ fst x y, (f ≫ snd x y)) :=
  rfl

/-- The inverse comparison functor sends a pair of morphisms to their `lift`. -/
@[simp]
lemma inv_prodComparison_toFunctor_obj (a x y : C) (p : (a ⟶ x) × (a ⟶ y)) :
    (inv (prodComparison ((homFunctor C).obj (op a)) x y)).toFunctor.obj p = lift p.1 p.2 := by
  set F := (homFunctor C).obj (op a)
  apply hom_ext
  · rw [lift_fst]
    exact congr(($(inv_prodComparison_map_fst F x y)).toFunctor.obj p)
  · rw [lift_snd]
    exact congr(($(inv_prodComparison_map_snd F x y)).toFunctor.obj p)

set_option backward.isDefEq.respectTransparency false in
noncomputable def homTensorIsoProd_inv (a x y : C) : ((a ⟶ x) × (a ⟶ y)) ⥤ (a ⟶ x ⊗ y) where
  obj p := lift p.1 p.2
  map {p q} f :=
    eqToHom (by simp) ≫
      (inv (prodComparison ((homFunctor C).obj (op a)) x y)).toFunctor.map f ≫ eqToHom (by simp)
  map_id p := by
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

@[simp]
lemma homTensorIsoProd_inv_obj (a x y : C) (p : (a ⟶ x) × (a ⟶ y)) :
    (homTensorIsoProd_inv a x y).obj p = lift p.1 p.2 :=
  rfl

/-- `homTensorIsoProd_inv` agrees with the raw inverse comparison functor; they differ only by the
`eqToHom` decorations that make its object action compute to `lift`. -/
lemma homTensorIsoProd_inv_eq (a x y : C) :
    homTensorIsoProd_inv a x y =
      (inv (prodComparison ((homFunctor C).obj (op a)) x y)).toFunctor := by
  refine Functor.ext (fun p => (inv_prodComparison_toFunctor_obj a x y p).symm) ?_
  intro p q f
  simp [homTensorIsoProd_inv]

/-- The isomorphism of categories `(a ⟶ x ⊗ y) ≅ (a ⟶ x) × (a ⟶ y)`, assembled from the
comparison functor `homTensorIsoProd_func` and its inverse `homTensorIsoProd_inv`. -/
@[simps!]
noncomputable def homTensorIsoProd (a x y : C) : IsoCat (a ⟶ x ⊗ y) ((a ⟶ x) × (a ⟶ y)) where
  functor := homTensorIsoProd_func a x y
  inverse := homTensorIsoProd_inv a x y
  unitIso := by
    rw [homTensorIsoProd_inv_eq, homTensorIsoProd_func]
    exact congr(($((asIso (prodComparison ((homFunctor C).obj (op a)) x y)).hom_inv_id)).toFunctor).symm
  counitIso := by
    rw [homTensorIsoProd_inv_eq, homTensorIsoProd_func]
    exact congr(($((asIso (prodComparison ((homFunctor C).obj (op a)) x y)).inv_hom_id)).toFunctor)

set_option backward.isDefEq.respectTransparency false in
/-- Whiskering `homTensorIsoProd_inv.map ρ` by `fst` recovers the first component. -/
lemma homTensorIsoProd_inv_map_whiskerRight_fst {a x y : C} {p q : (a ⟶ x) × (a ⟶ y)} (ρ : p ⟶ q) :
    (homTensorIsoProd_inv a x y).map ρ ▷ fst x y = eqToHom (by simp) ≫ ρ.1 ≫ eqToHom (by simp) := by
  have h : (inv (prodComparison ((homFunctor C).obj (op a)) x y)).toFunctor.map ρ ▷ fst x y
      = eqToHom (by simp) ≫ ρ.1 ≫ eqToHom (by simp) :=
    Functor.congr_hom
      congr(($(inv_prodComparison_map_fst ((homFunctor C).obj (op a)) x y)).toFunctor) _
  simp [homTensorIsoProd_inv, h]

set_option backward.isDefEq.respectTransparency false in
/-- Whiskering `homTensorIsoProd_inv.map ρ` by `snd` recovers the second component. -/
lemma homTensorIsoProd_inv_map_whiskerRight_snd {a x y : C} {p q : (a ⟶ x) × (a ⟶ y)} (ρ : p ⟶ q) :
    (homTensorIsoProd_inv a x y).map ρ ▷ snd x y = eqToHom (by simp) ≫ ρ.2 ≫ eqToHom (by simp) := by
  have h : (inv (prodComparison ((homFunctor C).obj (op a)) x y)).toFunctor.map ρ ▷ snd x y
      = eqToHom (by simp) ≫ ρ.2 ≫ eqToHom (by simp) :=
    Functor.congr_hom
      congr(($(inv_prodComparison_map_snd ((homFunctor C).obj (op a)) x y)).toFunctor) _
  simp [homTensorIsoProd_inv, h]

lemma homFunctor_hom_ext {Z x y : C} {r s : Z ⟶ x ⊗ y} {θ θ' : r ⟶ s}
    (hfst : θ ▷ fst x y = θ' ▷ fst x y) (hsnd : θ ▷ snd x y = θ' ▷ snd x y) : θ = θ' :=
  (homTensorIsoProd Z x y).functor.map_injective (Prod.ext hfst hsnd)

/-- The hom functor `(x ⟶ y) ⥤ (a ⊗ x ⟶ a ⊗ y)` of `tensorLeft a`: it sends `f` to `a ◁ f`
on the nose, and a 2-cell `η : f ⟶ g` to a 2-cell `a ◁ f ⟶ a ◁ g` obtained by transporting `η`
along the inverse of `homTensorIsoProd`. -/
@[simps]
noncomputable def tensorLeftHomFunctor (a x y : C) : (x ⟶ y) ⥤ (a ⊗ x ⟶ a ⊗ y) where
  obj f := a ◁ f
  map η := eqToHom (by simp) ≫ (homTensorIsoProd_inv (a ⊗ x) a y).map
        (Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ η)) ≫ eqToHom (by simp)
  map_id f := by simp [← prod_id]
  map_comp f g := by
    have h : Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ f ≫ snd a x ◁ g) =
        Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ f) ≫ Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ g) := by
      simp
    simp only [whiskerLeft_comp, h, Functor.map_comp, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

section WhiskerLaws

set_option backward.isDefEq.respectTransparency false in
/-- Whiskering `(tensorLeftHomFunctor a x y).map η` by `fst` gives an identity (up to
`eqToHom`). -/
lemma tensorLeftHomFunctor_map_whiskerRight_fst (a : C) {x y : C} {f g : x ⟶ y} (η : f ⟶ g) :
    (tensorLeftHomFunctor a x y).map η ▷ fst a y = eqToHom (by simp) := by
  rw [tensorLeftHomFunctor_map]
  simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc,
    homTensorIsoProd_inv_map_whiskerRight_fst]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Whiskering `(tensorLeftHomFunctor a x y).map η` by `snd` recovers `snd a x ◁ η` (up to
`eqToHom`). -/
lemma tensorLeftHomFunctor_map_whiskerRight_snd (a : C) {x y : C} {f g : x ⟶ y} (η : f ⟶ g) :
    (tensorLeftHomFunctor a x y).map η ▷ snd a y =
      eqToHom (by simp) ≫ snd a x ◁ η ≫ eqToHom (by simp) := by
  rw [tensorLeftHomFunctor_map]
  simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc,
    homTensorIsoProd_inv_map_whiskerRight_snd]
  simp

/-- The compatibility of the 2-cell action of `tensorLeftHomFunctor` with left whiskering. -/
lemma tensorLeftHomFunctor_map_whiskerLeft (a : C) {x y z : C} (f : x ⟶ y) {g g' : y ⟶ z}
    (η : g ⟶ g') :
    (tensorLeftHomFunctor a x z).map (f ◁ η) =
      eqToHom (by simp) ≫ (a ◁ f) ◁ (tensorLeftHomFunctor a y z).map η ≫ eqToHom (by simp) := by
  apply homFunctor_hom_ext
  · simp only [tensorLeftHomFunctor_map_whiskerRight_fst, comp_whiskerRight, whisker_assoc_strict]
    simp
  · simp only [tensorLeftHomFunctor_map_whiskerRight_snd, comp_whiskerRight, eqToHom_whiskerRight]
    rw [whisker_assoc_strict, tensorLeftHomFunctor_map_whiskerRight_snd]
    simp only [whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc]
    rw [whiskerLeft_whiskerLeft_strict, whiskerLeft_whiskerLeft_strict,
      congr_whiskerLeft (whiskerLeft_snd a f) η]
    simp

/-- The compatibility of the 2-cell action of `tensorLeftHomFunctor` with right whiskering. -/
lemma tensorLeftHomFunctor_map_whiskerRight (a : C) {x y z : C} {f f' : x ⟶ y} (η : f ⟶ f')
    (g : y ⟶ z) :
    (tensorLeftHomFunctor a x z).map (η ▷ g) =
      eqToHom (by simp) ≫ (tensorLeftHomFunctor a x y).map η ▷ (a ◁ g) ≫ eqToHom (by simp) := by
  apply homFunctor_hom_ext
  · simp only [tensorLeftHomFunctor_map_whiskerRight_fst, comp_whiskerRight, eqToHom_whiskerRight]
    rw [whiskerRight_whiskerRight_strict, whiskerRight_congr (whiskerLeft_fst a g),
      tensorLeftHomFunctor_map_whiskerRight_fst]
    simp
  · simp only [tensorLeftHomFunctor_map_whiskerRight_snd, comp_whiskerRight, eqToHom_whiskerRight]
    rw [whiskerRight_whiskerRight_strict, whiskerRight_congr (whiskerLeft_snd a g),
      whiskerRight_comp_strict, tensorLeftHomFunctor_map_whiskerRight_snd]
    simp only [comp_whiskerRight, eqToHom_whiskerRight]
    rw [whisker_assoc_strict]
    simp

end WhiskerLaws

/-- Tensoring on the left with an object `a`, as the data of a strict pseudofunctor `C ⥤ C`:
it acts on objects by `a ⊗ ·`, on 1-cells by `a ◁ ·`, and on 2-cells by the action of
`tensorLeftHomFunctor a`. -/
noncomputable def tensorLeft (a : C) : StrictPseudofunctorPreCore C C where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun c => a ⊗ c) (tensorLeftHomFunctor a)
  map_id _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
  map_comp _ _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
  map₂_whisker_left := tensorLeftHomFunctor_map_whiskerLeft a
  map₂_whisker_right := tensorLeftHomFunctor_map_whiskerRight a

end Strict.CartesianMonoidal

end CategoryTheory.Bicategory
