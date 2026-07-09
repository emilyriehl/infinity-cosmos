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
  is `tensorLeftMap₂ a η : a ◁ f ⟶ a ◁ g`, obtained by transporting `η` along
  `homTensorIsoProd`.
-/

universe w v u

namespace CategoryTheory.Bicategory

open Opposite MonoidalCategory CartesianMonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

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

/-- The isomorphism of categories `(a ⟶ x ⊗ y) ≅ (a ⟶ x) × (a ⟶ y)` coming from the
monoidality of the hom functor `(a ⟶ ·) : C ⥤ Cat`. -/
def homTensorIsoProd (a x y : C) : IsoCat (a ⟶ x ⊗ y) ((a ⟶ x) × (a ⟶ y)) :=
  let F := (homFunctor C).obj (op a)
  { functor := (δ F x y).toFunctor
    inverse := (μ F x y).toFunctor
    unitIso := congr(($(δ_μ F x y)).toFunctor).symm
    counitIso := congr(($(μ_δ F x y)).toFunctor) }

noncomputable def homTensorIsoProd' (a x y : C) : IsoCat (a ⟶ x ⊗ y) ((a ⟶ x) × (a ⟶ y)) :=
  IsoCat.ofIso <| asIso (prodComparison ((homFunctor C).obj (op a)) x y)

lemma homTensorIsoProd'_inv (a x y : C) :
  (homTensorIsoProd' a x y).inverse =
    (inv (prodComparison ((homFunctor C).obj (op a)) x y)).toFunctor :=
  rfl

lemma homTensorIsoProd_inverse_obj' (a x y : C) (p : (a ⟶ x) × (a ⟶ y)) :
    (homTensorIsoProd' a x y).inverse.obj p = lift p.1 p.2 := by
  set F := (homFunctor C).obj (op a)
  apply hom_ext
  · rw [lift_fst]
    exact congr(($(inv_prodComparison_map_fst F x y)).toFunctor.obj p)
  · rw [lift_snd]
    exact congr(($(inv_prodComparison_map_snd F x y)).toFunctor.obj p)

/-- The inverse of `homTensorIsoProd` sends a pair of morphisms to their `lift`. -/
@[simp]
lemma homTensorIsoProd_inverse_obj (a x y : C) (p : (a ⟶ x) × (a ⟶ y)) :
    (homTensorIsoProd a x y).inverse.obj p = lift p.1 p.2 := by
  set F := (homFunctor C).obj (op a)
  apply hom_ext
  · exact congr(($(μ_fst F x y)).toFunctor.obj p).trans (lift_fst _ _).symm
  · exact congr(($(μ_snd F x y)).toFunctor.obj p).trans (lift_snd _ _).symm

/-- The functor `(x ⟶ y) ⥤ (a ⊗ x ⟶ a ⊗ y)` underlying the action on 2-cells of `tensorLeft a`.
On objects it sends `f` to (something equal to) `a ◁ f`; see `tensorLeftMap₂Functor_obj`. -/
def tensorLeftMap₂Functor (a x y : C) : (x ⟶ y) ⥤ (a ⊗ x ⟶ a ⊗ y) :=
  Functor.prod' ((Functor.const _).obj (fst a x)) (precomp y (snd a x)) ⋙
    (homTensorIsoProd (a ⊗ x) a y).inverse

@[simp]
lemma tensorLeftMap₂Functor_obj (a : C) {x y : C} (f : x ⟶ y) :
    (tensorLeftMap₂Functor a x y).obj f = a ◁ f := by
  unfold tensorLeftMap₂Functor
  apply hom_ext <;> simp

/-- The action on 2-cells of `tensorLeft a`: a 2-cell `η : f ⟶ g` between `f g : x ⟶ y` is
transported to a 2-cell `a ◁ f ⟶ a ◁ g` using the inverse of `homTensorIsoProd`. -/
def tensorLeftMap₂ (a : C) {x y : C} {f g : x ⟶ y} (η : f ⟶ g) : a ◁ f ⟶ a ◁ g :=
  eqToHom (tensorLeftMap₂Functor_obj a f).symm ≫
    (tensorLeftMap₂Functor a x y).map η ≫ eqToHom (tensorLeftMap₂Functor_obj a g)

@[simp]
lemma tensorLeftMap₂_id (a : C) {x y : C} (f : x ⟶ y) :
    tensorLeftMap₂ a (𝟙 f) = 𝟙 (a ◁ f) := by
  rw [tensorLeftMap₂, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

@[simp]
lemma tensorLeftMap₂_comp (a : C) {x y : C} {f g h : x ⟶ y} (η : f ⟶ g) (θ : g ⟶ h) :
    tensorLeftMap₂ a (η ≫ θ) = tensorLeftMap₂ a η ≫ tensorLeftMap₂ a θ := by
  rw [tensorLeftMap₂, tensorLeftMap₂, tensorLeftMap₂, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

section WhiskerLaws

variable {Z x y : C} {r s : Z ⟶ x ⊗ y} {θ θ' : r ⟶ s}

#synth IsIso (prodComparison ((homFunctor C).obj (op Z)) x y)

lemma homFunctor_hom_ext' {Z x y : C} {r s : Z ⟶ x ⊗ y} {θ θ' : r ⟶ s}
    (hfst : θ ▷ fst x y = θ' ▷ fst x y) (hsnd : θ ▷ snd x y = θ' ▷ snd x y) : θ = θ' := by
  have : (homTensorIsoProd Z x y).inverse.Faithful :=
    (homTensorIsoProd Z x y).symm.toEquivalence.faithful_functor
  have foo := (homTensorIsoProd Z x y).inverse.map_injective
    (X := (r ≫ fst x y, r ≫ snd x y)) (Y := (s ≫ fst x y, s ≫ snd x y))
  dsimp at foo
  sorry


set_option backward.isDefEq.respectTransparency false
/-- Two 2-morphisms with the same source and target into a tensor `x ⊗ y` are equal as soon as
their whiskerings by `fst` and `snd` agree. This is joint monicity coming from the isomorphism of
categories `Hom(Z, x ⊗ y) ≅ Hom(Z, x) × Hom(Z, y)`. -/
lemma homFunctor_hom_ext {Z x y : C} {r s : Z ⟶ x ⊗ y} {θ θ' : r ⟶ s}
    (hfst : θ ▷ fst x y = θ' ▷ fst x y) (hsnd : θ ▷ snd x y = θ' ▷ snd x y) : θ = θ' := by
  have : (prodComparison ((homFunctor C).obj (op Z)) x y).toFunctor.Faithful :=
    (Cat.equivOfIso (asIso (prodComparison ((homFunctor C).obj (op Z)) x y))).faithful_functor
  apply (prodComparison ((homFunctor C).obj (op Z)) x y).toFunctor.map_injective
  -- simp [prodComparison, homFunctor, postcomp, lift, ]
  show ((θ ▷ fst x y, θ ▷ snd x y) : _ × _) = (θ' ▷ fst x y, θ' ▷ snd x y)
  rw [hfst, hsnd]

/-- The action of `tensorLeftMap₂Functor` on a 2-morphism, written as the image of an explicit
pair under the inverse of `homTensorIsoProd`. -/
lemma tensorLeftMap₂Functor_map (a : C) {x y : C} {f g : x ⟶ y} (η : f ⟶ g) :
    (tensorLeftMap₂Functor a x y).map η =
      (homTensorIsoProd (a ⊗ x) a y).inverse.map
        (X := (fst a x, snd a x ≫ f)) (Y := (fst a x, snd a x ≫ g))
        (Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ η)) :=
  rfl

/-- Whiskering `tensorLeftMap₂ a η` by `fst` gives an identity (up to `eqToHom`). -/
lemma tensorLeftMap₂_whiskerRight_fst (a : C) {x y : C} {f g : x ⟶ y} (η : f ⟶ g) :
    tensorLeftMap₂ a η ▷ fst a y = eqToHom (by simp) := by
  rw [tensorLeftMap₂]
  simp only [comp_whiskerRight, eqToHom_whiskerRight]
  have h : (homTensorIsoProd (a ⊗ x) a y).inverse.map (Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ η))
      ▷ fst a y = eqToHom (by simp) ≫ 𝟙 (fst a x) ≫ eqToHom (by simp) :=
    Functor.congr_hom congr(($(μ_fst ((homFunctor C).obj (op (a ⊗ x))) a y)).toFunctor)
      (Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ η))
  rw [tensorLeftMap₂Functor_map, h]
  simp

/-- Whiskering `tensorLeftMap₂ a η` by `snd` recovers `snd a x ◁ η` (up to `eqToHom`). -/
lemma tensorLeftMap₂_whiskerRight_snd (a : C) {x y : C} {f g : x ⟶ y} (η : f ⟶ g) :
    tensorLeftMap₂ a η ▷ snd a y = eqToHom (by simp) ≫ snd a x ◁ η ≫ eqToHom (by simp) := by
  rw [tensorLeftMap₂]
  simp only [comp_whiskerRight, eqToHom_whiskerRight]
  have h : (homTensorIsoProd (a ⊗ x) a y).inverse.map (Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ η))
      ▷ snd a y = eqToHom (by simp) ≫ snd a x ◁ η ≫ eqToHom (by simp) :=
    Functor.congr_hom congr(($(μ_snd ((homFunctor C).obj (op (a ⊗ x))) a y)).toFunctor)
      (Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ η))
  rw [tensorLeftMap₂Functor_map, h]
  simp

/-- The compatibility of `tensorLeftMap₂` with left whiskering. -/
lemma tensorLeftMap₂_whiskerLeft (a : C) {x y z : C} (f : x ⟶ y) {g g' : y ⟶ z} (η : g ⟶ g') :
    tensorLeftMap₂ a (f ◁ η) =
      eqToHom (by simp) ≫ (a ◁ f) ◁ tensorLeftMap₂ a η ≫ eqToHom (by simp) := by
  apply homFunctor_hom_ext
  · rw [tensorLeftMap₂_whiskerRight_fst]
    simp only [comp_whiskerRight, eqToHom_whiskerRight]
    rw [whisker_assoc_strict, tensorLeftMap₂_whiskerRight_fst]
    simp
  · rw [tensorLeftMap₂_whiskerRight_snd]
    simp only [comp_whiskerRight, eqToHom_whiskerRight]
    rw [whisker_assoc_strict, tensorLeftMap₂_whiskerRight_snd]
    simp only [whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc]
    rw [whiskerLeft_whiskerLeft_strict, whiskerLeft_whiskerLeft_strict,
      congr_whiskerLeft (whiskerLeft_snd a f) η]
    simp

/-- The compatibility of `tensorLeftMap₂` with right whiskering. -/
lemma tensorLeftMap₂_whiskerRight (a : C) {x y z : C} {f f' : x ⟶ y} (η : f ⟶ f') (g : y ⟶ z) :
    tensorLeftMap₂ a (η ▷ g) =
      eqToHom (by simp) ≫ tensorLeftMap₂ a η ▷ (a ◁ g) ≫ eqToHom (by simp) := by
  apply homFunctor_hom_ext
  · rw [tensorLeftMap₂_whiskerRight_fst]
    simp only [comp_whiskerRight, eqToHom_whiskerRight]
    rw [whiskerRight_whiskerRight_strict, whiskerRight_congr (whiskerLeft_fst a g),
      tensorLeftMap₂_whiskerRight_fst]
    simp
  · rw [tensorLeftMap₂_whiskerRight_snd]
    simp only [comp_whiskerRight, eqToHom_whiskerRight]
    rw [whiskerRight_whiskerRight_strict, whiskerRight_congr (whiskerLeft_snd a g),
      whiskerRight_comp_strict, tensorLeftMap₂_whiskerRight_snd]
    simp only [comp_whiskerRight, eqToHom_whiskerRight]
    rw [whisker_assoc_strict]
    simp

end WhiskerLaws

/-- Tensoring on the left with an object `a`, as the data of a strict pseudofunctor `C ⥤ C`:
it acts on objects by `a ⊗ ·`, on 1-cells by `a ◁ ·`, and on 2-cells by `tensorLeftMap₂ a`. -/
def tensorLeft (a : C) : StrictPseudofunctorPreCore C C where
  obj c := a ⊗ c
  map f := a ◁ f
  map₂ η := tensorLeftMap₂ a η
  map_id _ := by simp
  map_comp _ _ := by simp
  map₂_whisker_left := tensorLeftMap₂_whiskerLeft a
  map₂_whisker_right := tensorLeftMap₂_whiskerRight a

end Strict.CartesianMonoidal

end CategoryTheory.Bicategory
