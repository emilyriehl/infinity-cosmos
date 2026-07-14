import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.IsoCat

/-!
# Cartesian monoidal strict bicategories

A strict bicategory `C` whose underlying category is cartesian monoidal is *cartesian monoidal*
as a bicategory if if for every object `a : C` the hom functor `(a ⟶ ·) : C ⥤ Cat` is monoidal;
equivalently, the canonical comparison functor `(a ⟶ x ⊗ y) ⥤ (a ⟶ x) × (a ⟶ y)` is an isomorphism
of categories.

## Main definitions

* `CategoryTheory.Bicategory.Strict.CartesianMonoidal`: the typeclass of cartesian monoidal
  strict bicategories.
* `CategoryTheory.Bicategory.Strict.CartesianMonoidal.liftIso`: the isomorphism of
  categories `(a ⟶ x) × (a ⟶ y) ≅ (a ⟶ x ⊗ y)`.
* `CategoryTheory.Bicategory.Strict.CartesianMonoidal.tensorLeft`: tensoring on the left
  `a ⊗ ·` as the data of a strict pseudofunctor `C ⥤ C`.
* `CategoryTheory.Bicategory.Strict.CartesianMonoidal.const`: the constant-diagram natural
  transformation `Δ : 𝟭 C ⟶ ihom J`, currying the projection, together with its strict
  naturality (`const_ihom`).
-/

universe w v u

namespace CategoryTheory.Bicategory

open Opposite MonoidalCategory CartesianMonoidalCategory MonoidalClosed

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
lemma lift_eq_whiskerLeft {a x y : C} (f : x ⟶ y) :
    lift (fst a x) (snd a x ≫ f) = a ◁ f := by
  ext <;> simp

@[simp]
lemma lift_eq_whiskerRight {x y a : C} (f : x ⟶ y) :
    lift (fst x a ≫ f) (snd x a) = f ▷ a := by
  ext <;> simp

end

variable (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C]

/-- A strict bicategory is *cartesian monoidal* if its underlying category is cartesian monoidal
and, for every object `a : C`, the hom functor `(a ⟶ ·) : C ⥤ Cat` is monoidal. -/
class Strict.CartesianMonoidal extends CartesianMonoidalCategory C where
  isMonoidal (Z : C) : ((homFunctor C).obj (op Z)).Monoidal

attribute [reducible, instance] Strict.CartesianMonoidal.isMonoidal

namespace Strict.CartesianMonoidal

variable {C} [Strict.CartesianMonoidal C]
variable (A X Y : C)

/-- The induced canonical functor `(a ⟶ x ⊗ y) ⥤ ((a ⟶ x) × (a ⟶ y))` for a cartesian monoidal
strict bicategory. -/
def liftFunctorInv : (A ⟶ X ⊗ Y) ⥤ ((A ⟶ X) × (A ⟶ Y)) :=
  (prodComparison ((homFunctor C).obj (op A)) X Y).toFunctor

@[simp]
lemma liftFunctorInv_obj (f : A ⟶ X ⊗ Y) :
    (liftFunctorInv A X Y).obj f = (f ≫ fst X Y, (f ≫ snd X Y)) :=
  rfl

/-- The induced canonical functor `((a ⟶ x) × (a ⟶ y)) ⥤ (a ⟶ x ⊗ y)` for a cartesian monoidal
strict bicategory. However, the action on objects is not definitional to the expected one, so we
later define `liftFunctor`, with the correct computation on objects.  -/
noncomputable def liftFunctor' : ((A ⟶ X) × (A ⟶ Y)) ⥤ (A ⟶ X ⊗ Y) :=
  (inv (prodComparison ((homFunctor C).obj (op A)) X Y)).toFunctor

@[simp]
lemma liftFunctor'_obj {a x y : C} (p : (a ⟶ x) × (a ⟶ y)) :
    (liftFunctor' a x y).obj p = lift p.1 p.2 := by
  set F := (homFunctor C).obj (op a)
  apply hom_ext
  · rw [lift_fst]
    exact congr(($(inv_prodComparison_map_fst F x y)).toFunctor.obj p)
  · rw [lift_snd]
    exact congr(($(inv_prodComparison_map_snd F x y)).toFunctor.obj p)

/-- The induced canonical functor `liftFunctor : ((a ⟶ x) × (a ⟶ y)) ⥤ (a ⟶ x ⊗ y)` for a cartesian
monoidal strict bicategory, satisfying `(liftFunctor a x y).obj p = lift p.1 p.2` definitionally. -/
noncomputable def liftFunctor : ((A ⟶ X) × (A ⟶ Y)) ⥤ (A ⟶ X ⊗ Y) :=
  (liftFunctor' A X Y).copyObj  (fun p ↦ lift p.1 p.2) (fun p ↦ eqToIso (by simp))

@[simp]
lemma liftFunctor_obj (p : (A ⟶ X) × (A ⟶ Y)) :
  (liftFunctor A X Y).obj p = lift p.1 p.2 := rfl

lemma liftFunctor_map (p q : (A ⟶ X) × (A ⟶ Y)) (η : p ⟶ q) :
  (liftFunctor A X Y).map η =
    eqToHom (by simp) ≫ (liftFunctor' A X Y).map η ≫ eqToHom (by simp) := rfl

lemma liftFunctor_eq_liftFunctor' :
    liftFunctor A X Y = liftFunctor' A X Y :=
  Functor.ext (fun p ↦ (liftFunctor'_obj p).symm) (fun _ _ _ ↦ by simp [liftFunctor_map])

/-- The canonical isomorphism of categories `((a ⟶ x) × (a ⟶ y)) ≅ (a ⟶ x ⊗ y)` for a cartesian
monoidal strict bicategory. -/
@[simps!]
noncomputable def liftIso : IsoCat ((A ⟶ X) × (A ⟶ Y)) (A ⟶ X ⊗ Y) where
  functor := liftFunctor A X Y
  inverse := liftFunctorInv A X Y
  unitIso := by
    rw [liftFunctor_eq_liftFunctor', liftFunctorInv]
    exact congr(($((asIso (prodComparison ((homFunctor C).obj (op A)) X Y)).inv_hom_id)).toFunctor).symm
  counitIso := by
    rw [liftFunctor_eq_liftFunctor', liftFunctorInv]
    exact congr(($((asIso (prodComparison ((homFunctor C).obj (op A)) X Y)).hom_inv_id)).toFunctor)

@[ext]
lemma hom₂_ext {a x y : C} {r s : a ⟶ x ⊗ y} {θ θ' : r ⟶ s}
    (hfst : θ ▷ fst x y = θ' ▷ fst x y) (hsnd : θ ▷ snd x y = θ' ▷ snd x y) : θ = θ' :=
  (liftIso a x y).symm.functor.map_injective (Prod.ext hfst hsnd)

set_option backward.isDefEq.respectTransparency false in
lemma liftFunctor_map_whiskerRight_fst {a x y : C} {p q : (a ⟶ x) × (a ⟶ y)} (ρ : p ⟶ q) :
    (liftFunctor a x y).map ρ ▷ fst x y = eqToHom (by simp) ≫ ρ.1 ≫ eqToHom (by simp) := by
  simpa [liftFunctor_map, homFunctor, Functor.toCatHom] using
    congr(($(Functor.congr_hom (liftIso a x y).unitIso.symm ρ)).1)

set_option backward.isDefEq.respectTransparency false in
lemma liftFunctor_map_whiskerRight_snd {a x y : C} {p q : (a ⟶ x) × (a ⟶ y)} (ρ : p ⟶ q) :
    (liftFunctor a x y).map ρ ▷ snd x y = eqToHom (by simp) ≫ ρ.2 ≫ eqToHom (by simp) := by
  simpa [liftFunctor_map, homFunctor, Functor.toCatHom] using
    congr(($(Functor.congr_hom (liftIso a x y).unitIso.symm ρ)).2)

section WhiskerLaws

variable (a : C) {x y z : C}

/-- The hom functor `(x ⟶ y) ⥤ (a ⊗ x ⟶ a ⊗ y)` of of the strict pseudofunctor that tensors with
`a` on the left. -/
@[simps]
noncomputable def tensorLeftHomFunctor (x y : C) : (x ⟶ y) ⥤ (a ⊗ x ⟶ a ⊗ y) where
  obj f := a ◁ f
  map η := eqToHom (by simp) ≫ (liftFunctor (a ⊗ x) a y).map
        (Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ η)) ≫ eqToHom (by simp)
  map_id f := by simp [← prod_id]
  map_comp f g := by
    have h : Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ f ≫ snd a x ◁ g) =
        Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ f) ≫ Prod.mkHom (𝟙 (fst a x)) (snd a x ◁ g) := by
      simp
    simp only [whiskerLeft_comp, h, Functor.map_comp, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
lemma tensorLeftHomFunctor_map_whiskerRight_fst {f g : x ⟶ y} (η : f ⟶ g) :
    (tensorLeftHomFunctor a x y).map η ▷ fst a y = eqToHom (by simp) := by
  simp [liftFunctor_map_whiskerRight_fst]

set_option backward.isDefEq.respectTransparency false in
lemma tensorLeftHomFunctor_map_whiskerRight_snd {f g : x ⟶ y} (η : f ⟶ g) :
    (tensorLeftHomFunctor a x y).map η ▷ snd a y =
      eqToHom (by simp) ≫ snd a x ◁ η ≫ eqToHom (by simp) := by
  simp [liftFunctor_map_whiskerRight_snd]

set_option backward.isDefEq.respectTransparency false in
lemma tensorLeftHomFunctor_map_whiskerLeft (f : x ⟶ y) {g g' : y ⟶ z} (η : g ⟶ g') :
    (tensorLeftHomFunctor a x z).map (f ◁ η) =
      eqToHom (by simp) ≫ (a ◁ f) ◁ (tensorLeftHomFunctor a y z).map η ≫ eqToHom (by simp) := by
  ext
  · simp [tensorLeftHomFunctor_map_whiskerRight_fst, Strict.associator_eqToIso,
      -tensorLeftHomFunctor_map]
  · simp [tensorLeftHomFunctor_map_whiskerRight_snd, Strict.associator_eqToIso,
      whiskerLeft_whiskerLeft_strict, congr_whiskerLeft (whiskerLeft_snd a f) η,
      -tensorLeftHomFunctor_map, -comp_whiskerLeft]

lemma tensorLeftHomFunctor_map_whiskerRight {f f' : x ⟶ y} (η : f ⟶ f') (g : y ⟶ z) :
    (tensorLeftHomFunctor a x z).map (η ▷ g) =
      eqToHom (by simp) ≫ (tensorLeftHomFunctor a x y).map η ▷ (a ◁ g) ≫ eqToHom (by simp) := by
  ext
  · simp [tensorLeftHomFunctor_map_whiskerRight_fst, whiskerRight_whiskerRight_strict,
      whiskerRight_congr (whiskerLeft_fst a g),
      -tensorLeftHomFunctor_map, -whisker_assoc]
  · simp [tensorLeftHomFunctor_map_whiskerRight_snd, whiskerRight_whiskerRight_strict,
      whiskerRight_congr (whiskerLeft_snd a g), Strict.associator_eqToIso,
      -tensorLeftHomFunctor_map]

end WhiskerLaws

/-- The strict pseudofunctor `C ⥤ C` that tensors on the left with a given 0-cell. -/
noncomputable def tensorLeft (a : C) : StrictPseudofunctor C C := .mk'' {
    toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun c => a ⊗ c) (tensorLeftHomFunctor a)
    map_id _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
    map_comp _ _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
    map₂_whisker_left := tensorLeftHomFunctor_map_whiskerLeft a
    map₂_whisker_right := tensorLeftHomFunctor_map_whiskerRight a
  }

-- TODO: When porting upstream, this section should be generalized to semicartesian
-- monoidal 1-categories
section Const

variable [MonoidalClosed C]

/-- The "constant" morphism `Δ : 𝟭 C ⟶ ihom J`, whose component at `A` is the currying of the
projection `A ⊗ J ⟶ A`. -/
def const (J : C) : 𝟭 C ⟶ ihom J where
  app A := curry <| snd J A
  naturality A B η := by simp [← curry_natural_left, ← curry_natural_right]

variable {J A : C}

-- Helpful as the `𝟭 C` functor isn't totally transparent. We make this a simp lemma following
-- coev_naturality
@[simp]
lemma const_naturality {B} (u : A ⟶ B) : u ≫ (const J).app B = (const J).app A ≫ (ihom J).map u :=
  (const J).naturality u

@[simp]
lemma uncurry_const (X : C) :
    uncurry ((const J).app X) = snd J X := by
  simp [const]

@[simp]
lemma whiskerLeft_const_ev (X : C) :
    J ◁ (const J).app X ≫ (ihom.ev J).app X = snd J X := by
  rw [const, ← uncurry_eq, uncurry_curry]

end Const

end Strict.CartesianMonoidal

end CategoryTheory.Bicategory
