import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.IsoCat

/-!
# Cartesian monoidal strict bicategories
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
lemma lift_eq_whiskerLeft {A X Y : C} (f : X ⟶ Y) :
    lift (fst A X) (snd A X ≫ f) = A ◁ f := by
  ext <;> simp

@[simp]
lemma lift_eq_whiskerRight {X Y A : C} (f : X ⟶ Y) :
    lift (fst X A ≫ f) (snd X A) = f ▷ A := by
  ext <;> simp

end

variable (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C]

/-- A strict bicategory is *cartesian monoidal* if its underlying category is cartesian monoidal
and, for every object `A : C`, the hom functor `(A ⟶ ·) : C ⥤ Cat` is monoidal. -/
class Strict.CartesianMonoidal extends CartesianMonoidalCategory C where
  isMonoidal (A : C) : ((homFunctor C).obj (op A)).Monoidal

attribute [reducible, instance] Strict.CartesianMonoidal.isMonoidal

namespace Strict.CartesianMonoidal

variable {C} [Strict.CartesianMonoidal C]
variable (A X Y : C)

/-- The induced canonical functor `(A ⟶ X ⊗ Y) ⥤ ((A ⟶ X) × (A ⟶ Y))` for a cartesian monoidal
strict bicategory. -/
def liftFunctorInv : (A ⟶ X ⊗ Y) ⥤ ((A ⟶ X) × (A ⟶ Y)) :=
  (prodComparison ((homFunctor C).obj (op A)) X Y).toFunctor

@[simp]
lemma liftFunctorInv_obj (f : A ⟶ X ⊗ Y) :
    (liftFunctorInv A X Y).obj f = (f ≫ fst X Y, (f ≫ snd X Y)) :=
  rfl

/-- The induced canonical functor `((A ⟶ X) × (A ⟶ Y)) ⥤ (A ⟶ X ⊗ Y)` for a cartesian monoidal
strict bicategory. However, the action on objects is not definitional to the expected one, so we
later define `liftFunctor`, with the correct computation on objects.  -/
noncomputable def liftFunctor' : ((A ⟶ X) × (A ⟶ Y)) ⥤ (A ⟶ X ⊗ Y) :=
  (inv (prodComparison ((homFunctor C).obj (op A)) X Y)).toFunctor

@[simp]
lemma liftFunctor'_obj {A X Y : C} (p : (A ⟶ X) × (A ⟶ Y)) :
    (liftFunctor' A X Y).obj p = lift p.1 p.2 := by
  set F := (homFunctor C).obj (op A)
  apply hom_ext
  · rw [lift_fst]
    exact congr(($(inv_prodComparison_map_fst F X Y)).toFunctor.obj p)
  · rw [lift_snd]
    exact congr(($(inv_prodComparison_map_snd F X Y)).toFunctor.obj p)

/-- The induced canonical functor `liftFunctor : ((A ⟶ X) × (A ⟶ Y)) ⥤ (A ⟶ X ⊗ Y)` for a cartesian
monoidal strict bicategory, satisfying `(liftFunctor A X Y).obj p = lift p.1 p.2` definitionally. -/
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

/-- The canonical isomorphism of categories `((A ⟶ X) × (A ⟶ Y)) ≅ (A ⟶ X ⊗ Y)` for a cartesian
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
lemma hom₂_ext {A X Y : C} {f g : A ⟶ X ⊗ Y} {η η' : f ⟶ g}
    (hfst : η ▷ fst X Y = η' ▷ fst X Y) (hsnd : η ▷ snd X Y = η' ▷ snd X Y) : η = η' :=
  (liftIso A X Y).symm.functor.map_injective (Prod.ext hfst hsnd)

set_option backward.isDefEq.respectTransparency false in
lemma liftFunctor_map_whiskerRight_fst {A X Y : C} {p q : (A ⟶ X) × (A ⟶ Y)} (η : p ⟶ q) :
    (liftFunctor A X Y).map η ▷ fst X Y = eqToHom (by simp) ≫ η.1 ≫ eqToHom (by simp) := by
  simpa [liftFunctor_map, homFunctor, Functor.toCatHom] using
    congr(($(Functor.congr_hom (liftIso A X Y).unitIso.symm η)).1)

set_option backward.isDefEq.respectTransparency false in
lemma liftFunctor_map_whiskerRight_snd {A X Y : C} {p q : (A ⟶ X) × (A ⟶ Y)} (η : p ⟶ q) :
    (liftFunctor A X Y).map η ▷ snd X Y = eqToHom (by simp) ≫ η.2 ≫ eqToHom (by simp) := by
  simpa [liftFunctor_map, homFunctor, Functor.toCatHom] using
    congr(($(Functor.congr_hom (liftIso A X Y).unitIso.symm η)).2)

section WhiskerLaws

variable (A : C) {X Y Z : C}

/-- The hom functor `(X ⟶ Y) ⥤ (A ⊗ X ⟶ A ⊗ Y)` of the strict pseudofunctor that tensors with
`A` on the left. -/
@[simps]
noncomputable def tensorLeftHomFunctor (X Y : C) : (X ⟶ Y) ⥤ (A ⊗ X ⟶ A ⊗ Y) where
  obj f := A ◁ f
  map η := eqToHom (by simp) ≫ (liftFunctor (A ⊗ X) A Y).map
        (Prod.mkHom (𝟙 (fst A X)) (snd A X ◁ η)) ≫ eqToHom (by simp)
  map_id f := by simp [← prod_id]
  map_comp f g := by
    have h : Prod.mkHom (𝟙 (fst A X)) (snd A X ◁ f ≫ snd A X ◁ g) =
        Prod.mkHom (𝟙 (fst A X)) (snd A X ◁ f) ≫ Prod.mkHom (𝟙 (fst A X)) (snd A X ◁ g) := by
      simp
    simp only [whiskerLeft_comp, h, Functor.map_comp, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
lemma tensorLeftHomFunctor_map_whiskerRight_fst {f g : X ⟶ Y} (η : f ⟶ g) :
    (tensorLeftHomFunctor A X Y).map η ▷ fst A Y = eqToHom (by simp) := by
  simp [liftFunctor_map_whiskerRight_fst]

set_option backward.isDefEq.respectTransparency false in
lemma tensorLeftHomFunctor_map_whiskerRight_snd {f g : X ⟶ Y} (η : f ⟶ g) :
    (tensorLeftHomFunctor A X Y).map η ▷ snd A Y =
      eqToHom (by simp) ≫ snd A X ◁ η ≫ eqToHom (by simp) := by
  simp [liftFunctor_map_whiskerRight_snd]

set_option backward.isDefEq.respectTransparency false in
lemma tensorLeftHomFunctor_map_whiskerLeft (f : X ⟶ Y) {g g' : Y ⟶ Z} (η : g ⟶ g') :
    (tensorLeftHomFunctor A X Z).map (f ◁ η) =
      eqToHom (by simp) ≫ (A ◁ f) ◁ (tensorLeftHomFunctor A Y Z).map η ≫ eqToHom (by simp) := by
  ext
  · simp [tensorLeftHomFunctor_map_whiskerRight_fst, Strict.associator_eqToIso,
      -tensorLeftHomFunctor_map]
  · simp [tensorLeftHomFunctor_map_whiskerRight_snd, Strict.associator_eqToIso,
      whiskerLeft_whiskerLeft_strict, congr_whiskerLeft (whiskerLeft_snd A f) η,
      -tensorLeftHomFunctor_map, -comp_whiskerLeft]

lemma tensorLeftHomFunctor_map_whiskerRight {f f' : X ⟶ Y} (η : f ⟶ f') (g : Y ⟶ Z) :
    (tensorLeftHomFunctor A X Z).map (η ▷ g) =
      eqToHom (by simp) ≫ (tensorLeftHomFunctor A X Y).map η ▷ (A ◁ g) ≫ eqToHom (by simp) := by
  ext
  · simp [tensorLeftHomFunctor_map_whiskerRight_fst, whiskerRight_whiskerRight_strict,
      whiskerRight_congr (whiskerLeft_fst A g),
      -tensorLeftHomFunctor_map, -whisker_assoc]
  · simp [tensorLeftHomFunctor_map_whiskerRight_snd, whiskerRight_whiskerRight_strict,
      whiskerRight_congr (whiskerLeft_snd A g), Strict.associator_eqToIso,
      -tensorLeftHomFunctor_map]

end WhiskerLaws

/-- The strict pseudofunctor `C ⥤ C` that tensors on the left with a given 0-cell. -/
noncomputable def tensorLeft (A : C) : StrictPseudofunctor C C := .mk'' {
    toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun X => A ⊗ X) (tensorLeftHomFunctor A)
    map_id _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
    map_comp _ _ := by simp [PrelaxFunctor.mkOfHomFunctors, PrelaxFunctorStruct.mkOfHomPrefunctors]
    map₂_whisker_left := tensorLeftHomFunctor_map_whiskerLeft A
    map₂_whisker_right := tensorLeftHomFunctor_map_whiskerRight A
  }

-- TODO: When porting upstream, this section should be generalized to semicartesian
-- monoidal 1-categories
section Const

variable [MonoidalClosed C]

/-- The "constant" morphism `Δ : 𝟭 C ⟶ ihom J`, whose component at `X` is the currying of the
projection `J ⊗ X ⟶ X`. -/
def const (J : C) : 𝟭 C ⟶ ihom J where
  app X := curry <| snd J X
  naturality X Y f := by simp [← curry_natural_left, ← curry_natural_right]

variable {J : C}

-- Helpful as the `𝟭 C` functor isn't totally transparent. We make this a simp lemma following
-- coev_naturality
@[simp]
lemma const_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (const J).app Y = (const J).app X ≫ (ihom J).map f :=
  (const J).naturality f

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
