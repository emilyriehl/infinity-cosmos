import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-
Isomorphisms between categories.
-/

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

/-- An isomorphism of categories. -/
structure IsoCat where mk' ::
  /-- The forwards direction of an equivalence. -/
  functor : C ⥤ D
  /-- The backwards direction of an equivalence. -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is equal to the identity. -/
  unitIso : 𝟭 C = functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is equal to the identity. -/
  counitIso : inverse ⋙ functor = 𝟭 D

/-- The inverse isomorphism of categories, obtained by swapping `functor` and `inverse`. -/
@[symm]
def IsoCat.symm {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (e : IsoCat C D) : IsoCat D C where
  functor := e.inverse
  inverse := e.functor
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm

/-- Composition of isomorphisms of categories. -/
@[trans]
def IsoCat.trans {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (e : IsoCat C D) (f : IsoCat D E) : IsoCat C E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := by
    rw [Functor.assoc, ← Functor.assoc f.functor, ← f.unitIso, Functor.id_comp]
    exact e.unitIso
  counitIso := by
    rw [Functor.assoc, ← Functor.assoc e.inverse, e.counitIso, Functor.id_comp]
    exact f.counitIso

variable {C} {D} in
class Functor.IsIsomorphism (F : C ⥤ D) : Prop where
  faithful : F.Faithful := by infer_instance
  full : F.Full := by infer_instance
  bijectiveOnObjects : F.obj.Bijective := by infer_instance

variable {C} {D} (F : C ⥤ D) [h : F.IsIsomorphism]

instance : F.Full := h.full
instance : F.Faithful := h.faithful

noncomputable def Functor.objEquiv : C ≃ D := .ofBijective _ h.bijectiveOnObjects

noncomputable def strictInv : D ⥤ C where
  obj := F.objEquiv.invFun
  map {X Y} f :=
    F.preimage (eqToHom (F.objEquiv.apply_symm_apply X) ≫ f ≫
      eqToHom (F.objEquiv.apply_symm_apply Y).symm)
  map_id X := by simp
  map_comp {X Y Z} f g := by simp [← Functor.preimage_comp]

set_option backward.defeqAttrib.useBackward true in
/-- A functor that is an isomorphism of categories assembles into an `IsoCat`,
with `strictInv` as its inverse. -/
noncomputable def Functor.asIsomorphism : IsoCat C D where
  functor := F
  inverse := strictInv F
  unitIso := by
    refine Functor.ext
      (fun X => ((Equiv.ofBijective _ h.bijectiveOnObjects).symm_apply_apply X).symm) ?_
    intro X Y f
    apply F.map_injective
    simp [strictInv, eqToHom_map]
  counitIso := by
    refine Functor.ext
      (fun X => (Equiv.ofBijective _ h.bijectiveOnObjects).apply_symm_apply X) ?_
    intro X Y f
    simp [strictInv]

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence of categories underlying an `IsoCat`, with the unit and counit
isomorphisms induced by the defining equalities. -/
def IsoCat.toEquivalence (e : IsoCat C D) : C ≌ D where
  functor := e.functor
  inverse := e.inverse
  unitIso := eqToIso e.unitIso
  counitIso := eqToIso e.counitIso
  functor_unitIso_comp X := by simp [eqToHom_map]

@[simps]
def Equivalence.toIsoCat (e : C ≌ D)
    (h : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h' : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (k : ∀ (X : C), e.unitIso.hom.app X = eqToHom (h X).symm := by cat_disch)
    (k' : ∀ (Y : D), e.counitIso.hom.app Y = eqToHom (h' Y) := by cat_disch) : IsoCat C D where
  functor := e.functor
  inverse := e.inverse
  unitIso := Functor.ext_of_iso e.unitIso (by simp [h])
  counitIso := Functor.ext_of_iso e.counitIso (by simp [h'])

instance IsoCat.isIsomorphismFunctor (e : IsoCat C D) : e.functor.IsIsomorphism where
  faithful := e.toEquivalence.faithful_functor
  full := e.toEquivalence.full_functor
  bijectiveOnObjects := Function.bijective_iff_has_inverse.mpr
    ⟨e.inverse.obj, fun X => (Functor.congr_obj e.unitIso X).symm,
      Functor.congr_obj e.counitIso⟩
