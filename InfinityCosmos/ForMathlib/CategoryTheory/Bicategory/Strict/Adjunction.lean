import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Pseudofunctors preserve adjunctions

We show that a pseudofunctor `F : Pseudofunctor B C` carries an adjunction `f ⊣ g` between
1-morphisms of `B` to an adjunction `F.map f ⊣ F.map g` in `C`, see
`Pseudofunctor.mapAdjunction`.

For a strict pseudofunctor between strict bicategories, presented by the data of a
`StrictPseudofunctorPreCore`, we provide the corresponding specialization
`StrictPseudofunctorPreCore.mapAdjunction`.
-/

namespace CategoryTheory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

namespace Pseudofunctor

variable (F : Pseudofunctor B C)

section MapAdjunction

variable {a b : B} {f : a ⟶ b} {g : b ⟶ a}

/-- The image of an adjunction unit under a pseudofunctor. -/
def mapAdjunctionUnit (adj : f ⊣ g) : 𝟙 (F.obj a) ⟶ F.map f ≫ F.map g :=
  (F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom

/-- The image of an adjunction counit under a pseudofunctor. -/
def mapAdjunctionCounit (adj : f ⊣ g) : F.map g ≫ F.map f ⟶ 𝟙 (F.obj b) :=
  (F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom

/-- `map₂_associator`, solved for the middle composite. -/
lemma map₂_associator' {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f g).hom ▷ F.map h ≫ (α_ (F.map f) (F.map g) (F.map h)).hom ≫
      F.map f ◁ (F.mapComp g h).inv =
    (F.mapComp (f ≫ g) h).inv ≫ F.map₂ (α_ f g h).hom ≫ (F.mapComp f (g ≫ h)).hom := by
  rw [F.map₂_associator]
  simp

/-- The inverse form of `map₂_associator'`. -/
lemma map₂_associator_inv' {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map f ◁ (F.mapComp g h).hom ≫ (α_ (F.map f) (F.map g) (F.map h)).inv ≫
      (F.mapComp f g).inv ▷ F.map h =
    (F.mapComp f (g ≫ h)).inv ≫ F.map₂ (α_ f g h).inv ≫ (F.mapComp (f ≫ g) h).hom := by
  rw [← IsIso.inv_eq_inv]
  simp only [IsIso.inv_comp, IsIso.Iso.inv_hom, IsIso.Iso.inv_inv, inv_whiskerLeft,
    inv_whiskerRight, ← PrelaxFunctor.map₂_inv, Category.assoc]
  exact F.map₂_associator' f g h

/-- The image of `map₂_left_unitor` for the inverse of the left unitor. -/
lemma map₂_left_unitor_inv {a b : B} (f : a ⟶ b) :
    F.map₂ (λ_ f).inv =
      (λ_ (F.map f)).inv ≫ (F.mapId a).inv ▷ F.map f ≫ (F.mapComp (𝟙 a) f).inv := by
  rw [← cancel_epi (F.map₂ (λ_ f).hom), ← F.map₂_comp, Iso.hom_inv_id, F.map₂_id,
    F.map₂_left_unitor]
  simp

/-- The image of `map₂_right_unitor` for the inverse of the right unitor. -/
lemma map₂_right_unitor_inv {a b : B} (f : a ⟶ b) :
    F.map₂ (ρ_ f).inv =
      (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv ≫ (F.mapComp f (𝟙 b)).inv := by
  rw [← cancel_epi (F.map₂ (ρ_ f).hom), ← F.map₂_comp, Iso.hom_inv_id, F.map₂_id,
    F.map₂_right_unitor]
  simp

/-- The left zigzag of the conjugated images of a pair of 2-morphisms is the conjugated image
of their left zigzag. -/
lemma leftZigzag_map (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    leftZigzag ((F.mapId a).inv ≫ F.map₂ η ≫ (F.mapComp f g).hom)
        ((F.mapComp g f).inv ≫ F.map₂ ε ≫ (F.mapId b).hom) =
      (F.mapId a).inv ▷ F.map f ⊗≫ (F.mapComp (𝟙 a) f).inv ≫
        F.map₂ (leftZigzag η ε) ≫ (F.mapComp f (𝟙 b)).hom ⊗≫ F.map f ◁ (F.mapId b).hom := by
  simp [leftZigzag, bicategoricalComp]

/-- The right zigzag of the conjugated images of a pair of 2-morphisms is the conjugated image
of their right zigzag. -/
lemma rightZigzag_map (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    rightZigzag ((F.mapId a).inv ≫ F.map₂ η ≫ (F.mapComp f g).hom)
        ((F.mapComp g f).inv ≫ F.map₂ ε ≫ (F.mapId b).hom) =
      F.map g ◁ (F.mapId a).inv ⊗≫ (F.mapComp g (𝟙 a)).inv ≫
        F.map₂ (rightZigzag η ε) ≫ (F.mapComp (𝟙 b) g).hom ⊗≫ (F.mapId b).hom ▷ F.map g := by
  simp [rightZigzag, bicategoricalComp, reassoc_of% F.map₂_associator_inv' g f g]

/-- A pseudofunctor carries an adjunction `f ⊣ g` to an adjunction `F.map f ⊣ F.map g`. -/
@[simps]
def mapAdjunction (adj : f ⊣ g) : F.map f ⊣ F.map g where
  unit := F.mapAdjunctionUnit adj
  counit := F.mapAdjunctionCounit adj
  left_triangle := by
    rw [mapAdjunctionUnit, mapAdjunctionCounit, F.leftZigzag_map adj.unit adj.counit,
      adj.left_triangle, F.map₂_comp, F.map₂_right_unitor_inv]
    simp [bicategoricalComp]
  right_triangle := by
    rw [mapAdjunctionUnit, mapAdjunctionCounit, F.rightZigzag_map adj.unit adj.counit,
      adj.right_triangle, F.map₂_comp, F.map₂_left_unitor_inv]
    simp [bicategoricalComp]

end MapAdjunction

end Pseudofunctor

namespace StrictPseudofunctorPreCore

variable [Bicategory.Strict B] [Bicategory.Strict C]
  (S : StrictPseudofunctorPreCore B C) {a b : B} {f : a ⟶ b} {g : b ⟶ a}

/-- A strict pseudofunctor between strict bicategories, presented by the data of a
`StrictPseudofunctorPreCore`, carries an adjunction `f ⊣ g` to an adjunction
`S.map f ⊣ S.map g`. -/
def mapAdjunction (adj : f ⊣ g) : S.map f ⊣ S.map g :=
  (StrictPseudofunctor.mk'' S).toPseudofunctor.mapAdjunction adj

lemma mapAdjunction_unit (adj : f ⊣ g) :
    (S.mapAdjunction adj).unit =
      eqToHom (S.map_id a).symm ≫ S.map₂ adj.unit ≫ eqToHom (S.map_comp f g) := by
  simp [mapAdjunction, Pseudofunctor.mapAdjunctionUnit, StrictPseudofunctor.mk'']

lemma mapAdjunction_counit (adj : f ⊣ g) :
    (S.mapAdjunction adj).counit =
      eqToHom (S.map_comp g f).symm ≫ S.map₂ adj.counit ≫ eqToHom (S.map_id b) := by
  simp [mapAdjunction, Pseudofunctor.mapAdjunctionCounit, StrictPseudofunctor.mk'']

end StrictPseudofunctorPreCore

end CategoryTheory
