/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.Mathlib.AlgebraicTopology.Nerve

universe u v u' v'

open CategoryTheory Nat

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects called
`zero` and `one`. Perhaps these should have different names?-/
inductive walkingIso : Type u where
  | zero : walkingIso
  | one : walkingIso

open walkingIso

namespace WalkingIso

/-- The arrows in the walking iso category split into three cases.-/
inductive Hom : walkingIso → walkingIso → Type v where
  | id : (X : walkingIso) → Hom X X
  | hom : Hom zero one
  | inv : Hom one zero

/-- The quiver structure on `walkingIso`-/
instance : Quiver walkingIso where
  Hom := Hom

/-- The quiver `walkingIso` has at most one arrow in each hom.-/
instance : Quiver.IsThin walkingIso := fun _ _ => by
  constructor
  intro f g
  casesm* walkingIso, (_ : walkingIso) ⟶ (_ : walkingIso)
  · rfl
  · rfl
  · rfl
  · rfl

/-- The category structure on `walkingIso` defined by case analysis.-/
instance : CategoryStruct walkingIso where
  Hom := Hom
  id := Hom.id
  comp := by
    intro X Y Z f g
    cases g
    · exact f
    · cases f
      · exact Hom.hom
      · exact (Hom.id _)
    · cases f
      · exact Hom.inv
      · exact (Hom.id _)

/-- As a thin quiver with a category structure, `walkingIso` is a category.-/
instance : Category walkingIso := thin_category

section

variable {C : Type u'} [Category.{v'} C]

/-- Functors out of `walkingIso` define isomorphisms in the target category.-/
def toIso  (F : walkingIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map Hom.hom
  inv := F.map Hom.inv
  hom_inv_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl
  inv_hom_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl

/-- From an isomorphism in a category, one can build a functor out of `walkingIso` to
that category.-/
def fromIso (X Y : C) : (X ≅ Y) → (walkingIso ⥤ C) := fun f => {
  obj := by
    intro E
    match E with
    | walkingIso.zero => exact X
    | one => exact Y
  map := by
    intro E F h
    match h with
    | Hom.id _ => exact 𝟙 _
    | Hom.hom => exact f.hom
    | Hom.inv => exact f.inv
  map_id := by aesop_cat
  map_comp := by
    intro E F G h k
    cases k
    · dsimp
      simp only [Category.comp_id]
      exact rfl
    · dsimp
      cases h
      · dsimp
        simp only [Category.id_comp]
        exact rfl
      · dsimp
        simp only [Iso.inv_hom_id]
        exact rfl
    · dsimp
      cases h
      · dsimp
        simp only [Category.id_comp]
        exact rfl
      · dsimp
        simp only [Iso.hom_inv_id]
        exact rfl
}

end

end WalkingIso

end CategoryTheory

namespace SSet

/-- This is the homotopy coherent isomorphism, defined to be the nerve of `walkingIso`.-/
def coherentIso : SSet := nerve walkingIso

end SSet
