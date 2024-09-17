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
inductive WalkingIso : Type u where
  | zero : WalkingIso
  | one : WalkingIso

open WalkingIso

namespace WalkingIso

/-- The arrows in the walking iso category split into three cases.-/
inductive Hom : WalkingIso → WalkingIso → Type v where
  | id : (X : WalkingIso) → Hom X X
  | hom : Hom zero one
  | inv : Hom one zero

/-- The quiver structure on `WalkingIso`-/
instance : Quiver WalkingIso where
  Hom := Hom

/-- The quiver `WalkingIso` has at most one arrow in each hom.-/
instance : Quiver.IsThin WalkingIso := fun _ _ => by
  constructor
  intro f g
  casesm* WalkingIso, (_ : WalkingIso) ⟶ (_ : WalkingIso)
  · rfl
  · rfl
  · rfl
  · rfl

/-- The category structure on `WalkingIso` defined by case analysis.-/
instance : CategoryStruct WalkingIso where
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

/-- As a thin quiver with a category structure, `WalkingIso` is a category.-/
instance : Category WalkingIso := thin_category

section

variable {C : Type u'} [Category.{v'} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category.-/
def toIso  (F : WalkingIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map Hom.hom
  inv := F.map Hom.inv
  hom_inv_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl
  inv_hom_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl

/-- From an isomorphism in a category, one can build a functor out of `WalkingIso` to
that category.-/
def fromIso (X Y : C) : (X ≅ Y) → (WalkingIso ⥤ C) := fun f => {
  obj := by
    intro E
    match E with
    | WalkingIso.zero => exact X
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

/-- Now we redefine `WalkingIso` as `FreeIso` to experiment with a different definition. We start by
introducting an alias for the type underlying a codiscrete or chaotic or contractible category
structure.-/
def Contractible (A : Type u) : Type u := A
namespace Contractible

instance (A : Type u) : Category (Contractible A) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

end Contractible

inductive FreeIso : Type u where
  | zero : FreeIso
  | one : FreeIso

open FreeIso

namespace FreeIso

/-- The free isomorphism is the contractible category on two objects.-/
instance : Category (FreeIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u'} [Category.{v'} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category.-/
def toIso  (F : FreeIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map PUnit.unit
  inv := F.map PUnit.unit
  hom_inv_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl
  inv_hom_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl

/-- From an isomorphism in a category, one can build a functor out of `FreeIso` to
that category.-/
def fromIso {X Y : C} (e : X ≅ Y) : FreeIso ⥤ C where
  obj := fun
    | zero => X
    | one => Y
  map := @fun
    | zero, zero, _ => 𝟙 _
    | zero, one,  _ => e.hom
    | one,  zero, _ => e.inv
    | one,  one,  _ => 𝟙 _
end

end FreeIso


end CategoryTheory

namespace SSet

/-- This is the homotopy coherent isomorphism, defined to be the nerve of `WalkingIso`.-/
def coherentIso : SSet := nerve WalkingIso

end SSet
