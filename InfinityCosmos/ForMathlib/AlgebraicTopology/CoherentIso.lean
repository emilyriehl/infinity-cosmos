/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/
import InfinityCosmos.Mathlib.AlgebraicTopology.Nerve
import InfinityCosmos.Mathlib.AlgebraicTopology.Quasicategory

/-!
# The homotopy coherent isomorphism

The homotopy coherent isomorphism is a simplicial set that corepresents isomorphisms in a quasi-category, which are defined to be arrows that define isomorphisms in the homotopy category.

## Future work

There is a lot of work still to do.

-/

universe u v

open CategoryTheory Simplicial

namespace CategoryTheory

/-- We refer to the two objects in the type `walkingIso` as `src` and `tgt`.
-/
inductive walkingIso : Type u
  | src : walkingIso
  | tgt : walkingIso

open walkingIso

namespace WalkingIso

/-- The groupoid `walkingIso` has a unique arrow in each hom type, but we spell these out explicitly to give them better names.-/
inductive Hom : walkingIso → walkingIso → Type v
  | id : ∀ X, Hom X X
  | hom : Hom src tgt
  | inv : Hom tgt src

instance : Quiver walkingIso where
  Hom := Hom

instance walkingIso_isThin : Quiver.IsThin walkingIso := fun _ _ => by
  constructor
  intro a b
  casesm* walkingIso, (_ : walkingIso) ⟶ (_ : walkingIso)
  · rfl
  · rfl
  · rfl
  · rfl

instance struct : CategoryStruct walkingIso where
  Hom := Hom
  id := Hom.id
  comp f g := by
    cases f
    · exact g
    · cases g
      · exact Hom.hom
      · exact (Hom.id _)
    · cases g
      · exact Hom.inv
      · exact (Hom.id _)

instance : Category walkingIso := thin_category

end WalkingIso

end CategoryTheory

namespace SSet

def walkingCoherentIso : SSet.{u} := nerve walkingIso

-- structure CoherentIso {S : SSet.{u}} [Quasicategory S] (X Y : S _[0]) where
--   /-- The forward direction of an isomorphism. -/
--   hom : X ⟶ Y
--   /-- The backwards direction of an isomorphism. -/
--   inv : Y ⟶ X
--   /-- Composition of the two directions of an isomorphism is the identity on the source. -/
--   hom_inv_id : hom ≫ inv = 𝟙 X := by aesop_cat
--   /-- Composition of the two directions of an isomorphism in reverse order
--   is the identity on the target. -/
--   inv_hom_id : inv ≫ hom = 𝟙 Y := by aesop_cat

end SSet
