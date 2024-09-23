/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.CategoryTheory.CodiscreteCat
import InfinityCosmos.Mathlib.AlgebraicTopology.Nerve
import InfinityCosmos.Mathlib.AlgebraicTopology.SimplicialCategory.Basic

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

/-- The free isomorphism is the codiscrete category on two objects. Can we make this a special
case of the other definition?-/
instance : Category (WalkingIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u'} [Category.{v'} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category.-/
def toIso  (F : WalkingIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map PUnit.unit
  inv := F.map PUnit.unit
  hom_inv_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl
  inv_hom_id := by
    rw [← F.map_comp, ← F.map_id]
    exact rfl

/-- From an isomorphism in a category, one can build a functor out of `WalkingIso` to
that category.-/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso ⥤ C where
  obj := fun
    | zero => X
    | one => Y
  map := @fun
    | zero, zero, _ => 𝟙 _
    | zero, one,  _ => e.hom
    | one,  zero, _ => e.inv
    | one,  one,  _ => 𝟙 _


def equiv : (WalkingIso ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ => rfl
  left_inv F := by
    simp [toIso, fromIso]
    fapply Functor.hext
    · intro i; cases i <;> rfl
    · intro i j
      simp [toIso, fromIso]
      cases i <;> cases j <;> intro ⟨⟩ <;> simp only [heq_eq_eq] <;> rw [← F.map_id] <;> rfl

end

def coev (i : WalkingIso) : Fin 1 ⥤ WalkingIso := ComposableArrows.mk₀ i

end WalkingIso

end CategoryTheory

namespace SSet

def coherentIso : SSet.{u} := nerve WalkingIso

open Simplicial SimplicialCategory

def coherentIso.pt (i : WalkingIso) : Δ[0] ⟶ coherentIso :=
  (yonedaEquiv coherentIso [0]).symm (WalkingIso.coev i)

open MonoidalCategory in
def pointIsUnit : Δ[0] ≅ (𝟙_ SSet) := by sorry

open MonoidalCategory in
noncomputable def expUnitNatIso : ihom (𝟙_ SSet) ≅ 𝟭 SSet :=
  (conjugateIsoEquiv (Adjunction.id (C := SSet)) (ihom.adjunction _)
    (leftUnitorNatIso _)).symm

def expPointNatIso : ihom Δ[0] ≅ 𝟭 SSet := by sorry
--   refine ?_ ≪≫ expUnitNatIso
--   have := pointIsUnit.symm.op
--   sorry

def expPointIsoSelf (X : SSet) : sHom Δ[0] X ≅ X := sorry -- expPointNatIso.app X

noncomputable def coherentIso.ev (X : SSet) (i : WalkingIso) : sHom coherentIso X ⟶ X :=
  (MonoidalClosed.pre (coherentIso.pt i)).app X ≫ (expPointIsoSelf X).hom

/-- This is in the wrong file.
We should add a hypothesis that `A` and `B` are quasi-categories and perhaps move into a
quasi-category namespace?-/
structure SHomotopy {A B : SSet.{u}} (f g : A ⟶ B) : Type u where
  homotopy : A ⟶ sHom coherentIso B
  source_eq : homotopy ≫ coherentIso.ev B WalkingIso.zero = f
  target_eq : homotopy ≫ coherentIso.ev B WalkingIso.one = g

structure Equiv (A B : SSet.{u}) : Type u where
  toFun : A ⟶ B
  invFun : B ⟶ A
  left_inv : SHomotopy (toFun ≫ invFun) (𝟙 A)
  right_inv : SHomotopy (invFun ≫ toFun) (𝟙 B)

end SSet
