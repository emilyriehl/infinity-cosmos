/-
Copyright (c) 2024 Alvaro Belmonte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvaro Belmonte
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.ULift
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic

universe u v

namespace CategoryTheory

/-- We start by introducting an alias for the type underlying a codiscrete category
structure.-/
def Codiscrete (A : Type u) : Type u := A

namespace Codiscrete

instance (A : Type*) : Category (Codiscrete A) where
  Hom _ _ := Unit -- The hom types in the Codiscrete A are the unit type.
  id _ := ⟨⟩ -- This is the unique element of the unit type.
  comp _ _ := ⟨⟩

/-- A function induces a functor between codiscrete categories.-/
def funToFunc {A B : Type*} (f : A → B) : Codiscrete A ⥤ Codiscrete B where
  obj a := f a
  map _ := ⟨⟩

/-- Any function `C → A` lifts to a functor `C ⥤  Codiscrete A`. For discrete categories this is
called `functor` but we use that name for something else. -/
def lift {A C : Type*}[Category C] (F : C → A) : C ⥤ Codiscrete A where
  obj := F
  map _ := ⟨⟩

/-- Any functor `C ⥤  Codiscrete A` has an underlying function.-/
def invlift {A C : Type*}[Category C] (F : C ⥤ Codiscrete A) : C → A := F.obj

/-- For functors to a codiscrete category, a natural transformation is trivial.-/
def natTrans {A C : Type*} [Category C] {F G : C ⥤ Codiscrete A} (_ : ∀ c : C, F.obj c ⟶ G.obj c) :
    F ⟶ G where
  app _ := ⟨⟩

/-- For functors into a codiscrete category, a natural isomorphism is just a collection of
isomorphisms, as the naturality squares are trivial.-/
def natIso {A C : Type*}[Category C] {F G : C ⥤ Codiscrete A} (_ : ∀ c : C, F.obj c ≅ G.obj c) :
    F ≅ G where
  hom := {
    app := fun _ => ⟨⟩
  }
  inv := {
    app := fun _ => ⟨⟩
  }

/-- Every functor `F` to a codiscrete category is naturally isomorphic {(actually, equal)?} to
  `Codiscrete.functor (F.obj)`. -/
def natIsoFunctor {A C : Type*}[Category C] {F : C ⥤ Codiscrete A} : F ≅ lift (F.obj) where
  hom := {
    app := fun _ => ⟨⟩
  }
  inv := {
    app := fun _ => ⟨⟩
  }

open Opposite

/-- A codiscrete category is equivalent to its opposite category. -/
protected def opposite (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A :=
 let F : (Codiscrete A)ᵒᵖ ⥤ Codiscrete A := lift fun (op (x)) => x
 {
  functor := F
  inverse := F.rightOp
  unitIso := NatIso.ofComponents fun ⟨x⟩ =>
   Iso.refl _
  counitIso := natIso fun c => Iso.refl c
 }

def functor : Type u ⥤ Cat.{0,u} where
  obj A := Cat.of (Codiscrete A)
  map := funToFunc

open Adjunction Cat

/-- For a category `C` and type `A`, there is an equivalence between functions `objects.obj C ⟶ A`
and functors `C ⥤ Codiscrete A`.-/
def homEquiv' (C : Cat) (A : Type*) : (objects.obj C ⟶ A) ≃ (C ⟶ functor.obj A) where
  toFun := lift
  invFun := invlift
  left_inv _ := rfl
  right_inv _ := rfl

/-- The functor that turns a type into a codiscrete category is right adjoint to the objects
functor.-/
def adj : objects ⊣ functor := mkOfHomEquiv
  {
    homEquiv := homEquiv'
    homEquiv_naturality_left_symm := fun _ _ => Eq.refl _
    homEquiv_naturality_right := fun _ _ => Eq.refl _
  }

/-- A second proof of the same adjunction.  -/
def adj' : objects ⊣ functor where
  unit := {
    app := fun _ => {
      obj := fun _ => _
      map := fun _ => ⟨⟩
    }
  }
  counit := {
    app := fun _ => id
  }
  left_triangle_components := by
    intro _
    simp only [Functor.id_obj, Functor.comp_obj, id_eq]
    rfl
  right_triangle_components := by
    intro _
    simp only [Functor.id_obj, Functor.comp_obj, id_eq]
    rfl

end Codiscrete

end CategoryTheory
