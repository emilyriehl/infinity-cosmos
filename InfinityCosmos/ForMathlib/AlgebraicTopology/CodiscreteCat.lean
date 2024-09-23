import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.ULift
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic

universe u v

namespace CategoryTheory

-- def isCodiscrete (C : Type) [Category C] :=
-- ∀ a b : C, inhabited ( inssubsingleton (a ⟶ b) )

/-- We start by introducting an alias for the type underlying a codiscrete or chaotic or contractible category
structure.-/
def Codiscrete (A : Type u) : Type u := A


namespace Codiscrete

instance (A : Type u) : Category (Codiscrete A) where
  Hom _ _ := Unit -- The hom types in the Codiscrete A are the unit type.
  id _ := ⟨⟩ -- This is the unique element of the unit type.
  comp _ _ := ⟨⟩


/-- \ func is the functor arrow; \ to is the function arrow.-/
def funToFunc {A B : Type u} (f : A → B) : Codiscrete A ⥤ Codiscrete B where
  obj a := f a
  map _ := ⟨⟩

/-- Any function `C → A` lifts to a functor `C ⥤  Codiscrete A`. For discrete categories this is
called `functor` but we use that name for something else. -/
def lift {A C: Type u}[Category C] (F : C → A) : C ⥤ Codiscrete A where
  obj := F
  map _ := ⟨⟩

def invlift {A C: Type u}[Category C] (F : C ⥤ Codiscrete A) : C → A :=
  F.obj


/-- For functors to a codiscrete category, a natural transformation is trivial
-/
def natTrans {A C : Type u} [Category C] {F G : C ⥤ Codiscrete A} (_ : ∀ c : C, F.obj c ⟶ G.obj c)
:
    F ⟶ G where
  app _ := ⟨⟩

/-- For functors into a codiscrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
def natIso {A C : Type u}[Category C] {F G : C ⥤ Codiscrete A} (_ : ∀ c : C, F.obj c ≅ G.obj c) :
    F ≅ G where
  hom := {
    app := fun _ => ⟨⟩
  }
  inv := {
    app := fun _ => ⟨⟩
  }

/-- Every functor `F` to a codiscrete category is naturally isomorphic {(actually, equal)?} to
  `Codiscrete.functor (F.obj)`. -/
def natIsoFunctor {A C : Type u}[Category C] {F : C ⥤ Codiscrete A} : F ≅ lift (F.obj) where
  hom := {
    app := fun _ => ⟨⟩
  }
  inv := {
    app := fun _ => ⟨⟩
  }

open Opposite

/-- A codiscrete category is equivalent to its opposite category. -/
protected def opposite (A : Type u) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A :=
 let F : (Codiscrete A)ᵒᵖ ⥤ Codiscrete A := lift fun (op (x)) => x
 {
  functor := F
  inverse := F.rightOp
  unitIso := NatIso.ofComponents fun ⟨x⟩ =>
   Iso.refl _
  counitIso := natIso fun c => Iso.refl c
 }

def Cod : Type u ⥤ Cat.{0,u} where
  obj A := Cat.of (Codiscrete A)
  map := funToFunc

open Adjunction

/-For a category C and Y : type u, this is the equivalence between the hom objects C → Y
and hom  C ⥤ Codiscrete Y -/
def homEquiv' (C : Cat) (Y : Type u) : (Cat.objects.obj C ⟶ Y) ≃ (C ⟶ Cod.obj Y) where
  toFun := lift
  invFun := invlift
  left_inv _ := rfl
  right_inv _ := rfl

/-Adjunction between the Objects functor (left adjoint) and the codiscrete functor (right adjoint)
using the hom set adjunction definition  -/
def adj : Cat.objects ⊣ Cod := by
  apply mkOfHomEquiv
  exact {
    homEquiv := homEquiv'
    homEquiv_naturality_left_symm := by
      intro _ _ _ _ _
      rfl
    homEquiv_naturality_right := by
      intro _ _ _ _ _
      rfl
  }

/-Adjunction between the Objects functor (left adjoint) and the codiscrete functor (right adjoint)
using the unit/counit definition  -/
def adj' : Cat.objects ⊣ Cod where
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
