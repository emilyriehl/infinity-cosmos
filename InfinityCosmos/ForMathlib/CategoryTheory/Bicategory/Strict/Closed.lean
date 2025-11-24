import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Closed.Monoidal

universe v v' u u'

namespace CategoryTheory.Bicategory

universe w

variable (C : Type u) [Bicategory.{w,v} C] [Bicategory.Strict C]

/-- The morphism `(X ⟶ Y) ⥤ (X ⟶ Y')` induced by a morphism `Y ⟶ Y'`. -/
@[simps] def HomWhiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') : (X ⟶ Y) ⥤ (X ⟶ Y') where
  obj f := f ≫ g
  map φ := φ ▷ g

@[simps] def HomWhiskerRight {X X' : C} (Y : C) (f : X ⟶ X') : (X' ⟶ Y) ⥤ (X ⟶ Y) where
  obj g := f ≫ g
  map φ := f ◁ φ

def HomFunctor : Cᵒᵖ ⥤ C ⥤ Cat where
  obj X :=
    { obj := fun Y => Cat.of (X.unop ⟶ Y)
      map := fun φ => HomWhiskerLeft C X.unop φ
      map_id f := by fapply Functor.ext <;> simp [Strict.rightUnitor_eqToIso]
      map_comp f g := by fapply Functor.ext <;> simp [Strict.associator_eqToIso] }
  map φ :=
    { app := fun Y => HomWhiskerRight C Y φ.unop
      naturality X Y f := by simp; fapply Functor.ext <;> simp [Strict.associator_eqToIso] }
  map_id φ := by ext Z; fapply Functor.ext <;> simp [Strict.leftUnitor_eqToIso]
  map_comp φ ψ := by ext Z; fapply Functor.ext <;> simp [Strict.associator_eqToIso]

class Strict.CartesianMonoidal extends CartesianMonoidalCategory C where
  isMonoidal (Z : C) : ((HomFunctor C).obj (Opposite.op Z) : C ⥤ Cat).Monoidal

class Strict.CartesianClosed extends Strict.CartesianMonoidal C, MonoidalClosed C

end CategoryTheory.Bicategory
