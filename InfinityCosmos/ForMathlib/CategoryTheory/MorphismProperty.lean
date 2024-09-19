import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.LiftingProperties.Basic

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- left lifting property with respect to a class of morphisms -/
def llp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty f g

/-- rlp wrt a class of morphisms -/
def rlp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty g f

end CategoryTheory.MorphismProperty
