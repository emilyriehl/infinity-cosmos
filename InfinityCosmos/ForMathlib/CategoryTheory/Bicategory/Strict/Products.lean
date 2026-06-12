import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
The product of two strict bicategories is strict.
-/

namespace CategoryTheory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Prod

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

@[simp]
theorem eqToHom_fst {X Y : C × D} (h : X = Y) :
    (eqToHom h).1 = eqToHom (h ▸ rfl) := by subst h; rfl

@[simp]
theorem eqToHom_snd {X Y : C × D} (h : X = Y) :
    (eqToHom h).2 = eqToHom (h ▸ rfl) := by subst h; rfl

end Prod

namespace Bicategory.Prod

/-- The cartesian product of two strict bicategories is strict. -/
instance (B : Type u₁) [Bicategory.{w₁, v₁} B] [Strict B]
    (C : Type u₂) [Bicategory.{w₂, v₂} C] [Strict C] :
    Strict (B × C) where
  leftUnitor_eqToIso f := by
    apply Iso.ext
    apply CategoryTheory.Prod.hom_ext
    · simpa using congrArg Iso.hom (Strict.leftUnitor_eqToIso f.1)
    · simpa using congrArg Iso.hom (Strict.leftUnitor_eqToIso f.2)
  rightUnitor_eqToIso f := by
    apply Iso.ext
    apply CategoryTheory.Prod.hom_ext
    · simpa using congrArg Iso.hom (Strict.rightUnitor_eqToIso f.1)
    · simpa using congrArg Iso.hom (Strict.rightUnitor_eqToIso f.2)
  associator_eqToIso f g h := by
    apply Iso.ext
    apply CategoryTheory.Prod.hom_ext
    · simpa using congrArg Iso.hom (Strict.associator_eqToIso f.1 g.1 h.1)
    · simpa using congrArg Iso.hom (Strict.associator_eqToIso f.2 g.2 h.2)

end Bicategory.Prod

end CategoryTheory
