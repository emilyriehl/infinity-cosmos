module

/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

@[expose] public section

/-!
# Currying out of the tensor unit

`MonoidalClosed.unitIsoSelf` identifies the internal hom out of the tensor unit `𝟙_ C` with the
object itself. This file records how that identification interacts with currying: a map
`𝟙_ C ⊗ A ⟶ B` is recovered from its curried form by precomposing with the left unitor.

Only `Closed (𝟙_ C)` is needed, the same hypothesis that `MonoidalClosed.unitIsoSelf` requires.
-/

universe v u

namespace CategoryTheory.MonoidalClosed

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Closed (𝟙_ C)]

/-- `MonoidalClosed.unitIsoSelf` is evaluation at the tensor unit, up to the left unitor. -/
lemma unitIsoSelf_hom (B : C) :
    (unitIsoSelf (C := C) (X := B)).hom =
      (λ_ ((ihom (𝟙_ C)).obj B)).inv ≫ (ihom.ev (𝟙_ C)).app B := by
  change (conjugateEquiv (ihom.adjunction (𝟙_ C)) (Adjunction.id (C := C))
    (leftUnitorNatIso C).inv).app B = _
  rw [conjugateEquiv_adjunction_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating a curried map out of the tensor unit agrees with precomposition by the left
unitor. -/
lemma curry_unitIsoSelf_hom {A B : C} (H : 𝟙_ C ⊗ A ⟶ B) :
    curry H ≫ (unitIsoSelf (C := C) (X := B)).hom = (λ_ A).inv ≫ H := by
  rw [unitIsoSelf_hom, leftUnitor_inv_naturality_assoc, whiskerLeft_curry_ihom_ev_app]

end CategoryTheory.MonoidalClosed
