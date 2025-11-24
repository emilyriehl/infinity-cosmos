/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic

universe v v' u u'

/-!
# 2025 Goals of the Infinity-Cosmos Project

This file gives an overview of the medium term goals of the infinity-cosmos project, which aims to
develop some non-trivial infinity-category theory in Mathlib by the end of the year.

Two methods to develop quasicategory theory in Lean:

(i) The "analytic" approach:
- Follow Joyal or Lurie and give all the definitions directly in the language of quasicategories.
- Advantage: definitions are relatively direct and well resourced.
- Disadvantage: formalizing any theorems is very difficult.

(ii) The "axiomatic" or "formal category theory" approach:
- Build a 2-category (strict bicategory) of quasicategories, "functors", and "natural transformations."
- This can be thought of as in analogy with the 2-category of categories, functors, and natural transformations.
- Then "formal theory category" says that you can capture categorical definitions like equivalence,
adjunction, limit and colimit, pointwise Kan extension in a 2-category and surprisingly these give
the correct ∞-categorical notions (meaning these capture sufficient "higher structure").
- In particular: mathlib already has a notion of adjunction in a bicategory. Once we have the
strict bicategory of quasicategories this will give the correct notion of adjunction between quasicategories.

The ∞-cosmos project follows approach (ii).
-/


open CategoryTheory SSet

-- Work over the summer has lead to the following, in mathlib as of November 23, 2025.
-- #check QCat.strictBicategory


-- The payoff is now we get to develop some category theory of quasi-categories.
namespace SSet

namespace QCat

variable {A B : SSet} [Quasicategory A] [Quasicategory B] (f : B ⟶ A) (u : A ⟶ B)
variable {A B : QCat} (f : B ⟶ A) (u : A ⟶ B)

abbrev Adjunction : Type := CategoryTheory.Bicategory.Adjunction (B := QCat) f u


end QCat

end SSet

namespace InfinityCosmos

open CategoryTheory Simplicial

variable (K : Type u) [Category.{v} K] [InfinityCosmos.{v} K]

/-- `QCat` obtains a `Cat`-enriched ordinary category structure by applying `hoFunctor` to the
hom objects in its `SSet`-enriched ordinary structure. -/
noncomputable instance catEnrichedOrdinaryCategory : EnrichedOrdinaryCategory Cat K :=
  TransportEnrichment.enrichedOrdinaryCategory K hoFunctor
    hoFunctor.unitHomEquiv hoFunctor.unitHomEquiv_eq

section «workaround for #32063»

universe u'' v''
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V] (C : Type u) [Category.{v} C]
variable [EnrichedOrdinaryCategory V C] {C}

/-- If `D` is already an enriched ordinary category, there is a canonical functor from `D` to
`ForgetEnrichment V D`. -/
@[simps]
def ForgetEnrichment.equivInverse (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    D ⥤ ForgetEnrichment V D where
  obj X := .of V X
  map f := ForgetEnrichment.homOf V (eHomEquiv V f)
  map_comp f g := by simp [eHomEquiv_comp]

/-- If `D` is already an enriched ordinary category, there is a canonical functor from
`ForgetEnrichment V D` to `D`. -/
@[simps]
def ForgetEnrichment.equivFunctor (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ⥤ D where
  obj X := ForgetEnrichment.to V X
  map f := (eHomEquiv V).symm (ForgetEnrichment.homTo V f)
  map_id X := by rw [ForgetEnrichment.homTo_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {X} {Y} {Z} f g :=  Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V Z))
    (by simp [eHomEquiv_comp])

/-- If `D` is already an enriched ordinary category, it is equivalent to `ForgetEnrichment V D`. -/
@[simps]
def ForgetEnrichment.equiv {D : Type u''} [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ≌ D where
  functor := equivFunctor V D
  inverse := equivInverse V D
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)
  functor_unitIso_comp X := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V X)) (by simp)

end «workaround for #32063»

/-- The underlying category of the `Cat`-enriched ordinary category of quasicategories is
equivalent to `QCat`. -/
noncomputable def forgetEnrichment.equiv :
    ForgetEnrichment Cat K ≌ K :=
  ForgetEnrichment.equiv Cat (D := K)

/-- The bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
noncomputable instance bicategory : Bicategory K :=
  CatEnrichedOrdinary.instBicategory

/-- The strict bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
noncomputable instance strictBicategory : Bicategory.Strict K :=
  CatEnrichedOrdinary.instStrict

end InfinityCosmos
