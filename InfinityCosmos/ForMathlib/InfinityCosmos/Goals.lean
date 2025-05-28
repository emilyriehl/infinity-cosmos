/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

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

open CategoryTheory Category Functor Simplicial MonoidalCategory SSet Limits Bicategory

namespace CategoryTheory

namespace SimplicialCategory

/-- As a full subcategory, the category of quasi-categories is simplicially enriched. -/
def QCat.SimplicialCat : SimplicialCategory QCat := sorry

/-- One of the fields of a simplicial category is a simplicially enriched category. -/
def QCat.SSetEnrichedCat : EnrichedCategory SSet QCat :=
  QCat.SimplicialCat.toEnrichedCategory

end SimplicialCategory

/-- PR #25010 will prove: -/
instance hoFunctor.preservesBinaryProducts' :
    PreservesLimitsOfShape (Discrete Limits.WalkingPair) hoFunctor where
  preservesLimit := sorry

/-- A product preserving functor between cartesian closed categories is lax monoidal. -/
instance hoFunctor.laxMonoidal : LaxMonoidal hoFunctor := sorry

/-- Applying this result, the category of quasi-categories is an enriched ordinary category over the
cartesian closed category of categories. -/
def QCat.CatEnrichedCat : EnrichedCategory Cat QCat := by
--  let ans := CategoryTheory.TransportEnrichment (V := SSet) (W := Cat) hoFunctor QCat
  sorry

-- Finally we convert the Cat enriched category of categories to a 2-category. Perhaps it would be
-- better to first extend this to Cat enriched ordinary category?

/-- This is required, unfortunately, by the following definition. -/
instance QCat.Bicategory : Bicategory QCat := sorry

/-- For this statement to typecheck, we need a bicategory instance. -/
instance QCat.strictBicategory : Bicategory.Strict QCat := sorry

end CategoryTheory

-- The payoff is now we get to develop some category theory of quasi-categories.
namespace SSet

namespace Quasicategory

-- variable {A B : SSet} [Quasicategory A] [Quasicategory B] (f : B ⟶ A) (u : A ⟶ B)
-- variable {A B : QCat} (f : B ⟶ A) (u : A ⟶ B)

-- def Adjunction : Type := CategoryTheory.Bicategory.Adjunction (B := QCat) f u


end Quasicategory

end SSet
