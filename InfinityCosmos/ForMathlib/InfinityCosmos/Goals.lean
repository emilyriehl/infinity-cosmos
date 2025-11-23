/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

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

def Adjunction : Type := CategoryTheory.Bicategory.Adjunction (B := QCat) f u


end QCat

end SSet
