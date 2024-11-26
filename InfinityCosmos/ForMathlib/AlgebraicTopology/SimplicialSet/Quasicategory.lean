/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic

namespace SSet

open CategoryTheory Simplicial

section categoryofqcats

/-
QCat is the category of quasi-categories defined as the full
subcategory of the category of simplicial sets SSet.
-/
def QCat := FullSubcategory Quasicategory
instance : Category QCat := FullSubcategory.category Quasicategory

end categoryofqcats

end SSet
