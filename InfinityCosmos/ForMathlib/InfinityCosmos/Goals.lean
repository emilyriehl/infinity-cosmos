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
import Mathlib.CategoryTheory.Closed.FunctorToTypes
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

open CategoryTheory Category Functor Simplicial MonoidalCategory SSet Limits

namespace CategoryTheory

namespace SimplicialCategory

/-- As a full subcategory, the category of quasi-categories is simplicially enriched. -/
noncomputable def QCat.SimplicialCat : SimplicialCategory QCat where
 Hom X Y := X.obj.functorHom Y.obj
 id X := Functor.natTransEquiv.symm (𝟙 X.obj)
 comp X Y Z := { app := fun _ ⟨f, g⟩ => f.comp g }
 homEquiv := Functor.natTransEquiv.symm

/-- One of the fields of a simplicial category is a simplicially enriched category. -/
noncomputable instance QCat.SSetEnrichedCat : EnrichedCategory SSet QCat :=
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
noncomputable def QCat.CatEnrichedCat : EnrichedCategory Cat QCat :=
  instEnrichedCategoryTransportEnrichment (C := QCat) hoFunctor

-- Finally we convert the Cat enriched category of categories to a 2-category. Perhaps it would be
-- better to first extend this to Cat enriched ordinary category?

/-- This is required, unfortunately, by the following definition. -/
instance QCat.Bicategory : Bicategory QCat := sorry

/-- For this statement to typecheck, we need a bicategory instance. -/
instance QCat.strictBicategory : Bicategory.Strict QCat := sorry

section
variable (C : Type*) [EnrichedCategory Cat C]

-- FIXME why doesn't this work the same?
-- instance : Category C := categoryForgetEnrichment Cat
instance : CategoryStruct C where
  Hom a b := (a ⟶[Cat] b).α
  id a := (eId Cat a).obj ⟨⟨()⟩⟩
  comp {a b c} f g := (eComp Cat a b c).obj (f, g)

instance : Category C where
  id_comp {a b} (f : a ⟶[Cat] b) := congrArg (·.obj f) (e_id_comp (V := Cat) a b)
  comp_id {a b} f := congrArg (·.obj f) (e_comp_id (V := Cat) a b)
  assoc {a b c d} f g h := congrArg (·.obj (f, g, h)) (e_assoc (V := Cat) a b c d)

instance : Bicategory C where
  Hom a b := (a ⟶[Cat] b).α
  homCategory a b := (a ⟶[Cat] b).str
  id a := (eId Cat a).obj ⟨⟨()⟩⟩
  comp {a b c} f g := (eComp Cat a b c).obj (f, g)
  whiskerLeft {_ _ _} f {_ _} η := (eComp Cat ..).map (𝟙 f, η)
  whiskerRight η h := (eComp Cat ..).map (η, 𝟙 h)
  associator f g h := eqToIso (assoc (obj := C) f g h)
  leftUnitor f := eqToIso (id_comp (obj := C) f)
  rightUnitor f := eqToIso (comp_id (obj := C) f)
  whiskerLeft_id _ _ := Functor.map_id ..
  whiskerLeft_comp {_ _ _} _ {_ _ _} _ _ := by
    refine .trans ?_ (Functor.map_comp ..)
    congr 2; exact (id_comp (𝟙 _)).symm
  id_whiskerLeft {_ _ _ _} η := by
    simp [← heq_eq_eq]; rw [← Functor.map_id]
    exact congr_arg_heq (·.map η) (e_id_comp (V := Cat) ..)
  comp_whiskerLeft {_ _ _ _} f g {_ _} η := by
    simp [← heq_eq_eq]; rw [← Functor.map_id]
    exact congr_arg_heq
      (·.map (X := (_, _, _)) (Y := (_, _, _)) (𝟙 f, 𝟙 g, η)) (e_assoc (V := Cat) ..)
  id_whiskerRight _ _ := Functor.map_id ..
  comp_whiskerRight  {_ _ _} _ {_ _ _} _ _ := by
    refine .trans ?_ (Functor.map_comp ..)
    congr 2; exact (id_comp (𝟙 _)).symm
  whiskerRight_id {_ _ _ _} η := by
    simp [← heq_eq_eq]; rw [← Functor.map_id]
    exact congr_arg_heq (·.map η) (e_comp_id (V := Cat) ..)
  whiskerRight_comp {_ _ _ _ _ _} η g h := by
    simp [← heq_eq_eq]; rw [← Functor.map_id]
    exact .symm <| congr_arg_heq
      (·.map (X := (_, _, _)) (Y := (_, _, _)) (η, 𝟙 g, 𝟙 h)) (e_assoc (V := Cat) ..)
  whisker_assoc {_ _ _ _} f {_ _} η h := by
    simp [← heq_eq_eq]
    exact congr_arg_heq
      (·.map (X := (_, _, _)) (Y := (_, _, _)) (𝟙 f, η, 𝟙 h)) (e_assoc (V := Cat) ..)
  whisker_exchange η θ := by
    refine (Functor.map_comp ..).symm.trans <| .trans ?_ (Functor.map_comp ..)
    congr 1; apply Prod.ext
    · exact (id_comp _).trans (comp_id _).symm
    · exact (comp_id _).trans (id_comp _).symm
  pentagon {a b c d e} f g h i := by
    let foo (b : C) (x y) {x' y'} (hx : x = x') (hy : y = y') :
        (eComp Cat a b e).obj (x, y) ⟶ (eComp Cat a b e).obj (x', y') :=
      (eComp Cat a b e).map (eqToHom hx, eqToHom hy)
    suffices ∀ x w h1 h2 h3 h4,
      foo d x i h1 rfl ≫ eqToHom h2 ≫ foo b f w rfl h3 = eqToHom h4 by
      simpa [foo] using this ..
    rintro _ _  rfl _ rfl _
    conv => enter [1, 1]; apply Functor.map_id
    conv => enter [1, 2, 2]; apply Functor.map_id
    simp
  triangle {a b c} f g := by
    let foo (x y) {x' y'} (hx : x = x') (hy : y = y') :
        (eComp Cat a b c).obj (x, y) ⟶ (eComp Cat a b c).obj (x', y') :=
      (eComp Cat a b c).map (eqToHom hx, eqToHom hy)
    dsimp
    suffices ∀ f' g' h1 h2 h3, eqToHom h1 ≫ foo f g' rfl h2 = foo f' g h3 rfl from this ..
    rintro _ _ _ rfl rfl; simp

instance : Bicategory.Strict C where

end


end CategoryTheory

-- The payoff is now we get to develop some category theory of quasi-categories.
namespace SSet

namespace Quasicategory

-- variable {A B : SSet} [Quasicategory A] [Quasicategory B] (f : B ⟶ A) (u : A ⟶ B)
-- variable {A B : QCat} (f : B ⟶ A) (u : A ⟶ B)

-- def Adjunction : Type := CategoryTheory.Bicategory.Adjunction (B := QCat) f u


end Quasicategory

end SSet
