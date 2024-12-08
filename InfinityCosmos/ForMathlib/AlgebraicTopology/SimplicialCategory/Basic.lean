/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Ordinary
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Closed.FunctorToTypes

/-!
# Simplicial categories

A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.

## TODO

* construct a simplicial category structure on simplicial objects, so
that it applies in particular to simplicial sets
* obtain the adjunction property `(K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y)` when `K`, `X`, and `Y`
are simplicial sets
* develop the notion of "simplicial tensor" `K ⊗ₛ X : C` with `K : SSet` and `X : C`
an object in a simplicial category `C`
* define the notion of path between `0`-simplices of simplicial sets
* deduce the notion of homotopy between morphisms in a simplicial category
* obtain that homotopies in simplicial categories can be interpreted as given
by morphisms `Δ[1] ⊗ X ⟶ Y`.

## References
* [Daniel G. Quillen, *Homotopical algebra*, II §1][quillen-1967]

-/

universe v u

open CategoryTheory Category MonoidalCategory Simplicial SSet

namespace CategoryTheory

namespace SimplicialCategory
variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- The morphism `sHom K' L ⟶ sHom K L` induced by a morphism `K ⟶ K'`. -/
noncomputable abbrev sHomWhiskerRight {K K' : C} (f : K ⟶ K') (L : C) :
    sHom K' L ⟶ sHom K L := eHomWhiskerRight SSet f L

noncomputable abbrev sHomWhiskerRightIso {K K' : C} (i : K ≅ K') (L : C) :
    sHom K' L ≅ sHom K L := eHomWhiskerRightIso SSet i L

@[simp]
lemma sHomWhiskerRight_id (K L : C) : sHomWhiskerRight (𝟙 K) L = 𝟙 _ :=
  eHomWhiskerRight_id _ K L

@[simp, reassoc]
lemma sHomWhiskerRight_comp {K K' K'' : C} (f : K ⟶ K') (f' : K' ⟶ K'') (L : C) :
    sHomWhiskerRight (f ≫ f') L = sHomWhiskerRight f' L ≫ sHomWhiskerRight f L :=
  eHomWhiskerRight_comp _ f f' L

/-- The morphism `sHom K L ⟶ sHom K L'` induced by a morphism `L ⟶ L'`. -/
noncomputable abbrev sHomWhiskerLeft (K : C) {L L' : C} (g : L ⟶ L') :
    sHom K L ⟶ sHom K L' := eHomWhiskerLeft SSet K g

noncomputable abbrev sHomWhiskerLeftIso (K : C) {L L' : C} (i : L ≅ L') :
    sHom K L ≅ sHom K L' := eHomWhiskerLeftIso SSet K i

@[simp]
lemma sHomWhiskerLeft_id (K L : C) : sHomWhiskerLeft K (𝟙 L) = 𝟙 _ :=
  eHomWhiskerLeft_id _ _ _

@[simp, reassoc]
lemma sHomWhiskerLeft_comp (K : C) {L L' L'' : C} (g : L ⟶ L') (g' : L' ⟶ L'') :
    sHomWhiskerLeft K (g ≫ g') = sHomWhiskerLeft K g ≫ sHomWhiskerLeft K g' :=
  eHomWhiskerLeft_comp _ _ _ _

@[reassoc]
lemma sHom_whisker_exchange {K K' L L' : C} (f : K ⟶ K') (g : L ⟶ L') :
    sHomWhiskerLeft K' g ≫ sHomWhiskerRight f L' =
      sHomWhiskerRight f L ≫ sHomWhiskerLeft K g := eHom_whisker_exchange _ f g

attribute [local simp] sHom_whisker_exchange

noncomputable instance : SimplicialCategory SSet where
  toEnrichedCategory := inferInstanceAs (EnrichedCategory (_ ⥤ Type _) (_ ⥤ Type _))
  homEquiv {K} {L} :=
    letI e : (K ⟶ L) ≃ (K ⊗ 𝟙_ SSet ⟶ L) :=
      ⟨fun f => (ρ_ _).hom ≫ f, fun f => (ρ_ _).inv ≫ f, by aesop_cat, by aesop_cat⟩
    e.trans (Functor.homObjEquiv _ _ _).symm |>.trans (Functor.functorHomEquiv K L (𝟙_ SSet)).symm
  homEquiv_id := by aesop_cat
  homEquiv_comp := by aesop_cat

noncomputable instance : MonoidalClosed SSet where
  closed A := {
    rightAdj := (sHomFunctor _).obj ⟨A⟩
    adj := FunctorToTypes.adj _
  }

noncomputable instance : SymmetricCategory SSet := inferInstance

/-- The monoidal structure given by the `ChosenFiniteProducts` has good definitional properties,
like the following: -/
example (R S : SSet) (n : SimplexCategory) : (R ⊗ S).obj ⟨n⟩ = (R.obj ⟨n⟩ × S.obj ⟨n⟩) := rfl

end SimplicialCategory

end CategoryTheory
