import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The simplicial join

This file defines the join bifunctor by extending simplicial sets to augmented
simplicial sets with terminal augmentation, taking Day convolution along ordinal
sum on `Δ₊`, and restricting back to ordinary simplices.

The finite pointwise formula for this Day convolution, the standard-simplex
calculation, and the monomorphism lemmas are the next missing API layer.
-/

open CategoryTheory Simplicial Opposite Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.DayFunctor
open scoped Simplicial

universe u

namespace SSet

noncomputable section

/-- An ordinary simplicial set as an augmented simplicial set with terminal
augmentation. -/
def terminalAugmentedObj (X : SSet.{u}) : SSet.Augmented.{u} where
  left := X
  right := PUnit.{u + 1}
  hom :=
    { app := fun n => TypeCat.ofHom (fun _ : X.obj n => PUnit.unit)
      naturality := by
        intro n m f
        ext x
        rfl }

/-- Add the terminal augmentation to an ordinary simplicial set. -/
def terminalAugmented : SSet.{u} ⥤ SSet.Augmented.{u} where
  obj X := terminalAugmentedObj X
  map {X Y} f :=
    { left := f
      right := 𝟙 PUnit.{u + 1}
      w := by
        ext n x
        rfl }
  map_id X := by
    ext n x
    · rfl
    · rfl
  map_comp {X Y Z} f g := by
    ext n x
    · rfl
    · rfl

/-- The augmented presheaf associated to a simplicial set. -/
def augmentedPresheaf :
    SSet.{u} ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :=
  terminalAugmented ⋙
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse

/-- Day functors on augmented simplicial sets. -/
abbrev AugDay : Type (u + 1) :=
  AugmentedSimplexCategoryᵒᵖ ⊛⥤ Type u

/-- The augmented presheaf associated to a simplicial set, viewed in the Day
functor category. -/
def augmentedDay : SSet.{u} ⥤ AugDay.{u} :=
  augmentedPresheaf ⋙
    (DayFunctor.equiv AugmentedSimplexCategoryᵒᵖ (Type u)).inverse

/-- Restrict an augmented presheaf to ordinary simplices. -/
def restrictAugmentedPresheaf :
    (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj AugmentedSimplexCategory.inclusion.op

/-- Restrict a Day functor on augmented simplices to an ordinary simplicial set. -/
def restrictAugmentedDay : AugDay.{u} ⥤ SSet.{u} :=
  (DayFunctor.equiv AugmentedSimplexCategoryᵒᵖ (Type u)).functor ⋙
    restrictAugmentedPresheaf

/-- The simplicial join as Day convolution on terminally augmented simplicial
sets, restricted back to ordinary simplices. -/
def joinFunctor : SSet.{u} ⥤ SSet.{u} ⥤ SSet.{u} :=
  augmentedDay ⋙
    curriedTensor AugDay.{u} ⋙
    (Functor.whiskeringLeft SSet.{u} AugDay.{u} AugDay.{u}).obj augmentedDay ⋙
    (Functor.whiskeringRight SSet.{u} AugDay.{u} SSet.{u}).obj restrictAugmentedDay

/-- The join of two simplicial sets `X ⋆ Y`. -/
def join (X Y : SSet.{u}) : SSet.{u} :=
  (joinFunctor.obj X).obj Y

@[inherit_doc] scoped infixr:70 " ⋆ " => SSet.join

/-- Functoriality on maps, packaged for downstream use. -/
def joinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X ⋆ Y ⟶ X' ⋆ Y' :=
  (joinFunctor.map f).app Y ≫ (joinFunctor.obj X').map g

/-- Index of the mixed simplices in the expected pointwise formula. -/
def JoinIndex (n : ℕ) : Type :=
  { p : ℕ × ℕ // p.1 + p.2 + 1 = n }

/-- The expected set of `n`-simplices of the join. -/
def joinObj (X Y : SSet.{u}) (n : ℕ) : Type u :=
  X _⦋n⦌ ⊕ Y _⦋n⦌ ⊕
    (Σ p : JoinIndex n, X _⦋p.1.1⦌ × Y _⦋p.1.2⦌)

/-- Naturality square for the join bifunctor. -/
theorem joinMap_comm {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    joinMap f (𝟙 C) ≫ joinMap (𝟙 B) g =
      joinMap (𝟙 A) g ≫ joinMap f (𝟙 D) := by
  have h₁ : (joinFunctor.obj B).map (𝟙 C) =
      𝟙 ((joinFunctor.obj B).obj C) := by simp
  have h₂ : (joinFunctor.map (𝟙 B)).app C =
      𝟙 ((joinFunctor.obj B).obj C) := by
    simp
  have h₃ : (joinFunctor.map (𝟙 A)).app C =
      𝟙 ((joinFunctor.obj A).obj C) := by
    simp
  have h₄ : (joinFunctor.obj B).map (𝟙 D) =
      𝟙 ((joinFunctor.obj B).obj D) := by simp
  unfold joinMap join
  rw [h₁, h₂, h₃, h₄]
  simp only [Category.comp_id, Category.id_comp]
  exact ((joinFunctor.map f).naturality g).symm

/-- The Leibniz join of `f : A ⟶ B` and `g : C ⟶ D`. -/
def leibnizJoin {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    pushout (joinMap f (𝟙 C)) (joinMap (𝟙 A) g) ⟶ B ⋆ D :=
  pushout.desc (joinMap (𝟙 B) g) (joinMap f (𝟙 D)) (joinMap_comm f g)

end

end SSet
