import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

/-- The augmented representable presheaf, packaged as a Day functor. -/
def ucoyDay (X : AugmentedSimplexCategoryᵒᵖ) : AugDay.{u} :=
  DayFunctor.mk (uliftCoyoneda.{u}.obj (op X))

/-- Two-variable Yoneda identifies the Day convolution of two augmented
representables with the representable at their tensor product. -/
def twoVarYonedaCorep (X Y : AugmentedSimplexCategoryᵒᵖ) :
    ((Functor.whiskeringLeft (AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ)
          AugmentedSimplexCategoryᵒᵖ (Type u)).obj
        (tensor AugmentedSimplexCategoryᵒᵖ) ⋙
      coyoneda.obj (op (externalProduct (ucoyDay.{u} X).functor
        (ucoyDay.{u} Y).functor))).CorepresentableBy
      (uliftCoyoneda.{u}.obj (op (X ⊗ Y))) where
  homEquiv {H} :=
    { toFun := fun τ =>
        { app := fun xy => ↾fun fg =>
            H.map (fg.1.down ⊗ₘ fg.2.down) (uliftCoyonedaEquiv.{u} τ)
          naturality := by
            intro xy xy' h
            ext fg
            rcases fg with ⟨f, g⟩
            dsimp
            rw [← Functor.map_comp_apply H]
            apply congrArg (fun k => H.map k (uliftCoyonedaEquiv τ))
            change (f.down ≫ h.1) ⊗ₘ (g.down ≫ h.2) =
              (f.down ⊗ₘ g.down) ≫ (h.1 ⊗ₘ h.2)
            simp }
      invFun := fun α =>
        uliftCoyonedaEquiv.{u}.symm (α.app (X, Y) (ULift.up (𝟙 X), ULift.up (𝟙 Y)))
      left_inv := by
        intro τ
        apply uliftCoyonedaEquiv.injective
        simp [uliftCoyonedaEquiv]
      right_inv := by
        intro α
        apply NatTrans.ext
        funext xy
        ext fg
        rcases fg with ⟨f, g⟩
        let hxy : (X, Y) ⟶ xy := (f.down, g.down)
        have hα := congrArg
          (fun e => (ConcreteCategory.hom e) (ULift.up (𝟙 X), ULift.up (𝟙 Y)))
          (α.naturality hxy)
        have hfg :
            (ConcreteCategory.hom
                ((externalProduct (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor).map hxy))
              (ULift.up (𝟙 X), ULift.up (𝟙 Y)) = (f, g) := by
          rcases f with ⟨f⟩
          rcases g with ⟨g⟩
          apply Prod.ext
          · change ULift.up ((𝟙 X) ≫ f) = ULift.up f
            simp
          · change ULift.up ((𝟙 Y) ≫ g) = ULift.up g
            simp
        simp only [Equiv.apply_symm_apply]
        change (ConcreteCategory.hom (H.map (f.down ⊗ₘ g.down)))
            ((ConcreteCategory.hom (α.app (X, Y))) (ULift.up (𝟙 X), ULift.up (𝟙 Y))) =
          (ConcreteCategory.hom (α.app xy)) (f, g)
        have hα' :
            (ConcreteCategory.hom (H.map (f.down ⊗ₘ g.down)))
                ((ConcreteCategory.hom (α.app (X, Y))) (ULift.up (𝟙 X), ULift.up (𝟙 Y))) =
              (ConcreteCategory.hom (α.app xy))
                ((ConcreteCategory.hom
                    ((externalProduct (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor).map hxy))
                  (ULift.up (𝟙 X), ULift.up (𝟙 Y))) := by
          simpa [hxy, ucoyDay, uliftCoyoneda, tensorHom_def, Category.assoc] using hα.symm
        rw [hfg] at hα'
        simpa using hα' }
  homEquiv_comp {H H'} β τ := by
    apply NatTrans.ext
    funext xy
    ext fg
    rcases fg with ⟨f, g⟩
    change (ConcreteCategory.hom (H'.map (f.down ⊗ₘ g.down)))
        (uliftCoyonedaEquiv.{u} (τ ≫ β)) =
      (ConcreteCategory.hom (β.app (xy.1 ⊗ xy.2)))
        ((ConcreteCategory.hom (H.map (f.down ⊗ₘ g.down))) (uliftCoyonedaEquiv.{u} τ))
    rw [uliftCoyonedaEquiv_comp]
    simp

/-- The Day tensor product of two augmented representables is the augmented
representable at their tensor product. -/
def ucoyTensorFunctorIso (X Y : AugmentedSimplexCategoryᵒᵖ) :
    (ucoyDay.{u} X ⊗ ucoyDay.{u} Y).functor ≅ (ucoyDay.{u} (X ⊗ Y)).functor :=
  letI : DayConvolution (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution
      (C := AugmentedSimplexCategoryᵒᵖ) (V := Type u) AugDay.{u}
      (ucoyDay.{u} X) (ucoyDay.{u} Y)
  (DayConvolution.corepresentableBy
      (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor).uniqueUpToIso
    (twoVarYonedaCorep.{u} X Y)

/-- Day-functor form of `ucoyTensorFunctorIso`. -/
def ucoyTensorIso (X Y : AugmentedSimplexCategoryᵒᵖ) :
    ucoyDay.{u} X ⊗ ucoyDay.{u} Y ≅ ucoyDay.{u} (X ⊗ Y) :=
  (DayFunctor.equiv AugmentedSimplexCategoryᵒᵖ (Type u)).inverse.mapIso
    (ucoyTensorFunctorIso.{u} X Y)

/-- On ordinary simplex objects, the augmented inclusion is fully faithful. -/
def augmentedInclusionHomEquiv (m n : SimplexCategory) :
    (AugmentedSimplexCategory.inclusion.obj m ⟶
      AugmentedSimplexCategory.inclusion.obj n) ≃ (m ⟶ n) where
  toFun f := WithInitial.down f
  invFun f := AugmentedSimplexCategory.inclusion.map f
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting the augmented representable on `⦋a⦌` recovers `Δ[a]`. -/
def ucoyRestrictedStdEquiv (a : ℕ) (n : SimplexCategoryᵒᵖ) :
    (AugmentedSimplexCategory.inclusion.op ⋙
        (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor).obj n ≃
      (SSet.stdSimplex.{u}.obj ⦋a⦌).obj n where
  toFun x := ULift.up (WithInitial.down x.down.unop)
  invFun y := ULift.up (AugmentedSimplexCategory.inclusion.map y.down).op
  left_inv x := by
    rcases x with ⟨x⟩
    rfl
  right_inv y := by
    rcases y with ⟨y⟩
    rfl

/-- The restricted augmented representable on `⦋a⦌` is `Δ[a]`. -/
def ucoyRestrictedStdIso (a : ℕ) :
    AugmentedSimplexCategory.inclusion.op ⋙
        (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor ≅
      SSet.stdSimplex.{u}.obj ⦋a⦌ :=
  NatIso.ofComponents (fun n => Equiv.toIso <| ucoyRestrictedStdEquiv.{u} a n) (by
    intro n m f
    ext x
    rcases x with ⟨x⟩
    rfl)

/-- The drop of the augmented representable on `⦋a⦌` is `Δ[a]`. -/
def ucoyDropStdIso (a : ℕ) :
    (AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj
        (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor).left ≅
      (terminalAugmented.obj (SSet.stdSimplex.{u}.obj ⦋a⦌)).left :=
  (AugmentedSimplexCategory.equivAugmentedSimplicialObjectFunctorCompDropIso.app
      (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor) ≪≫
    ucoyRestrictedStdIso.{u} a

/-- The augmentation point of the augmented representable on `⦋a⦌` is terminal. -/
def ucoyPointStdIso (a : ℕ) :
    (AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj
        (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor).right ≅
      (terminalAugmented.obj (SSet.stdSimplex.{u}.obj ⦋a⦌)).right :=
  Equiv.toIso
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ULift.up (WithInitial.homTo ⦋a⦌).op
      left_inv := by
        intro x
        rcases x with ⟨x⟩
        cases x.unop
        rfl
      right_inv := by
        intro x
        cases x
        rfl }

/-- The augmented representable on `⦋a⦌` is the terminally augmented standard simplex. -/
def ucoyAugmentedStdIso (a : ℕ) :
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj
        (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor ≅
      terminalAugmented.obj (SSet.stdSimplex.{u}.obj ⦋a⦌) :=
  Comma.isoMk (ucoyDropStdIso.{u} a) (ucoyPointStdIso.{u} a) (by
    ext n x
    rfl)

/-- The terminal augmented standard simplex is the augmented representable on `⦋a⦌`. -/
def augmentedPresheafStdIso (a : ℕ) :
    augmentedPresheaf.obj (SSet.stdSimplex.{u}.obj ⦋a⦌) ≅
      (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor :=
  AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.mapIso
      (ucoyAugmentedStdIso.{u} a).symm ≪≫
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.unitIso.symm.app
      (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor

/-- Day-functor form of `augmentedPresheafStdIso`. -/
def augmentedDayStdIso (a : ℕ) :
    augmentedDay.obj (SSet.stdSimplex.{u}.obj ⦋a⦌) ≅
      ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌)) :=
  (DayFunctor.equiv AugmentedSimplexCategoryᵒᵖ (Type u)).inverse.mapIso
    (augmentedPresheafStdIso.{u} a)

/-- Ordinal-sum arithmetic in the augmented simplex category. -/
theorem ordinalSum_eq (a b : ℕ) :
    AugmentedSimplexCategory.inclusion.obj ⦋a⦌ ⊗
        AugmentedSimplexCategory.inclusion.obj ⦋b⦌ =
      AugmentedSimplexCategory.inclusion.obj ⦋a + b + 1⦌ :=
  rfl

/-- Ordinal-sum arithmetic after passing to the opposite category. -/
theorem opOrdinalSum_eq (a b : ℕ) :
    op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌) ⊗
        op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌) =
      op (AugmentedSimplexCategory.inclusion.obj ⦋a + b + 1⦌) :=
  rfl

/-- The join definition is the restriction of the Day tensor of terminal
augmentations. -/
theorem join_eq_restrict (X Y : SSet.{u}) :
    X ⋆ Y = restrictAugmentedDay.obj (augmentedDay.obj X ⊗ augmentedDay.obj Y) :=
  rfl

/-- Restricting a terminal augmentation returns the original simplicial set. -/
theorem restrict_augmentedDay_roundtrip (X : SSet.{u}) :
    restrictAugmentedDay.obj (augmentedDay.obj X) = X :=
  rfl

/-- The middle representable-monoidal isomorphism for standard simplices. -/
def joinMiddleIso (a b : ℕ) :
    augmentedDay.{u}.obj (SSet.stdSimplex.{u}.obj ⦋a⦌) ⊗
        augmentedDay.{u}.obj (SSet.stdSimplex.{u}.obj ⦋b⦌) ≅
      augmentedDay.{u}.obj (SSet.stdSimplex.{u}.obj ⦋a + b + 1⦌) :=
  (MonoidalCategory.tensorIso (C := AugDay.{u})
      (augmentedDayStdIso.{u} a) (augmentedDayStdIso.{u} b)) ≪≫
    ucoyTensorIso.{u}
      (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
      (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)) ≪≫
    (augmentedDayStdIso.{u} (a + b + 1)).symm

/-- Given the middle augmented-Day isomorphism, restriction gives the standard
simplex join isomorphism. -/
def joinStdSimplexOf (a b : ℕ)
    (B : augmentedDay.{u}.obj (SSet.stdSimplex.{u}.obj ⦋a⦌) ⊗
        augmentedDay.{u}.obj (SSet.stdSimplex.{u}.obj ⦋b⦌) ≅
      augmentedDay.{u}.obj (SSet.stdSimplex.{u}.obj ⦋a + b + 1⦌)) :
    SSet.stdSimplex.{u}.obj ⦋a⦌ ⋆ SSet.stdSimplex.{u}.obj ⦋b⦌ ≅
      SSet.stdSimplex.{u}.obj ⦋a + b + 1⦌ :=
  restrictAugmentedDay.mapIso B

/-- The join of standard simplices is the standard simplex on the ordinal sum. -/
def joinStdSimplex (a b : ℕ) :
    SSet.stdSimplex.{u}.obj ⦋a⦌ ⋆ SSet.stdSimplex.{u}.obj ⦋b⦌ ≅
      SSet.stdSimplex.{u}.obj ⦋a + b + 1⦌ :=
  joinStdSimplexOf.{u} a b (joinMiddleIso.{u} a b)

end

end SSet
