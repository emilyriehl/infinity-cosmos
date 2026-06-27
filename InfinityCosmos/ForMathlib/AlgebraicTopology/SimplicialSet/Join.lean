import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Coproducts
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
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

universe u w w'

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

abbrev AC := AugmentedSimplexCategoryᵒᵖ

lemma externalProduct_map_app_eq_tensorHom
    {F F' G G' : AC ⥤ Type u} (α : F ⟶ F') (β : G ⟶ G')
    (x y : AC) :
    ((externalProductBifunctor AC AC (Type u)).map
        (show (F, G) ⟶ (F', G') from ⟨α, β⟩)).app (x, y) =
      α.app x ⊗ₘ β.app y := by
  rw [externalProductBifunctor_map_app, tensorHom_def]

def rightExt (D : AugDay.{u}) : (AC ⥤ Type u) ⥤ (AC × AC ⥤ Type u) :=
  Functor.prod' (𝟭 _) ((Functor.const _).obj D.functor) ⋙
    externalProductBifunctor AC AC (Type u)

def bigLam (D : AugDay.{u}) : (AC ⥤ Type u) ⥤ (AC ⥤ Type u) :=
  (DayFunctor.equiv AC (Type u)).inverse ⋙ tensorRight D ⋙
    (DayFunctor.equiv AC (Type u)).functor

abbrev Rwhisk : (AC ⥤ Type u) ⥤ (AC × AC ⥤ Type u) :=
  (Functor.whiskeringLeft (AC × AC) AC (Type u)).obj (tensor AC)

def theta (D : AugDay.{u}) : rightExt D ⟶ bigLam D ⋙ Rwhisk where
  app F := DayFunctor.η (DayFunctor.mk F) D
  naturality {F G} f := by
    apply NatTrans.ext
    funext ab
    obtain ⟨x, y⟩ := ab
    have key :
        (DayFunctor.η (DayFunctor.mk F) D).app (x, y) ≫
            ((DayFunctor.Hom.mk f ▷ D).natTrans).app (x ⊗ y) =
          (f.app x ▷ D.functor.obj y) ≫
            (DayFunctor.η (DayFunctor.mk G) D).app (x, y) :=
      LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
        (C := AC) (V := Type u) (D := AugDay) (DayFunctor.Hom.mk f) D x y
    simp only [NatTrans.comp_app, Functor.comp_map, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app]
    exact key.symm

def thetaBar (D : AugDay.{u}) :
    rightExt D ⋙ Functor.lan (tensor AC) ⟶ bigLam D :=
  Functor.whiskerRight (theta D) (Functor.lan (tensor AC)) ≫
    Functor.whiskerLeft (bigLam D) (Functor.lanAdjunction (tensor AC) (Type u)).counit

instance thetaBar_app_isIso (D : AugDay.{u}) (F : AC ⥤ Type u) :
    IsIso ((thetaBar D).app F) := by
  have h3 : (thetaBar D).app F =
      ((Functor.lanAdjunction (tensor AC) (Type u)).homEquiv ((rightExt D).obj F)
        ((bigLam D).obj F)).symm ((theta D).app F) := by
    simp only [thetaBar, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Adjunction.homEquiv_counit]
  rw [h3]
  refine (Functor.isIso_lanAdjunction_homEquiv_symm_iff
    (L := tensor AC) (G := (bigLam D).obj F) ((theta D).app F)).mpr ?_
  exact inferInstanceAs
    (((DayFunctor.mk F) ⊗ D).functor.IsLeftKanExtension (DayFunctor.η (DayFunctor.mk F) D))

instance thetaBar_isIso (D : AugDay.{u}) : IsIso (thetaBar D) :=
  NatIso.isIso_of_isIso_app _

def bigLamIso (D : AugDay.{u}) : rightExt D ⋙ Functor.lan (tensor AC) ≅ bigLam D :=
  asIso (thetaBar D)

instance rightExt_pres (D : AugDay.{u}) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (rightExt D) := by
  apply preservesColimitsOfShape_of_evaluation
  intro ab
  exact preservesColimitsOfShape_of_natIso
    (NatIso.ofComponents (fun F => Iso.refl _) (by intro F G f; rfl) :
      (evaluation AC (Type u)).obj ab.1 ⋙ tensorRight (D.functor.obj ab.2) ≅
        rightExt D ⋙ (evaluation (AC × AC) (Type u)).obj ab)

instance lan_pres (J : Type w) [Category.{w'} J] :
    PreservesColimitsOfShape J
      (Functor.lan (tensor AC) : (AC × AC ⥤ Type u) ⥤ (AC ⥤ Type u)) :=
  (Functor.lanAdjunction (tensor AC) (Type u)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance bigLam_pres (D : AugDay.{u}) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (bigLam D) :=
  preservesColimitsOfShape_of_natIso (bigLamIso D)

instance tensorRight_pres (D : AugDay.{u}) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (tensorRight D) := by
  haveI : PreservesColimitsOfShape J (tensorRight D ⋙ (DayFunctor.equiv AC (Type u)).functor) := by
    rw [show tensorRight D ⋙ (DayFunctor.equiv AC (Type u)).functor =
        (DayFunctor.equiv AC (Type u)).functor ⋙ bigLam D from rfl]
    infer_instance
  exact Limits.preservesColimitsOfShape_of_reflects_of_preserves
    (tensorRight D) (DayFunctor.equiv AC (Type u)).functor

/-- The augmented presheaf associated to a simplicial set, viewed in the Day
functor category. -/
def augmentedDay : SSet.{u} ⥤ AugDay.{u} :=
  augmentedPresheaf ⋙
    (DayFunctor.equiv AugmentedSimplexCategoryᵒᵖ (Type u)).inverse

theorem constPUnit_preservesConnectedColimits {J : Type w} [Category.{w'} J] [IsConnected J] :
    PreservesColimitsOfShape J ((Functor.const SSet.{u}).obj PUnit.{u+1}) where
  preservesColimit {K} :=
    { preserves := fun {c} _ => ⟨by
        refine IsColimit.ofIsoColimit (isColimitConstCocone J PUnit.{u+1}) ?_
        refine Cocone.ext (Iso.refl _) ?_
        intro j
        ext x
        rfl⟩ }

instance augmentedPresheaf_preservesConnectedColimits (J : Type w) [Category.{w'} J]
    [IsConnected J] [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J augmentedPresheaf.{u} := by
  apply preservesColimitsOfShape_of_evaluation
  intro a
  rcases a with ⟨a⟩
  cases a with
  | star =>
      exact constPUnit_preservesConnectedColimits
  | of n =>
      change PreservesColimitsOfShape J
        (((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op n) : SSet.{u} ⥤ Type u))
      infer_instance

instance augmentedDay_preservesConnectedColimits (J : Type w) [Category.{w'} J]
    [IsConnected J] [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J augmentedDay.{u} := by
  dsimp [augmentedDay]
  infer_instance

/-- Restrict an augmented presheaf to ordinary simplices. -/
def restrictAugmentedPresheaf :
    (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj AugmentedSimplexCategory.inclusion.op

/-- Restrict a Day functor on augmented simplices to an ordinary simplicial set. -/
def restrictAugmentedDay : AugDay.{u} ⥤ SSet.{u} :=
  (DayFunctor.equiv AugmentedSimplexCategoryᵒᵖ (Type u)).functor ⋙
    restrictAugmentedPresheaf

instance restrictAugmentedPresheaf_preservesColimitsOfShape (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J restrictAugmentedPresheaf.{u} := by
  change PreservesColimitsOfShape J
    (((Functor.whiskeringLeft SimplexCategoryᵒᵖ AugmentedSimplexCategoryᵒᵖ (Type u)).obj
      AugmentedSimplexCategory.inclusion.op))
  infer_instance

instance restrictAugmentedDay_preservesColimitsOfShape (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J restrictAugmentedDay.{u} := by
  dsimp [restrictAugmentedDay]
  infer_instance

/-- The simplicial join as Day convolution on terminally augmented simplicial
sets, restricted back to ordinary simplices. -/
def joinFunctor : SSet.{u} ⥤ SSet.{u} ⥤ SSet.{u} :=
  augmentedDay ⋙
    curriedTensor AugDay.{u} ⋙
    (Functor.whiskeringLeft SSet.{u} AugDay.{u} AugDay.{u}).obj augmentedDay ⋙
    (Functor.whiskeringRight SSet.{u} AugDay.{u} SSet.{u}).obj restrictAugmentedDay

theorem joinFunctor_flip_preservesConnectedColimits_of_tensorRight
    (J : Type w) [Category.{w'} J] [IsConnected J] [HasColimitsOfShape J (Type u)]
    (K : SSet.{u})
    [PreservesColimitsOfShape J (tensorRight (augmentedDay.obj K))] :
    PreservesColimitsOfShape J (joinFunctor.flip.obj K) := by
  change PreservesColimitsOfShape J
    (augmentedDay ⋙ tensorRight (augmentedDay.obj K) ⋙ restrictAugmentedDay)
  infer_instance

/-- The join of two simplicial sets `X ⋆ Y`. -/
def join (X Y : SSet.{u}) : SSet.{u} :=
  (joinFunctor.obj X).obj Y

@[inherit_doc] scoped infixr:70 " ⋆ " => SSet.join

/-- Functoriality on maps, packaged for downstream use. -/
def joinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X ⋆ Y ⟶ X' ⋆ Y' :=
  (joinFunctor.map f).app Y ≫ (joinFunctor.obj X').map g

/-- The Day-unit map into the terminal augmentation of a simplicial set. -/
def augmentedDayUnitTo (X : SSet.{u}) : 𝟙_ AugDay.{u} ⟶ augmentedDay.obj X :=
  DayFunctor.unitDesc (C := AugmentedSimplexCategoryᵒᵖ) (V := Type u)
    (↾fun _ => PUnit.unit)

theorem isIso_of_isEmpty_target {S T : Type u} (f : S ⟶ T) [IsEmpty T] : IsIso f := by
  haveI : IsEmpty S := Function.isEmpty f
  rw [isIso_iff_bijective]
  exact ⟨fun a => isEmptyElim a, fun b => isEmptyElim b⟩

theorem isIso_of_subsingleton {S T : Type u} (f : S ⟶ T)
    [Subsingleton S] [Nonempty S] [Subsingleton T] : IsIso f := by
  rw [isIso_iff_bijective]
  exact ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨Classical.arbitrary S, Subsingleton.elim _ _⟩⟩

instance nu_isIso : IsIso (DayFunctor.ν AC (Type u)) := by
  haveI hsub : Subsingleton ((𝟙_ AC : AC) ⟶ 𝟙_ AC) :=
    inferInstanceAs (Subsingleton (op WithInitial.star ⟶ (op WithInitial.star : AC)))
  haveI : (Functor.fromPUnit.{0} (𝟙_ AC)).Full :=
    { map_surjective := fun {a b} f =>
        ⟨Discrete.eqToHom (Subsingleton.elim _ _), @Subsingleton.elim _ hsub _ f⟩ }
  have hpt : (Functor.LeftExtension.mk _ (DayFunctor.νNatTrans AC (Type u))).IsPointwiseLeftKanExtensionAt
      (𝟙_ AC) :=
    (LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit AC
      (Type u) AugDay) (𝟙_ AC)
  exact hpt.isIso_hom_app (X := Discrete.mk PUnit.unit)

instance bot_obj_isEmpty (m : SimplexCategory) : IsEmpty ((⊥_ SSet.{u}).obj (op m)) :=
  Function.isEmpty
    ((PreservesInitial.iso ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op m)) ≪≫
      Types.initialIso).hom)

instance augmentedDayUnitTo_initial_isIso : IsIso (augmentedDayUnitTo (⊥_ SSet.{u})) := by
  have hnt : IsIso ((augmentedDayUnitTo (⊥_ SSet.{u})).natTrans) := by
    haveI : ∀ c, IsIso (((augmentedDayUnitTo (⊥_ SSet.{u})).natTrans).app c) := by
      intro c
      obtain ⟨a⟩ := c
      cases a with
      | star =>
          haveI : Subsingleton (𝟙_ (Type u)) := inferInstanceAs (Subsingleton PUnit.{u+1})
          haveI : Subsingleton ((𝟙_ AugDay.{u}).functor.obj (op WithInitial.star)) :=
            Equiv.subsingleton ((asIso (DayFunctor.ν AC (Type u))).toEquiv).symm
          haveI : Nonempty ((𝟙_ AugDay.{u}).functor.obj (op WithInitial.star)) :=
            ⟨(DayFunctor.ν AC (Type u)) PUnit.unit⟩
          haveI : Subsingleton ((augmentedDay.obj (⊥_ SSet.{u})).functor.obj
              (op WithInitial.star)) :=
            inferInstanceAs (Subsingleton PUnit.{u+1})
          exact isIso_of_subsingleton _
      | of m =>
          haveI : IsEmpty ((augmentedDay.obj (⊥_ SSet.{u})).functor.obj
              (op (WithInitial.of m))) :=
            inferInstanceAs (IsEmpty ((⊥_ SSet.{u}).obj (op m)))
          exact isIso_of_isEmpty_target _
    exact NatIso.isIso_of_isIso_app _
  haveI : IsIso ((DayFunctor.equiv AC (Type u)).functor.map
      (augmentedDayUnitTo (⊥_ SSet.{u}))) := by
    change IsIso ((augmentedDayUnitTo (⊥_ SSet.{u})).natTrans)
    exact hnt
  exact isIso_of_reflects_iso _ (DayFunctor.equiv AC (Type u)).functor

theorem augmentedDayUnitTo_naturality {X X' : SSet.{u}} (f : X ⟶ X') :
    augmentedDayUnitTo X ≫ augmentedDay.map f = augmentedDayUnitTo X' := by
  apply DayFunctor.unit_hom_ext
  ext x
  simp [augmentedDayUnitTo]
  change PUnit.unit = PUnit.unit
  rfl

/-- The right-factor inclusion `Y ⟶ X ⋆ Y`. -/
def joinInr (X Y : SSet.{u}) : Y ⟶ X ⋆ Y := by
  change restrictAugmentedDay.obj (augmentedDay.obj Y) ⟶
    restrictAugmentedDay.obj (augmentedDay.obj X ⊗ augmentedDay.obj Y)
  exact restrictAugmentedDay.map
    ((λ_ (augmentedDay.obj Y)).inv ≫
      (augmentedDayUnitTo X) ▷ (augmentedDay.obj Y))

theorem joinInr_naturality_left {X X' : SSet.{u}} (f : X ⟶ X') (Y : SSet.{u}) :
    joinInr X Y ≫ (joinFunctor.map f).app Y = joinInr X' Y := by
  change
    restrictAugmentedDay.map
          ((λ_ (augmentedDay.obj Y)).inv ≫
            (augmentedDayUnitTo X) ▷ (augmentedDay.obj Y)) ≫
        restrictAugmentedDay.map ((augmentedDay.map f) ▷ (augmentedDay.obj Y)) =
      restrictAugmentedDay.map
          ((λ_ (augmentedDay.obj Y)).inv ≫
            (augmentedDayUnitTo X') ▷ (augmentedDay.obj Y))
  rw [← Functor.map_comp]
  congr 1
  rw [Category.assoc, ← MonoidalCategory.comp_whiskerRight, augmentedDayUnitTo_naturality f]

/-- The left-factor inclusion `X ⟶ X ⋆ Y`. -/
def joinInl' (X Y : SSet.{u}) : X ⟶ X ⋆ Y := by
  change restrictAugmentedDay.obj (augmentedDay.obj X) ⟶
    restrictAugmentedDay.obj (augmentedDay.obj X ⊗ augmentedDay.obj Y)
  exact restrictAugmentedDay.map
    ((ρ_ (augmentedDay.obj X)).inv ≫
      (augmentedDay.obj X) ◁ (augmentedDayUnitTo Y))

theorem joinInl'_naturality_right {Y Y' : SSet.{u}} (g : Y ⟶ Y') (X : SSet.{u}) :
    joinInl' X Y ≫ (joinFunctor.obj X).map g = joinInl' X Y' := by
  change
    restrictAugmentedDay.map
          ((ρ_ (augmentedDay.obj X)).inv ≫
            (augmentedDay.obj X) ◁ (augmentedDayUnitTo Y)) ≫
        restrictAugmentedDay.map ((augmentedDay.obj X) ◁ (augmentedDay.map g)) =
      restrictAugmentedDay.map
          ((ρ_ (augmentedDay.obj X)).inv ≫
            (augmentedDay.obj X) ◁ (augmentedDayUnitTo Y'))
  rw [← Functor.map_comp]
  congr 1
  rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, augmentedDayUnitTo_naturality g]

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

/-- The map of augmented representables induced by a map of ordinary simplex objects. -/
def ucoyMapOf {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌) :
    ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌)) ⟶
      ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)) :=
  DayFunctor.Hom.mk (uliftCoyoneda.{u}.map ((AugmentedSimplexCategory.inclusion.map f).op).op)

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

lemma ucoyTensorIso_hom_η_apply (X Y x y : AugmentedSimplexCategoryᵒᵖ)
    (fg : ((externalProduct (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor).obj (x, y))) :
    ((ConcreteCategory.hom ((ucoyTensorIso.{u} X Y).hom.natTrans.app (x ⊗ y)))
      ((ConcreteCategory.hom ((η (ucoyDay.{u} X) (ucoyDay.{u} Y)).app (x, y))) fg)) =
    ULift.up (fg.1.down ⊗ₘ fg.2.down) := by
  letI : DayConvolution (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution
      (C := AugmentedSimplexCategoryᵒᵖ) (V := Type u) AugDay.{u}
      (ucoyDay.{u} X) (ucoyDay.{u} Y)
  have hcore :
      (DayConvolution.corepresentableBy (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor).homEquiv
          (((ucoyTensorIso.{u} X Y).hom).natTrans) =
      (twoVarYonedaCorep.{u} X Y).homEquiv (𝟙 (uliftCoyoneda.{u}.obj (op (X ⊗ Y)))) := by
    let e := DayConvolution.corepresentableBy (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor
    let e' := twoVarYonedaCorep.{u} X Y
    change e.homEquiv (((ucoyTensorIso.{u} X Y).hom).natTrans) =
      e'.homEquiv (𝟙 (uliftCoyoneda.{u}.obj (op (X ⊗ Y))))
    dsimp [ucoyTensorIso, ucoyTensorFunctorIso]
    change e.homEquiv ((e.uniqueUpToIso e').hom) = e'.homEquiv (𝟙 _)
    dsimp [Functor.CorepresentableBy.uniqueUpToIso]
    change e.homEquiv (e.homEquiv.symm (e'.homEquiv (𝟙 _))) = e'.homEquiv (𝟙 _)
    exact e.homEquiv.apply_symm_apply (e'.homEquiv (𝟙 _))
  have h := DayConvolution.corepresentableBy_homEquiv_apply_app
    (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor (((ucoyTensorIso.{u} X Y).hom).natTrans) (x, y)
  have happ := congrArg (fun α => α.app (x, y)) hcore
  have h2 :
      ((twoVarYonedaCorep.{u} X Y).homEquiv (𝟙 (uliftCoyoneda.{u}.obj (op (X ⊗ Y))))).app (x, y) =
        (DayConvolution.unit (ucoyDay.{u} X).functor (ucoyDay.{u} Y).functor).app (x, y) ≫
          (((ucoyTensorIso.{u} X Y).hom).natTrans.app (x ⊗ y)) := by
    rw [← happ]
    exact h
  change (ConcreteCategory.hom (((DayConvolution.unit (ucoyDay.{u} X).functor
      (ucoyDay.{u} Y).functor).app (x, y)) ≫
      (((ucoyTensorIso.{u} X Y).hom).natTrans.app (x ⊗ y)))) fg =
    ULift.up (fg.1.down ⊗ₘ fg.2.down)
  rw [← h2]
  rcases fg with ⟨f, g⟩
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  simp [twoVarYonedaCorep, uliftCoyonedaEquiv]

lemma ucoyTensorIso_naturality {a a' b b' : ℕ}
    (f : ⦋a⦌ ⟶ ⦋a'⦌) (g : ⦋b⦌ ⟶ ⦋b'⦌) :
    (ucoyMapOf.{u} f ▷ ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)) ≫
        ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌)) ◁ ucoyMapOf.{u} g ≫
        (ucoyTensorIso.{u}
          (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌))
          (op (AugmentedSimplexCategory.inclusion.obj ⦋b'⦌))).hom) =
      (ucoyTensorIso.{u}
          (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
          (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).hom ≫
        ucoyMapOf.{u} (AugmentedSimplexCategory.tensorHomOf f g) := by
  rw [← Category.assoc]
  rw [← MonoidalCategory.tensorHom_def (ucoyMapOf.{u} f) (ucoyMapOf.{u} g)]
  apply DayFunctor.tensor_hom_ext
  intro x y
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
  change (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
      AugmentedSimplexCategoryᵒᵖ (Type u)
      (ucoyDay (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌)))
      (ucoyDay (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)))).app (x, y) ≫
      ((LawfulDayConvolutionMonoidalCategoryStruct.ι
        AugmentedSimplexCategoryᵒᵖ (Type u) AugDay.{u}).map
          (ucoyMapOf.{u} f ⊗ₘ ucoyMapOf.{u} g)).app (x ⊗ y) ≫
        (ucoyTensorIso.{u}
          (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌))
          (op (AugmentedSimplexCategory.inclusion.obj ⦋b'⦌))).hom.natTrans.app (x ⊗ y) =
    (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
      AugmentedSimplexCategoryᵒᵖ (Type u)
      (ucoyDay (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌)))
      (ucoyDay (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)))).app (x, y) ≫
        (ucoyTensorIso.{u}
          (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
          (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).hom.natTrans.app (x ⊗ y) ≫
          (ucoyMapOf.{u} (AugmentedSimplexCategory.tensorHomOf f g)).natTrans.app (x ⊗ y)
  rw [reassoc_of% LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_tensorHom_app
    (C := AugmentedSimplexCategoryᵒᵖ) (V := Type u) (D := AugDay.{u})]
  ext fg
  rcases fg with ⟨φ, ψ⟩
  rcases φ with ⟨φ⟩
  rcases ψ with ⟨ψ⟩
  let fg₀ :
      ((externalProduct
          (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor
          (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).functor).obj
        (x, y)) := ({ down := φ }, { down := ψ })
  let α : (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))).functor ⟶
      (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌))).functor :=
    (ucoyMapOf.{u} f).natTrans
  let β : (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).functor ⟶
      (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b'⦌))).functor :=
    (ucoyMapOf.{u} g).natTrans
  let fg₁ :
      ((externalProduct
          (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌))).functor
          (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b'⦌))).functor).obj
        (x, y)) :=
    (ConcreteCategory.hom
      (α.app x ⊗ₘ β.app y)) fg₀
  change
    (ConcreteCategory.hom
      ((ucoyTensorIso.{u}
        (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌))
        (op (AugmentedSimplexCategory.inclusion.obj ⦋b'⦌))).hom.natTrans.app (x ⊗ y)))
      ((ConcreteCategory.hom
        ((η (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌)))
          (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b'⦌)))).app (x, y))) fg₁) =
    (ConcreteCategory.hom
      ((ucoyMapOf.{u} (AugmentedSimplexCategory.tensorHomOf f g)).natTrans.app (x ⊗ y)))
      ((ConcreteCategory.hom
        ((ucoyTensorIso.{u}
          (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
          (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).hom.natTrans.app (x ⊗ y)))
        ((ConcreteCategory.hom
          ((η (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌)))
            (ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)))).app (x, y))) fg₀))
  rw [ucoyTensorIso_hom_η_apply
    (X := op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌))
    (Y := op (AugmentedSimplexCategory.inclusion.obj ⦋b'⦌)) (x := x) (y := y) fg₁]
  rw [ucoyTensorIso_hom_η_apply
    (X := op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
    (Y := op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)) (x := x) (y := y) fg₀]
  simp [fg₀, fg₁, α, β, ucoyMapOf]
  apply ULift.ext
  change
    ((AugmentedSimplexCategory.inclusion.map f).op ≫ φ) ⊗ₘ
        ((AugmentedSimplexCategory.inclusion.map g).op ≫ ψ) =
      (AugmentedSimplexCategory.inclusion.map
          (AugmentedSimplexCategory.tensorHomOf f g)).op ≫ (φ ⊗ₘ ψ)
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  rfl

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

@[reassoc]
lemma augmentedDayStdIso_naturality {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌) :
    (augmentedDayStdIso.{u} a).hom ≫ ucoyMapOf.{u} f =
      augmentedDay.map (stdSimplex.map f) ≫ (augmentedDayStdIso.{u} b).hom := by
  ext n x
  cases n using Opposite.rec with
  | _ n =>
    cases n with
    | star =>
      cases x
      simp [ucoyMapOf, augmentedDayStdIso, augmentedPresheafStdIso, ucoyAugmentedStdIso,
        ucoyDropStdIso, ucoyPointStdIso, terminalAugmented, terminalAugmentedObj,
        augmentedPresheaf, augmentedDay]
      apply ULift.ext
      apply Quiver.Hom.unop_inj
      change WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋a⦌) ≫
          AugmentedSimplexCategory.inclusion.map f =
        WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)
      simp
    | of n =>
      rcases x with ⟨x⟩
      rfl

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

lemma joinMiddleIso_naturality {a a' b b' : ℕ}
    (f : ⦋a⦌ ⟶ ⦋a'⦌) (g : ⦋b⦌ ⟶ ⦋b'⦌) :
    augmentedDay.map (stdSimplex.{u}.map f) ▷ augmentedDay.obj (stdSimplex.{u}.obj ⦋b⦌) ≫
      augmentedDay.obj (stdSimplex.{u}.obj ⦋a'⦌) ◁ augmentedDay.map (stdSimplex.{u}.map g) ≫
      (joinMiddleIso.{u} a' b').hom =
    (joinMiddleIso.{u} a b).hom ≫
      augmentedDay.map (stdSimplex.{u}.map (AugmentedSimplexCategory.tensorHomOf f g)) := by
  dsimp [joinMiddleIso]
  simp only [Category.assoc]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [← augmentedDayStdIso_naturality f]
  rw [← augmentedDayStdIso_naturality g]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [MonoidalCategory.tensorHom_def_assoc (ucoyMapOf.{u} f) (ucoyMapOf.{u} g)]
  have htensor := ucoyTensorIso_naturality f g
  change (ucoyMapOf.{u} f ▷
      ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌)) ≫
      ucoyDay.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a'⦌)) ◁ ucoyMapOf.{u} g ≫
      (ucoyTensorIso.{u} (op (WithInitial.of ⦋a'⦌)) (op (WithInitial.of ⦋b'⦌))).hom) =
    (ucoyTensorIso.{u} (op (WithInitial.of ⦋a⦌)) (op (WithInitial.of ⦋b⦌))).hom ≫
      ucoyMapOf.{u} (AugmentedSimplexCategory.tensorHomOf f g) at htensor
  rw [reassoc_of% htensor]
  have hfinal :
      ucoyMapOf.{u} (AugmentedSimplexCategory.tensorHomOf f g) ≫
          (augmentedDayStdIso.{u} (a' + b' + 1)).inv =
        (augmentedDayStdIso.{u} (a + b + 1)).inv ≫
          augmentedDay.map
            (stdSimplex.{u}.map (AugmentedSimplexCategory.tensorHomOf f g)) := by
    rw [Iso.comp_inv_eq]
    rw [Category.assoc]
    rw [Iso.eq_inv_comp]
    exact augmentedDayStdIso_naturality (AugmentedSimplexCategory.tensorHomOf f g)
  change ((augmentedDayStdIso.{u} a).hom ⊗ₘ (augmentedDayStdIso.{u} b).hom) ≫
      (ucoyTensorIso.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
        (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).hom ≫
      ucoyMapOf.{u} (AugmentedSimplexCategory.tensorHomOf f g) ≫
      (augmentedDayStdIso.{u} (a' + b' + 1)).inv =
    ((augmentedDayStdIso.{u} a).hom ⊗ₘ (augmentedDayStdIso.{u} b).hom) ≫
      (ucoyTensorIso.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
        (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).hom ≫
      (augmentedDayStdIso.{u} (a + b + 1)).inv ≫
      augmentedDay.map (stdSimplex.{u}.map (AugmentedSimplexCategory.tensorHomOf f g))
  exact congrArg
    (fun k => ((augmentedDayStdIso.{u} a).hom ⊗ₘ (augmentedDayStdIso.{u} b).hom) ≫
      (ucoyTensorIso.{u} (op (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
        (op (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))).hom ≫ k) hfinal

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

theorem joinStdSimplex_naturality {a a' b b' : ℕ}
    (f : ⦋a⦌ ⟶ ⦋a'⦌) (g : ⦋b⦌ ⟶ ⦋b'⦌) :
    joinMap (stdSimplex.{u}.map f) (stdSimplex.{u}.map g) ≫ (joinStdSimplex.{u} a' b').hom =
      (joinStdSimplex.{u} a b).hom ≫
        stdSimplex.{u}.map (AugmentedSimplexCategory.tensorHomOf f g) := by
  unfold joinStdSimplex joinStdSimplexOf joinMap joinFunctor
  simp only [Functor.comp_map, Category.assoc]
  change restrictAugmentedDay.map
        ((augmentedDay.map (stdSimplex.{u}.map f)) ▷
          augmentedDay.obj (stdSimplex.{u}.obj ⦋b⦌)) ≫
      restrictAugmentedDay.map
        (augmentedDay.obj (stdSimplex.{u}.obj ⦋a'⦌) ◁
          (augmentedDay.map (stdSimplex.{u}.map g))) ≫
        restrictAugmentedDay.map (joinMiddleIso.{u} a' b').hom =
    restrictAugmentedDay.map (joinMiddleIso.{u} a b).hom ≫
      restrictAugmentedDay.map
        (augmentedDay.map
          (stdSimplex.{u}.map (AugmentedSimplexCategory.tensorHomOf f g)))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact joinMiddleIso_naturality f g

end

end SSet
