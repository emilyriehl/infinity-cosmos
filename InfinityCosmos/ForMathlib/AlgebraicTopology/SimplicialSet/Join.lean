import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.ColimitType

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

/-- The image of a binary join of subcomplexes is the binary join of their images. -/
lemma image_sup {X Y : SSet.{u}} (A B : X.Subcomplex) (f : X ⟶ Y) :
    (A ⊔ B).image f = A.image f ⊔ B.image f := by
  apply le_antisymm
  · rw [Subcomplex.image_le_iff]
    apply sup_le
    · rw [← Subcomplex.image_le_iff]
      exact le_sup_left
    · rw [← Subcomplex.image_le_iff]
      exact le_sup_right
  · exact sup_le (Subcomplex.image_monotone f le_sup_left)
      (Subcomplex.image_monotone f le_sup_right)

/-- Image under `joinStdSimplex` of a standard-simplex range in the left join variable. -/
lemma image_range_joinMap_left (a a' b : ℕ) (f : ⦋a⦌ ⟶ ⦋a'⦌) :
    (Subcomplex.range (joinMap (stdSimplex.{u}.map f)
        (𝟙 (stdSimplex.{u}.obj ⦋b⦌)))).image (joinStdSimplex.{u} a' b).hom =
      Subcomplex.range
        (stdSimplex.{u}.map (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋b⦌))) := by
  rw [← Subcomplex.range_comp,
    show (𝟙 (stdSimplex.{u}.obj ⦋b⦌)) = stdSimplex.{u}.map (𝟙 ⦋b⦌) from
      (stdSimplex.{u}.map_id _).symm,
    joinStdSimplex_naturality f (𝟙 ⦋b⦌),
    Subcomplex.range_comp, Subcomplex.range_eq_top, Subcomplex.image_top]

/-- Image under `joinStdSimplex` of a standard-simplex range in the right join variable. -/
lemma image_range_joinMap_right (a b b' : ℕ) (g : ⦋b⦌ ⟶ ⦋b'⦌) :
    (Subcomplex.range (joinMap (𝟙 (stdSimplex.{u}.obj ⦋a⦌))
        (stdSimplex.{u}.map g))).image (joinStdSimplex.{u} a b').hom =
      Subcomplex.range
        (stdSimplex.{u}.map (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋a⦌) g)) := by
  rw [← Subcomplex.range_comp,
    show (𝟙 (stdSimplex.{u}.obj ⦋a⦌)) = stdSimplex.{u}.map (𝟙 ⦋a⦌) from
      (stdSimplex.{u}.map_id _).symm,
    joinStdSimplex_naturality (𝟙 ⦋a⦌) g,
    Subcomplex.range_comp, Subcomplex.range_eq_top, Subcomplex.image_top]

/-- `joinMap g (𝟙 K)` is the action of the functor `(- ⋆ K)`. -/
lemma joinMap_id_right {X X' K : SSet.{u}} (g : X ⟶ X') :
    joinMap g (𝟙 K) = (joinFunctor.flip.obj K).map g := by
  unfold joinMap
  change (joinFunctor.map g).app K ≫ (joinFunctor.obj X').map (𝟙 K) =
    (joinFunctor.map g).app K
  simp

/-- `joinMap (-, 𝟙 K)` is functorial in the left argument. -/
lemma joinMap_comp_left {X Y Z K : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    joinMap (f ≫ g) (𝟙 K) = joinMap f (𝟙 K) ≫ joinMap g (𝟙 K) := by
  rw [joinMap_id_right, joinMap_id_right, joinMap_id_right]
  exact Functor.map_comp _ _ _

/-- The multispan shape covering `∂Δ[n+1]` by its facets. -/
abbrev BSpan (n : ℕ) : MultispanShape :=
  MultispanShape.prod (Fin (n + 2))

instance bspan_nonempty (n : ℕ) : Nonempty (WalkingMultispan (BSpan n)) :=
  ⟨WalkingMultispan.right (0 : Fin (n + 2))⟩

instance bspan_connected (n : ℕ) : IsConnected (WalkingMultispan (BSpan n)) := by
  have hright : ∀ i : Fin (n + 2),
      Zigzag (WalkingMultispan.right i : WalkingMultispan (BSpan n))
        (WalkingMultispan.right (0 : Fin (n + 2))) := by
    intro i
    have z1 : Zag (WalkingMultispan.right i : WalkingMultispan (BSpan n))
        (WalkingMultispan.left (i, (0 : Fin (n + 2)))) :=
      Or.inr ⟨@WalkingMultispan.Hom.fst (BSpan n) (i, (0 : Fin (n + 2)))⟩
    have z2 : Zag (WalkingMultispan.left (i, (0 : Fin (n + 2))) :
        WalkingMultispan (BSpan n))
        (WalkingMultispan.right (0 : Fin (n + 2))) :=
      Or.inl ⟨@WalkingMultispan.Hom.snd (BSpan n) (i, (0 : Fin (n + 2)))⟩
    exact (Relation.ReflTransGen.single z1).trans (Relation.ReflTransGen.single z2)
  have zz0 : ∀ x : WalkingMultispan (BSpan n),
      Zigzag x (WalkingMultispan.right (0 : Fin (n + 2))) := by
    intro x
    cases x with
    | left a =>
        have z0 : Zag (WalkingMultispan.left a : WalkingMultispan (BSpan n))
            (WalkingMultispan.right a.1) :=
          Or.inl ⟨@WalkingMultispan.Hom.fst (BSpan n) a⟩
        exact (Relation.ReflTransGen.single z0).trans (hright a.1)
    | right i =>
        exact hright i
  exact zigzag_isConnected (fun j₁ j₂ => (zz0 j₁).trans (zz0 j₂).symm)

instance bspan_flip_pres (n m : ℕ) :
    PreservesColimitsOfShape (WalkingMultispan (BSpan n))
      (joinFunctor.flip.obj (Δ[m] : SSet.{u})) :=
  joinFunctor_flip_preservesConnectedColimits_of_tensorRight _ _

/-- `∂Δ[n+1]` is the supremum of its facets, with facet pairwise intersections. -/
lemma boundaryDiagram (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex)
      (fun i : Fin (n + 2) => stdSimplex.face {i}ᶜ)
      (fun i j => stdSimplex.face {i}ᶜ ⊓ stdSimplex.face {j}ᶜ) where
  iSup_eq := (boundary_eq_iSup (n + 1)).symm
  eq_inf _ _ := rfl

/-- The `i`-th facet leg of the mapped multicofork, composed with `∂Δ`'s
inclusion, is the facet inclusion. -/
lemma boundaryDiagram_legcomp (n : ℕ) (i : Fin (n + 2)) :
    ((boundaryDiagram n).multicofork.map Subcomplex.toSSetFunctor).π i ≫
        (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι =
      (stdSimplex.face {i}ᶜ : (Δ[n + 1] : SSet.{u}).Subcomplex).ι :=
  Subcomplex.homOfLE_ι (face_singleton_compl_le_boundary i)

/-- Range of the facet-join is below range of the corresponding coface-join. -/
lemma range_joinMap_face_le_delta (n m : ℕ) (i : Fin (n + 2)) :
    Subcomplex.range
        (joinMap (stdSimplex.face {i}ᶜ : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
          (𝟙 (Δ[m] : SSet.{u}))) ≤
      Subcomplex.range (joinMap (stdSimplex.δ i) (𝟙 (Δ[m] : SSet.{u}))) := by
  have hfac : (stdSimplex.face {i}ᶜ : (Δ[n + 1] : SSet.{u}).Subcomplex).ι =
      (stdSimplex.faceSingletonComplIso i).inv ≫ stdSimplex.δ i := by
    rw [← boundary.ι_ι i, ← Category.assoc, boundary.faceSingletonComplIso_inv_ι i]
    exact (boundary.faceι_ι i).symm
  rw [hfac, joinMap_comp_left, Subcomplex.range_comp]
  exact Subcomplex.image_le_range _ _

/-- The right facet leg of the F-mapped colimit cocone, composed with
`joinMap ∂Δ.ι 𝟙`, is the corresponding facet-join. -/
lemma boundaryDiagram_rightleg (n m : ℕ) (i : Fin (n + 2)) :
    ((joinFunctor.flip.obj (Δ[m] : SSet.{u})).mapCocone
        ((boundaryDiagram n).multicofork.map Subcomplex.toSSetFunctor)).ι.app
        (WalkingMultispan.right i) ≫
        joinMap (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
          (𝟙 (Δ[m] : SSet.{u})) =
      joinMap (stdSimplex.face {i}ᶜ : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
        (𝟙 (Δ[m] : SSet.{u})) := by
  have key := boundaryDiagram_legcomp n i
  rw [Functor.mapCocone_ι_app, Multicofork.π_eq_app_right, ← joinMap_id_right, ← key,
    joinMap_comp_left]

/-- Boundary-join distribution in the left factor: the range of
`∂Δ[n+1] ⋆ Δ[m]` is the supremum of the ranges of the facet-joins. -/
theorem range_joinMap_boundary_eq_iSup (n m : ℕ) :
    Subcomplex.range (joinMap (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
        (𝟙 (Δ[m] : SSet.{u}))) =
      ⨆ (i : Fin (n + 2)), Subcomplex.range
        (joinMap (stdSimplex.δ i) (𝟙 (Δ[m] : SSet.{u}))) := by
  apply le_antisymm
  · have hcolim := isColimitOfPreserves (joinFunctor.flip.obj (Δ[m] : SSet.{u}))
      (boundaryDiagram n).isColimit
    refine le_trans (le_of_eq (range_eq_iSup_of_isColimit hcolim _)) ?_
    apply iSup_le
    intro j
    cases j with
    | right i =>
        rw [boundaryDiagram_rightleg n m i]
        exact le_trans (range_joinMap_face_le_delta n m i)
          (le_iSup
            (fun i => Subcomplex.range
              (joinMap (stdSimplex.δ i) (𝟙 (Δ[m] : SSet.{u})))) i)
    | left a =>
        have hw := ((joinFunctor.flip.obj (Δ[m] : SSet.{u})).mapCocone
          ((boundaryDiagram n).multicofork.map Subcomplex.toSSetFunctor)).w
            (WalkingMultispan.Hom.fst a)
        rw [← hw, Category.assoc, Subcomplex.range_comp]
        refine le_trans (Subcomplex.image_le_range _ _) ?_
        rw [boundaryDiagram_rightleg n m ((MultispanShape.prod (Fin (n + 2))).fst a)]
        exact le_trans (range_joinMap_face_le_delta n m _)
          (le_iSup
            (fun i => Subcomplex.range
              (joinMap (stdSimplex.δ i) (𝟙 (Δ[m] : SSet.{u})))) _)
  · apply iSup_le
    intro i
    rw [← boundary.ι_ι i, joinMap_comp_left, Subcomplex.range_comp]
    exact Subcomplex.image_le_range _ _

/-- Image form of `range_joinMap_boundary_eq_iSup`, using the standard-simplex
naturality core for each facet. -/
theorem image_range_joinMap_boundary_eq_iSup (n m : ℕ) :
    (Subcomplex.range (joinMap (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
        (𝟙 (Δ[m] : SSet.{u})))).image (joinStdSimplex.{u} (n + 1) m).hom =
      ⨆ (i : Fin (n + 2)), Subcomplex.range (stdSimplex.{u}.map
        (AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ i) (𝟙 ⦋m⦌))) := by
  rw [range_joinMap_boundary_eq_iSup, Subcomplex.image_iSup]
  exact iSup_congr (fun i => image_range_joinMap_left n (n + 1) m (SimplexCategory.δ i))

/-- External product with a fixed left argument. -/
def leftExt (K : AugDay.{u}) : (AC ⥤ Type u) ⥤ (AC × AC ⥤ Type u) :=
  Functor.prod' ((Functor.const _).obj K.functor) (𝟭 _) ⋙
    externalProductBifunctor AC AC (Type u)

/-- Transport of `tensorLeft` across the Day equivalence. -/
def smallLam (K : AugDay.{u}) : (AC ⥤ Type u) ⥤ (AC ⥤ Type u) :=
  (DayFunctor.equiv AC (Type u)).inverse ⋙ tensorLeft K ⋙
    (DayFunctor.equiv AC (Type u)).functor

/-- Whiskering by the augmented-simplex tensor. -/
abbrev RwhiskL : (AC ⥤ Type u) ⥤ (AC × AC ⥤ Type u) :=
  (Functor.whiskeringLeft (AC × AC) AC (Type u)).obj (tensor AC)

/-- The external-product comparison map for the left Day tensor. -/
def thetaL (K : AugDay.{u}) : leftExt K ⟶ smallLam K ⋙ RwhiskL where
  app F := DayFunctor.η K (DayFunctor.mk F)
  naturality {F G} f := by
    apply NatTrans.ext
    funext ab
    obtain ⟨x, y⟩ := ab
    have key :
        (DayFunctor.η K (DayFunctor.mk F)).app (x, y) ≫
            ((K ◁ DayFunctor.Hom.mk f).natTrans).app (x ⊗ y) =
          (K.functor.obj x ◁ f.app y) ≫
            (DayFunctor.η K (DayFunctor.mk G)).app (x, y) :=
      LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        (C := AC) (V := Type u) (D := AugDay) K (DayFunctor.Hom.mk f) x y
    simp only [NatTrans.comp_app, Functor.comp_map, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app]
    exact key.symm

/-- Left Day tensor as the pointwise left Kan extension of fixed-left external product. -/
def thetaBarL (K : AugDay.{u}) :
    leftExt K ⋙ Functor.lan (tensor AC) ⟶ smallLam K :=
  Functor.whiskerRight (thetaL K) (Functor.lan (tensor AC)) ≫
    Functor.whiskerLeft (smallLam K) (Functor.lanAdjunction (tensor AC) (Type u)).counit

instance thetaBarL_app_isIso (K : AugDay.{u}) (F : AC ⥤ Type u) :
    IsIso ((thetaBarL K).app F) := by
  have h3 : (thetaBarL K).app F =
      ((Functor.lanAdjunction (tensor AC) (Type u)).homEquiv ((leftExt K).obj F)
        ((smallLam K).obj F)).symm ((thetaL K).app F) := by
    simp only [thetaBarL, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Adjunction.homEquiv_counit]
  rw [h3]
  refine (Functor.isIso_lanAdjunction_homEquiv_symm_iff
    (L := tensor AC) (G := (smallLam K).obj F) ((thetaL K).app F)).mpr ?_
  exact inferInstanceAs
    ((K ⊗ (DayFunctor.mk F)).functor.IsLeftKanExtension (DayFunctor.η K (DayFunctor.mk F)))

instance thetaBarL_isIso (K : AugDay.{u}) : IsIso (thetaBarL K) :=
  NatIso.isIso_of_isIso_app _

/-- The Kan-extension comparison isomorphism for fixed-left Day tensor. -/
def smallLamIso (K : AugDay.{u}) : leftExt K ⋙ Functor.lan (tensor AC) ≅ smallLam K :=
  asIso (thetaBarL K)

instance leftExt_pres (K : AugDay.{u}) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (leftExt K) := by
  apply preservesColimitsOfShape_of_evaluation
  intro ab
  exact preservesColimitsOfShape_of_natIso
    (NatIso.ofComponents (fun F => Iso.refl _) (by intro F G f; rfl) :
      (evaluation AC (Type u)).obj ab.2 ⋙ tensorLeft (K.functor.obj ab.1) ≅
        leftExt K ⋙ (evaluation (AC × AC) (Type u)).obj ab)

instance smallLam_pres (K : AugDay.{u}) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (smallLam K) :=
  preservesColimitsOfShape_of_natIso (smallLamIso K)

/-- The left Day tensor preserves colimits of any shape preserved by `Type`. -/
instance tensorLeft_pres (K : AugDay.{u}) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (tensorLeft K) := by
  haveI : PreservesColimitsOfShape J
      (tensorLeft K ⋙ (DayFunctor.equiv AC (Type u)).functor) := by
    rw [show tensorLeft K ⋙ (DayFunctor.equiv AC (Type u)).functor =
        (DayFunctor.equiv AC (Type u)).functor ⋙ smallLam K from rfl]
    infer_instance
  exact Limits.preservesColimitsOfShape_of_reflects_of_preserves
    (tensorLeft K) (DayFunctor.equiv AC (Type u)).functor

/-- The functor `(K ⋆ -)` preserves connected colimits when the underlying
left Day tensor does. -/
theorem joinFunctor_obj_preservesConnectedColimits_of_tensorLeft
    (J : Type w) [Category.{w'} J] [IsConnected J] [HasColimitsOfShape J (Type u)]
    (K : SSet.{u})
    [PreservesColimitsOfShape J (tensorLeft (augmentedDay.obj K))] :
    PreservesColimitsOfShape J (joinFunctor.obj K) := by
  change PreservesColimitsOfShape J
    (augmentedDay ⋙ tensorLeft (augmentedDay.obj K) ⋙ restrictAugmentedDay)
  infer_instance

/-- `joinMap (𝟙 K) g` is the action of the functor `(K ⋆ -)`. -/
lemma joinMap_id_left {Y Y' K : SSet.{u}} (g : Y ⟶ Y') :
    joinMap (𝟙 K) g = (joinFunctor.obj K).map g := by
  unfold joinMap
  change (joinFunctor.map (𝟙 K)).app Y ≫ (joinFunctor.obj K).map g =
    (joinFunctor.obj K).map g
  simp

/-- `joinMap (𝟙 K, -)` is functorial in the right argument. -/
lemma joinMap_comp_right {K Y Y' Z : SSet.{u}} (f : Y ⟶ Y') (g : Y' ⟶ Z) :
    joinMap (𝟙 K) (f ≫ g) = joinMap (𝟙 K) f ≫ joinMap (𝟙 K) g := by
  rw [joinMap_id_left, joinMap_id_left, joinMap_id_left]
  exact Functor.map_comp _ _ _

instance bspan_obj_pres (p m : ℕ) :
    PreservesColimitsOfShape (WalkingMultispan (BSpan m))
      (joinFunctor.obj (Δ[p] : SSet.{u})) :=
  joinFunctor_obj_preservesConnectedColimits_of_tensorLeft _ _

/-- Range of a right-factor facet join is below the corresponding right coface join. -/
lemma range_joinMap_face_le_delta_right (p m : ℕ) (j : Fin (m + 2)) :
    Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u}))
        (stdSimplex.face {j}ᶜ : (Δ[m + 1] : SSet.{u}).Subcomplex).ι) ≤
      Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u})) (stdSimplex.δ j)) := by
  have hfac : (stdSimplex.face {j}ᶜ : (Δ[m + 1] : SSet.{u}).Subcomplex).ι =
      (stdSimplex.faceSingletonComplIso j).inv ≫ stdSimplex.δ j := by
    rw [← boundary.ι_ι j, ← Category.assoc, boundary.faceSingletonComplIso_inv_ι j]
    exact (boundary.faceι_ι j).symm
  rw [hfac, joinMap_comp_right, Subcomplex.range_comp]
  exact Subcomplex.image_le_range _ _

/-- The right facet leg of the right-factor boundary colimit, after applying
`Δ[p] ⋆ -`, is the corresponding facet join. -/
lemma boundaryDiagram_rightleg_right (p m : ℕ) (j : Fin (m + 2)) :
    ((joinFunctor.obj (Δ[p] : SSet.{u})).mapCocone
        ((boundaryDiagram m).multicofork.map Subcomplex.toSSetFunctor)).ι.app
        (WalkingMultispan.right j) ≫
        joinMap (𝟙 (Δ[p] : SSet.{u}))
          (∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex).ι =
      joinMap (𝟙 (Δ[p] : SSet.{u}))
        (stdSimplex.face {j}ᶜ : (Δ[m + 1] : SSet.{u}).Subcomplex).ι := by
  have key := boundaryDiagram_legcomp m j
  rw [Functor.mapCocone_ι_app, Multicofork.π_eq_app_right, ← joinMap_id_left, ← key,
    joinMap_comp_right]

/-- Boundary-join distribution in the right factor. -/
theorem range_joinMap_boundary_eq_iSup_right (p m : ℕ) :
    Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u}))
        (∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex).ι) =
      ⨆ (j : Fin (m + 2)), Subcomplex.range
        (joinMap (𝟙 (Δ[p] : SSet.{u})) (stdSimplex.δ j)) := by
  apply le_antisymm
  · have hcolim := isColimitOfPreserves (joinFunctor.obj (Δ[p] : SSet.{u}))
      (boundaryDiagram m).isColimit
    refine le_trans (le_of_eq (range_eq_iSup_of_isColimit hcolim _)) ?_
    apply iSup_le
    intro j
    cases j with
    | right j =>
        rw [boundaryDiagram_rightleg_right p m j]
        exact le_trans (range_joinMap_face_le_delta_right p m j)
          (le_iSup
            (fun j => Subcomplex.range
              (joinMap (𝟙 (Δ[p] : SSet.{u})) (stdSimplex.δ j))) j)
    | left a =>
        have hw := ((joinFunctor.obj (Δ[p] : SSet.{u})).mapCocone
          ((boundaryDiagram m).multicofork.map Subcomplex.toSSetFunctor)).w
            (WalkingMultispan.Hom.fst a)
        rw [← hw, Category.assoc, Subcomplex.range_comp]
        refine le_trans (Subcomplex.image_le_range _ _) ?_
        rw [boundaryDiagram_rightleg_right p m ((MultispanShape.prod (Fin (m + 2))).fst a)]
        exact le_trans (range_joinMap_face_le_delta_right p m _)
          (le_iSup
            (fun j => Subcomplex.range
              (joinMap (𝟙 (Δ[p] : SSet.{u})) (stdSimplex.δ j))) _)
  · apply iSup_le
    intro j
    rw [← boundary.ι_ι j, joinMap_comp_right, Subcomplex.range_comp]
    exact Subcomplex.image_le_range _ _

/-- Image form of the right-factor boundary distribution. -/
theorem image_range_joinMap_boundary_eq_iSup_right (p m : ℕ) :
    (Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u}))
        (∂Δ[m + 1] : (Δ[m + 1] : SSet.{u}).Subcomplex).ι)).image
        (joinStdSimplex.{u} p (m + 1)).hom =
      ⨆ (j : Fin (m + 2)), Subcomplex.range (stdSimplex.{u}.map
        (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋p⦌) (SimplexCategory.δ j))) := by
  rw [range_joinMap_boundary_eq_iSup_right, Subcomplex.image_iSup]
  exact iSup_congr (fun j => image_range_joinMap_right p m (m + 1) (SimplexCategory.δ j))

instance prodMultispan_connected {ι : Type w} [hne : Nonempty ι] :
    IsConnected (WalkingMultispan (MultispanShape.prod ι)) := by
  obtain ⟨i₀⟩ := hne
  have hright : ∀ i : ι,
      Zigzag (WalkingMultispan.right i : WalkingMultispan (MultispanShape.prod ι))
        (WalkingMultispan.right i₀) := by
    intro i
    have z1 : Zag (WalkingMultispan.right i : WalkingMultispan (MultispanShape.prod ι))
        (WalkingMultispan.left (i, i₀)) :=
      Or.inr ⟨@WalkingMultispan.Hom.fst (MultispanShape.prod ι) (i, i₀)⟩
    have z2 : Zag (WalkingMultispan.left (i, i₀) : WalkingMultispan (MultispanShape.prod ι))
        (WalkingMultispan.right i₀) :=
      Or.inl ⟨@WalkingMultispan.Hom.snd (MultispanShape.prod ι) (i, i₀)⟩
    exact (Relation.ReflTransGen.single z1).trans (Relation.ReflTransGen.single z2)
  have zz0 : ∀ x : WalkingMultispan (MultispanShape.prod ι),
      Zigzag x (WalkingMultispan.right i₀) := by
    intro x
    cases x with
    | left a =>
        have z0 : Zag (WalkingMultispan.left a : WalkingMultispan (MultispanShape.prod ι))
            (WalkingMultispan.right a.1) :=
          Or.inl ⟨@WalkingMultispan.Hom.fst (MultispanShape.prod ι) a⟩
        exact (Relation.ReflTransGen.single z0).trans (hright a.1)
    | right i => exact hright i
  haveI : Nonempty (WalkingMultispan (MultispanShape.prod ι)) :=
    ⟨WalkingMultispan.right i₀⟩
  exact zigzag_isConnected (fun j₁ j₂ => (zz0 j₁).trans (zz0 j₂).symm)

instance horn_index_nonempty (M : ℕ) (k : Fin (M + 2)) :
    Nonempty ↑({k}ᶜ : Set (Fin (M + 2))) := by
  obtain ⟨j, hj⟩ := exists_ne k
  exact ⟨⟨j, hj⟩⟩

instance hspan_obj_pres (p M : ℕ) (k : Fin (M + 2)) :
    PreservesColimitsOfShape
      (WalkingMultispan (MultispanShape.prod ↑({k}ᶜ : Set (Fin (M + 2)))))
      (joinFunctor.obj (Δ[p] : SSet.{u})) :=
  joinFunctor_obj_preservesConnectedColimits_of_tensorLeft _ _

/-- The `j`-th horn facet leg composed with horn inclusion is the facet inclusion. -/
lemma horn_legcomp (M : ℕ) (k : Fin (M + 2)) (j : ↑({k}ᶜ : Set (Fin (M + 2)))) :
    ((horn.multicoequalizerDiagram k).multicofork.map Subcomplex.toSSetFunctor).π j ≫
        (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι =
      (stdSimplex.face {j.1}ᶜ : (Δ[M + 1] : SSet.{u}).Subcomplex).ι :=
  Subcomplex.homOfLE_ι (face_le_horn j.1 k j.2)

/-- The `j`-th horn facet leg, after applying `Δ[p] ⋆ -`, is the corresponding
facet join. -/
lemma horn_rightleg (p M : ℕ) (k : Fin (M + 2)) (j : ↑({k}ᶜ : Set (Fin (M + 2)))) :
    ((joinFunctor.obj (Δ[p] : SSet.{u})).mapCocone
        ((horn.multicoequalizerDiagram k).multicofork.map Subcomplex.toSSetFunctor)).ι.app
        (WalkingMultispan.right j) ≫
        joinMap (𝟙 (Δ[p] : SSet.{u})) (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι =
      joinMap (𝟙 (Δ[p] : SSet.{u}))
        (stdSimplex.face {j.1}ᶜ : (Δ[M + 1] : SSet.{u}).Subcomplex).ι := by
  have key := horn_legcomp M k j
  rw [Functor.mapCocone_ι_app, Multicofork.π_eq_app_right, ← joinMap_id_left, ← key,
    joinMap_comp_right]

/-- Horn-join distribution in the right factor. -/
theorem range_joinMap_horn_eq_iSup_right (p M : ℕ) (k : Fin (M + 2)) :
    Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u}))
        (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι) =
      ⨆ (j : ↑({k}ᶜ : Set (Fin (M + 2)))), Subcomplex.range
        (joinMap (𝟙 (Δ[p] : SSet.{u})) (stdSimplex.δ j.1)) := by
  apply le_antisymm
  · have hcolim := isColimitOfPreserves (joinFunctor.obj (Δ[p] : SSet.{u}))
      (horn.multicoequalizerDiagram k).isColimit
    refine le_trans (le_of_eq (range_eq_iSup_of_isColimit hcolim _)) ?_
    apply iSup_le
    intro w
    cases w with
    | right j =>
        rw [horn_rightleg p M k j]
        exact le_trans (range_joinMap_face_le_delta_right p M j.1)
          (le_iSup
            (fun j : ↑({k}ᶜ : Set (Fin (M + 2))) => Subcomplex.range
              (joinMap (𝟙 (Δ[p] : SSet.{u})) (stdSimplex.δ j.1))) j)
    | left a =>
        have hw := ((joinFunctor.obj (Δ[p] : SSet.{u})).mapCocone
          ((horn.multicoequalizerDiagram k).multicofork.map Subcomplex.toSSetFunctor)).w
            (WalkingMultispan.Hom.fst a)
        rw [← hw, Category.assoc, Subcomplex.range_comp]
        refine le_trans (Subcomplex.image_le_range _ _) ?_
        rw [horn_rightleg p M k ((MultispanShape.prod ↑({k}ᶜ : Set (Fin (M + 2)))).fst a)]
        exact le_trans (range_joinMap_face_le_delta_right p M _)
          (le_iSup
            (fun j : ↑({k}ᶜ : Set (Fin (M + 2))) => Subcomplex.range
              (joinMap (𝟙 (Δ[p] : SSet.{u})) (stdSimplex.δ j.1))) _)
  · apply iSup_le
    intro j
    have hne : (j.1 : Fin (M + 2)) ≠ k := j.2
    rw [← horn.ι_ι k j.1 hne, joinMap_comp_right, Subcomplex.range_comp]
    exact Subcomplex.image_le_range _ _

/-- Image form of the right-factor horn distribution. -/
theorem image_range_joinMap_horn_eq_iSup_right (p M : ℕ) (k : Fin (M + 2)) :
    (Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u}))
        (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι)).image
        (joinStdSimplex.{u} p (M + 1)).hom =
      ⨆ (j : ↑({k}ᶜ : Set (Fin (M + 2)))), Subcomplex.range (stdSimplex.{u}.map
        (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋p⦌) (SimplexCategory.δ j.1))) := by
  rw [range_joinMap_horn_eq_iSup_right, Subcomplex.image_iSup]
  exact iSup_congr (fun j => image_range_joinMap_right p M (M + 1) (SimplexCategory.δ j.1))

end

end SSet

open CategoryTheory Simplicial Finset
open AugmentedSimplexCategory

namespace SSet.JoinDecomp

/-! ### Step 1: the cut point of a monotone map into an ordinal -/

/-- A monotone map `f : Fin (n+1) → ℕ` crosses any threshold `A` at a unique cut
position `i`: the preimage of `[0, A)` is the initial segment `[0, i)`. -/
theorem cut_exists {n A : ℕ} (f : Fin (n+1) →o ℕ) :
    ∃ i : ℕ, i ≤ n+1 ∧ ∀ j : Fin (n+1), (f j < A ↔ (j:ℕ) < i) := by
  classical
  set R : Finset (Fin (n+1)) := univ.filter (fun j => A ≤ f j) with hRdef
  by_cases hR : R.Nonempty
  · refine ⟨(R.min' hR : Fin (n+1)).val, by omega, ?_⟩
    intro j
    have hmem : ∀ k : Fin (n+1), k ∈ R ↔ A ≤ f k := by intro k; simp [hRdef]
    constructor
    · intro hj
      by_contra hcon
      simp only [not_lt] at hcon
      have hle : (R.min' hR) ≤ j := by rw [Fin.le_def]; exact hcon
      have : A ≤ f j := le_trans ((hmem _).1 (R.min'_mem hR)) (f.monotone hle)
      omega
    · intro hj
      have hlt : j < R.min' hR := by rw [Fin.lt_def]; exact hj
      have hjnot : j ∉ R := fun hjmem => absurd (R.min'_le j hjmem) (not_le.2 hlt)
      rw [hmem] at hjnot; omega
  · refine ⟨n+1, le_refl _, ?_⟩
    intro j
    rw [Finset.not_nonempty_iff_eq_empty] at hR
    have hjnot : j ∉ R := by rw [hR]; exact Finset.notMem_empty j
    simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hjnot
    exact ⟨fun _ => by omega, fun _ => hjnot⟩

/-! ### Step 2: pointwise evaluation of `tensorHomOf` on the two blocks -/

lemma inl'_comp_tensorHomOf {p q a b : ℕ} (f : ⦋p⦌ ⟶ ⦋a⦌) (g : ⦋q⦌ ⟶ ⦋b⦌) :
    inl' ⦋p⦌ ⦋q⦌ ≫ tensorHomOf f g = f ≫ inl' ⦋a⦌ ⦋b⦌ := by
  ext i : 3
  dsimp [tensorHomOf]
  have e₁ := inl'_eval ⦋p⦌ ⦋q⦌ i
  have e₂ := inl'_eval ⦋a⦌ ⦋b⦌ (f.toOrderHom i)
  simp only [SimplexCategory.len_mk] at e₁ e₂
  rw [e₁, e₂]
  simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
  conv_lhs =>
    change Fin.addCases (fun i ↦ Fin.castAdd (b + 1) (f.toOrderHom i))
      (fun i ↦ Fin.natAdd (a + 1) (g.toOrderHom i)) (Fin.castAdd (q + 1) i)
    rw [Fin.addCases_left]

lemma inr'_comp_tensorHomOf {p q a b : ℕ} (f : ⦋p⦌ ⟶ ⦋a⦌) (g : ⦋q⦌ ⟶ ⦋b⦌) :
    inr' ⦋p⦌ ⦋q⦌ ≫ tensorHomOf f g = g ≫ inr' ⦋a⦌ ⦋b⦌ := by
  ext i : 3
  dsimp [tensorHomOf]
  have e₁ := inr'_eval ⦋p⦌ ⦋q⦌ i
  have e₂ := inr'_eval ⦋a⦌ ⦋b⦌ (g.toOrderHom i)
  simp only [SimplexCategory.len_mk] at e₁ e₂
  rw [e₁, e₂]
  simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
  conv_lhs =>
    change Fin.addCases (fun i ↦ Fin.castAdd (b + 1) (f.toOrderHom i))
      (fun i ↦ Fin.natAdd (a + 1) (g.toOrderHom i)) (Fin.natAdd (p + 1) i)
    rw [Fin.addCases_right]

lemma inl'_tensorHomOf_apply {p q a b : ℕ} (f : ⦋p⦌ ⟶ ⦋a⦌) (g : ⦋q⦌ ⟶ ⦋b⦌) (k : Fin (p+1)) :
    ((tensorHomOf f g).toOrderHom ((inl' ⦋p⦌ ⦋q⦌).toOrderHom k) : ℕ)
      = ((f.toOrderHom k : Fin (a+1)) : ℕ) := by
  have h := congrArg (fun m => (m.toOrderHom k : ℕ)) (inl'_comp_tensorHomOf f g)
  rw [SimplexCategory.comp_toOrderHom] at h
  simp only [OrderHom.comp_coe, Function.comp_apply] at h
  rw [h, SimplexCategory.comp_toOrderHom]
  simp only [OrderHom.comp_coe, Function.comp_apply]
  rw [inl'_eval]; simp

lemma inr'_tensorHomOf_apply {p q a b : ℕ} (f : ⦋p⦌ ⟶ ⦋a⦌) (g : ⦋q⦌ ⟶ ⦋b⦌) (k : Fin (q+1)) :
    ((tensorHomOf f g).toOrderHom ((inr' ⦋p⦌ ⦋q⦌).toOrderHom k) : ℕ)
      = (a+1) + ((g.toOrderHom k : Fin (b+1)) : ℕ) := by
  have h := congrArg (fun m => (m.toOrderHom k : ℕ)) (inr'_comp_tensorHomOf f g)
  rw [SimplexCategory.comp_toOrderHom] at h
  simp only [OrderHom.comp_coe, Function.comp_apply] at h
  rw [h, SimplexCategory.comp_toOrderHom]
  simp only [OrderHom.comp_coe, Function.comp_apply]
  rw [inr'_eval]; simp

/-- `inl'` is left-cancellable (it is injective). -/
lemma inl'_left_cancel {n a b : ℕ} (f g : ⦋n⦌ ⟶ ⦋a⦌)
    (h : f ≫ inl' ⦋a⦌ ⦋b⦌ = g ≫ inl' ⦋a⦌ ⦋b⦌) : f = g := by
  apply SimplexCategory.Hom.ext; apply OrderHom.ext; funext k
  have hk := congrArg (fun m => (m.toOrderHom k : ℕ)) h
  rw [SimplexCategory.comp_toOrderHom, SimplexCategory.comp_toOrderHom] at hk
  simp only [OrderHom.comp_coe, Function.comp_apply] at hk
  rw [inl'_eval, inl'_eval] at hk
  apply Fin.ext; simpa using hk

/-- `inr'` is left-cancellable (it is injective). -/
lemma inr'_left_cancel {n a b : ℕ} (f g : ⦋n⦌ ⟶ ⦋b⦌)
    (h : f ≫ inr' ⦋a⦌ ⦋b⦌ = g ≫ inr' ⦋a⦌ ⦋b⦌) : f = g := by
  apply SimplexCategory.Hom.ext; apply OrderHom.ext; funext k
  have hk := congrArg (fun m => (m.toOrderHom k : ℕ)) h
  rw [SimplexCategory.comp_toOrderHom, SimplexCategory.comp_toOrderHom] at hk
  simp only [OrderHom.comp_coe, Function.comp_apply] at hk
  rw [inr'_eval, inr'_eval] at hk
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd] at hk
  omega

/-- Uniqueness of the block restrictions: `tensorHomOf` is injective in both
arguments. This is the uniqueness half of the maps-into decomposition (it makes
the canonical split a terminal object in its connected component of the comma
category). -/
theorem tensorHomOf_injective {p q a b : ℕ} {ψL ψL' : ⦋p⦌ ⟶ ⦋a⦌} {ψR ψR' : ⦋q⦌ ⟶ ⦋b⦌}
    (h : tensorHomOf ψL ψR = tensorHomOf ψL' ψR') : ψL = ψL' ∧ ψR = ψR' := by
  refine ⟨inl'_left_cancel (b := b) ψL ψL' ?_, inr'_left_cancel (a := a) ψR ψR' ?_⟩
  · rw [← inl'_comp_tensorHomOf, ← inl'_comp_tensorHomOf, h]
  · rw [← inr'_comp_tensorHomOf, ← inr'_comp_tensorHomOf, h]

/-! ### Step 3: the three-way decomposition of a map into `⦋a⦌ ⊗ ⦋b⦌` -/

/-- All-left: a map whose image lies entirely in the left block `⦋a⦌` factors
through `inl'`. -/
theorem fact_left {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌)
    (h : ∀ j, ((φ.toOrderHom j : Fin (a+b+2)) : ℕ) < a+1) :
    ∃ ψ : ⦋n⦌ ⟶ ⦋a⦌, φ = ψ ≫ inl' ⦋a⦌ ⦋b⦌ := by
  refine ⟨SimplexCategory.mkHom ⟨fun j => ⟨(φ.toOrderHom j).val, h j⟩, ?_⟩, ?_⟩
  · intro i j hij; rw [Fin.le_def]; exact φ.toOrderHom.monotone hij
  · apply SimplexCategory.Hom.ext; apply OrderHom.ext; funext j
    rw [SimplexCategory.comp_toOrderHom]
    simp only [OrderHom.comp_coe, Function.comp_apply]
    rw [inl'_eval]; apply Fin.ext; simp

/-- All-right: a map whose image lies entirely in the right block `⦋b⦌` factors
through `inr'`. -/
theorem fact_right {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌)
    (h : ∀ j, ¬ ((φ.toOrderHom j : Fin (a+b+2)) : ℕ) < a+1) :
    ∃ ψ : ⦋n⦌ ⟶ ⦋b⦌, φ = ψ ≫ inr' ⦋a⦌ ⦋b⦌ := by
  refine ⟨SimplexCategory.mkHom ⟨fun j => ⟨(φ.toOrderHom j).val - (a+1), ?_⟩, ?_⟩, ?_⟩
  · have h2 : (φ.toOrderHom j).val < a + b + 2 := (φ.toOrderHom j).isLt; omega
  · intro i j hij
    have hm := φ.toOrderHom.monotone hij; rw [Fin.le_def] at hm
    rw [Fin.le_def]; exact Nat.sub_le_sub_right hm (a+1)
  · apply SimplexCategory.Hom.ext; apply OrderHom.ext; funext j
    rw [SimplexCategory.comp_toOrderHom]
    simp only [OrderHom.comp_coe, Function.comp_apply]
    rw [inr'_eval]; apply Fin.ext
    have hj := h j
    simp only [SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
      Fin.val_natAdd, Fin.val_cast]
    omega

/-- Genuine split: a map that crosses the boundary at cut position `i` (with
`1 ≤ i ≤ n`) factors as the canonical order-iso `⦋n⦌ ≅ ⦋i-1⦌ ⊗ ⦋n-i⦌` followed by
`tensorHomOf ψL ψR`, with `ψL` the left restriction and `ψR` the right restriction. -/
theorem fact_split {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcut : ∀ j : Fin (n+1), ((φ.toOrderHom j : Fin (a+b+2)) : ℕ) < a+1 ↔ (j:ℕ) < i) :
    ∃ (p q : ℕ) (_ : p + q + 1 = n) (ψL : ⦋p⦌ ⟶ ⦋a⦌) (ψR : ⦋q⦌ ⟶ ⦋b⦌),
      φ = eqToHom (show (⦋n⦌ : SimplexCategory) = tensorObjOf ⦋p⦌ ⦋q⦌ from
            by simp only [tensorObjOf, SimplexCategory.len_mk]; congr 1; omega)
            ≫ tensorHomOf ψL ψR := by
  refine ⟨i-1, n-i, by omega, ?_, ?_, ?_⟩
  · refine SimplexCategory.mkHom ⟨fun k => ⟨(φ.toOrderHom (⟨k.val, by have := k.isLt; omega⟩ : Fin (n+1))).val, ?_⟩, ?_⟩
    · have hk : (k : ℕ) < i := by have := k.isLt; omega
      exact (hcut (⟨k.val, by have := k.isLt; omega⟩ : Fin (n+1))).2 hk
    · intro x y hxy
      rw [Fin.le_def]
      exact φ.toOrderHom.monotone (by rw [Fin.le_def] at hxy ⊢; exact hxy)
  · refine SimplexCategory.mkHom ⟨fun k => ⟨(φ.toOrderHom (⟨i + k.val, by have := k.isLt; omega⟩ : Fin (n+1))).val - (a+1), ?_⟩, ?_⟩
    · have h2 : (φ.toOrderHom (⟨i + k.val, by have := k.isLt; omega⟩ : Fin (n+1)) : Fin (a+b+2)).val < a+b+2 :=
        (φ.toOrderHom _).isLt
      omega
    · intro x y hxy
      rw [Fin.le_def] at hxy ⊢
      have hm := φ.toOrderHom.monotone (show (⟨i + x.val, by have := x.isLt; omega⟩ : Fin (n+1)) ≤ ⟨i + y.val, by have := y.isLt; omega⟩ by rw [Fin.le_def]; simp only; omega)
      rw [Fin.le_def] at hm
      exact Nat.sub_le_sub_right hm (a+1)
  · apply SimplexCategory.Hom.ext; apply OrderHom.ext; funext j
    rw [SimplexCategory.comp_toOrderHom]
    simp only [OrderHom.comp_coe, Function.comp_apply]
    rw [SimplexCategory.eqToHom_toOrderHom]
    apply Fin.ext
    set j' : Fin ((i-1) + (n-i) + 1 + 1) :=
      (Fin.castOrderIso (congrArg (fun t => t.len + 1)
        (show (⦋n⦌ : SimplexCategory) = tensorObjOf ⦋(i-1)⦌ ⦋(n-i)⦌ from
          by simp only [tensorObjOf, SimplexCategory.len_mk]; congr 1; omega))).toOrderEmbedding.toOrderHom j with hj'
    have hjval : (j' : ℕ) = (j : ℕ) := by simp [hj']
    by_cases hjlt : (j:ℕ) < i
    · have hkbd : (j:ℕ) < (i-1) + 1 := by omega
      have hjeq : j' = (inl' ⦋(i-1)⦌ ⦋(n-i)⦌).toOrderHom ⟨j.val, hkbd⟩ := by
        apply Fin.ext; rw [inl'_eval]; simp [hjval]
      rw [hjeq, inl'_tensorHomOf_apply]
      simp only [SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
    · have hkbd : (j:ℕ) - i < (n-i) + 1 := by have := j.isLt; omega
      have hjeq : j' = (inr' ⦋(i-1)⦌ ⦋(n-i)⦌).toOrderHom ⟨j.val - i, hkbd⟩ := by
        apply Fin.ext; rw [inr'_eval]
        simp only [Fin.val_cast, Fin.val_natAdd, hjval]
        omega
      rw [hjeq, inr'_tensorHomOf_apply]
      simp only [SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
      have hge : a + 1 ≤ (φ.toOrderHom j : Fin (a+b+2)).val := by
        by_contra hlt; push_neg at hlt
        exact hjlt ((hcut j).1 hlt)
      have hje : (⟨i + (j.val - i), by have := j.isLt; omega⟩ : Fin (n+1)) = j := by
        apply Fin.ext; simp only; omega
      rw [hje]; omega

/-- The full trichotomy: every `φ : ⦋n⦌ ⟶ ⦋a⦌ ⊗ ⦋b⦌` is exactly one of all-left,
all-right, or a genuine split at a cut `1 ≤ i ≤ n`. -/
theorem mapsInto_trichotomy {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌) :
    (∃ ψ : ⦋n⦌ ⟶ ⦋a⦌, φ = ψ ≫ inl' ⦋a⦌ ⦋b⦌) ∨
    (∃ ψ : ⦋n⦌ ⟶ ⦋b⦌, φ = ψ ≫ inr' ⦋a⦌ ⦋b⦌) ∨
    (∃ (p q : ℕ) (_ : p + q + 1 = n) (ψL : ⦋p⦌ ⟶ ⦋a⦌) (ψR : ⦋q⦌ ⟶ ⦋b⦌),
      φ = eqToHom (show (⦋n⦌ : SimplexCategory) = tensorObjOf ⦋p⦌ ⦋q⦌ from
            by simp only [tensorObjOf, SimplexCategory.len_mk]; congr 1; omega)
            ≫ tensorHomOf ψL ψR) := by
  obtain ⟨i, hi, hcut⟩ := cut_exists (A := a+1)
    (f := ⟨fun j => ((φ.toOrderHom j : Fin (a+b+2)) : ℕ), fun x y hxy => by
      have := φ.toOrderHom.monotone hxy; rw [Fin.le_def] at this; exact this⟩)
  rcases Nat.lt_or_ge 0 i with hpos | hzero
  · rcases Nat.lt_or_ge i (n+1) with hilt | hige
    · -- 1 ≤ i ≤ n : genuine split
      right; right
      exact fact_split φ i hpos (by omega) hcut
    · -- i = n+1 : all-left
      left
      apply fact_left
      intro j
      exact (hcut j).2 (by have h := j.isLt; simp only [SimplexCategory.len_mk] at h; omega)
  · -- i = 0 : all-right
    right; left
    apply fact_right
    intro j hlt
    have : (j:ℕ) < i := (hcut j).1 hlt
    omega


/-! ### Deterministic classifier for a genuine map into a tensor -/

variable {X Y : SSet.{u}}

/-- The cut position of a genuine map `φ : ⦋n⦌ ⟶ ⦋a⦌ ⊗ ⦋b⦌`: the number of vertices
landing in the left block. Deterministic (no choice on which trichotomy branch). -/
noncomputable def cutOf {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌) : ℕ :=
  Classical.choose (cut_exists (A := a+1)
    (f := ⟨fun j => ((φ.toOrderHom j : Fin (a+b+2)) : ℕ),
       fun p q hpq => by have := φ.toOrderHom.monotone hpq; rwa [Fin.le_def] at this⟩))

theorem cutOf_spec {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌) :
    cutOf φ ≤ n+1 ∧ ∀ j : Fin (n+1),
      (((φ.toOrderHom j : Fin (a+b+2)) : ℕ) < a+1 ↔ (j:ℕ) < cutOf φ) :=
  Classical.choose_spec (cut_exists (A := a+1)
    (f := ⟨fun j => ((φ.toOrderHom j : Fin (a+b+2)) : ℕ),
       fun p q hpq => by have := φ.toOrderHom.monotone hpq; rwa [Fin.le_def] at this⟩))

/-- The classifier on a genuine `(of ⦋a⦌, of ⦋b⦌)` object: deterministic via `cutOf`. -/
noncomputable def clsOO (n a b : ℕ) (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌)
    (x : X _⦋a⦌) (y : Y _⦋b⦌) : joinObj X Y n :=
  if hi0 : cutOf φ = 0 then
    Sum.inr (Sum.inl (Y.map (Classical.choose (fact_right φ (fun j hlt => by
      have h := ((cutOf_spec φ).2 j).1 hlt; omega))).op y))
  else if hin : cutOf φ = n+1 then
    Sum.inl (X.map (Classical.choose (fact_left φ (fun j => by
      have h := (cutOf_spec φ).2 j
      have hj : (j:ℕ) < n + 1 := j.isLt
      exact h.2 (by omega)))).op x)
  else
    let hs := fact_split φ (cutOf φ) (Nat.one_le_iff_ne_zero.2 hi0)
      (by have := (cutOf_spec φ).1; omega) (cutOf_spec φ).2
    let p := Classical.choose hs
    let hsp := Classical.choose_spec hs
    let q := Classical.choose hsp
    let hsq := Classical.choose_spec hsp
    let hpq := Classical.choose hsq
    let hsL := Classical.choose_spec hsq
    let ψL := Classical.choose hsL
    let hsR := Classical.choose_spec hsL
    let ψR := Classical.choose hsR
    Sum.inr (Sum.inr ⟨⟨(p, q), hpq⟩, (X.map ψL.op x, Y.map ψR.op y)⟩)


open CategoryTheory.MonoidalCategory Opposite Limits

/-- The full object classifier (cocone leg) on a general object of the comma category. -/
noncomputable def cls (n : ℕ)
    (j : CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)))
    (x : (augmentedDay.obj X).functor.obj j.left.1)
    (y : (augmentedDay.obj Y).functor.obj j.left.2) : joinObj X Y n := by
  obtain ⟨⟨A, B⟩, r, φ⟩ := j
  obtain ⟨Au⟩ := A
  obtain ⟨Bu⟩ := B
  cases Au with
  | of A0 =>
    cases Bu with
    | of B0 => exact clsOO n A0.len B0.len (WithInitial.down φ.unop) x y
    | star => exact Sum.inl (X.map (WithInitial.down φ.unop).op x)
  | star =>
    cases Bu with
    | of B0 => exact Sum.inr (Sum.inl (Y.map (WithInitial.down φ.unop).op y))
    | star => exact (WithInitial.false_of_to_star φ.unop).elim


/-! ## Verified additions toward `colimitJoinIso` (RESIDUAL 1 + computational core) -/
open CategoryTheory.MonoidalCategory Opposite Limits

theorem cut_unique {n : ℕ} {P : Fin (n+1) → Prop} {i i' : ℕ}
    (hi : i ≤ n+1) (hi' : i' ≤ n+1)
    (h : ∀ j : Fin (n+1), (P j ↔ (j:ℕ) < i)) (h' : ∀ j : Fin (n+1), (P j ↔ (j:ℕ) < i')) :
    i = i' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exfalso; have hwit : i < n+1 := by omega
    have key : ((⟨i, hwit⟩ : Fin (n+1)) : ℕ) < i ↔ ((⟨i, hwit⟩ : Fin (n+1)) : ℕ) < i' := by
      rw [← h ⟨i, hwit⟩, ← h' ⟨i, hwit⟩]
    simp only [Fin.val_mk] at key; omega
  · exact heq
  · exfalso; have hwit : i' < n+1 := by omega
    have key : ((⟨i', hwit⟩ : Fin (n+1)) : ℕ) < i ↔ ((⟨i', hwit⟩ : Fin (n+1)) : ℕ) < i' := by
      rw [← h ⟨i', hwit⟩, ← h' ⟨i', hwit⟩]
    simp only [Fin.val_mk] at key; omega

theorem cutOf_left {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌) (ψ : ⦋n⦌ ⟶ ⦋a⦌)
    (hψ : φ = ψ ≫ inl' ⦋a⦌ ⦋b⦌) : cutOf φ = n + 1 := by
  have hspec := cutOf_spec φ
  refine cut_unique (n := n) (i := cutOf φ) (i' := n+1) hspec.1 le_rfl hspec.2 (fun j => ?_)
  have hlt : ((φ.toOrderHom j : Fin (a+b+2)) : ℕ) < a + 1 := by
    subst hψ; rw [SimplexCategory.comp_toOrderHom]
    simp only [OrderHom.comp_coe, Function.comp_apply]; rw [inl'_eval]
    simp only [Fin.cast, Fin.coe_castAdd]; exact (ψ.toOrderHom j).isLt
  exact ⟨fun _ => j.isLt, fun _ => hlt⟩

theorem cutOf_right {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌) (ψ : ⦋n⦌ ⟶ ⦋b⦌)
    (hψ : φ = ψ ≫ inr' ⦋a⦌ ⦋b⦌) : cutOf φ = 0 := by
  have hspec := cutOf_spec φ
  refine cut_unique (n := n) (i := cutOf φ) (i' := 0) hspec.1 (by omega) hspec.2 (fun j => ?_)
  have hge : a + 1 ≤ ((φ.toOrderHom j : Fin (a+b+2)) : ℕ) := by
    subst hψ; rw [SimplexCategory.comp_toOrderHom]
    simp only [OrderHom.comp_coe, Function.comp_apply]; rw [inr'_eval]
    simp only [Fin.val_natAdd, Fin.val_cast]; omega
  exact ⟨fun hcon => by omega, fun hcon => absurd hcon (by omega)⟩

theorem cutOf_tensorHomOf {p q a b : ℕ} (ψL : ⦋p⦌ ⟶ ⦋a⦌) (ψR : ⦋q⦌ ⟶ ⦋b⦌) :
    cutOf (tensorHomOf ψL ψR) = p + 1 := by
  have hspec := cutOf_spec (tensorHomOf ψL ψR)
  refine cut_unique (n := p+q+1) (i := cutOf _) (i' := p+1) hspec.1 (by omega) hspec.2 (fun j => ?_)
  by_cases hjp : (j : ℕ) < p + 1
  · have hje : j = (inl' ⦋p⦌ ⦋q⦌).toOrderHom ⟨j.val, by simpa using hjp⟩ := by
      apply Fin.ext; rw [inl'_eval]; simp
    have hval : ((tensorHomOf ψL ψR).toOrderHom j : Fin (a+b+2)).val < a + 1 := by
      rw [hje, inl'_tensorHomOf_apply]; exact (ψL.toOrderHom _).isLt
    exact ⟨fun _ => hjp, fun _ => hval⟩
  · have hjq : (j : ℕ) - (p+1) < q + 1 := by have := j.isLt; omega
    have hje : j = (inr' ⦋p⦌ ⦋q⦌).toOrderHom ⟨j.val - (p+1), hjq⟩ := by
      apply Fin.ext; rw [inr'_eval]; simp only [Fin.val_natAdd, Fin.val_cast]; omega
    have hval : a + 1 ≤ ((tensorHomOf ψL ψR).toOrderHom j : Fin (a+b+2)).val := by
      rw [hje, inr'_tensorHomOf_apply]; omega
    exact ⟨fun hcon => by omega, fun hcon => absurd hcon (by omega)⟩

theorem cutOf_split_form {n p q a b : ℕ} (h : (⦋n⦌ : SimplexCategory) = tensorObjOf ⦋p⦌ ⦋q⦌)
    (ψL : ⦋p⦌ ⟶ ⦋a⦌) (ψR : ⦋q⦌ ⟶ ⦋b⦌) :
    cutOf (eqToHom h ≫ tensorHomOf ψL ψR) = p + 1 := by
  have hn : n = p + q + 1 := by
    have := congrArg SimplexCategory.len h; simpa [tensorObjOf] using this
  subst hn
  rw [show eqToHom h ≫ tensorHomOf ψL ψR = tensorHomOf ψL ψR from by
    rw [Subsingleton.elim h rfl, eqToHom_refl, Category.id_comp]]
  exact cutOf_tensorHomOf ψL ψR

theorem cutOf_id (p q : ℕ) : cutOf (𝟙 (tensorObjOf ⦋p⦌ ⦋q⦌)) = p + 1 := by
  have hspec := cutOf_spec (𝟙 (tensorObjOf ⦋p⦌ ⦋q⦌))
  have hP : ∀ j : Fin (p+q+1+1),
      (((SimplexCategory.Hom.toOrderHom (𝟙 (tensorObjOf ⦋p⦌ ⦋q⦌)) j : Fin (p+q+2))) : ℕ)
        < p+1 ↔ (j:ℕ) < p+1 := by
    intro j; rw [SimplexCategory.id_toOrderHom]; rfl
  exact cut_unique (n := p+q+1) (i := cutOf _) (i' := p+1) hspec.1 (by omega) hspec.2 hP

theorem tensorHomOf_id (p q : ℕ) :
    tensorHomOf (𝟙 ⦋p⦌) (𝟙 ⦋q⦌) = 𝟙 (tensorObjOf ⦋p⦌ ⦋q⦌) :=
  MonoidalCategory.id_tensorHom_id (WithInitial.of ⦋p⦌) (WithInitial.of ⦋q⦌)

/-- RESIDUAL 1 (all-left star case): `tensorHom (inc ψ) (star→of b) = inc (ψ ≫ inl')`. -/
theorem tensorHom_star_left (a b n : ℕ) (ψ : ⦋n⦌ ⟶ ⦋a⦌) :
    MonoidalCategoryStruct.tensorHom (AugmentedSimplexCategory.inclusion.map ψ)
        (WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))
      = AugmentedSimplexCategory.inclusion.map (ψ ≫ AugmentedSimplexCategory.inl' ⦋a⦌ ⦋b⦌) := by
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (x₁ := AugmentedSimplexCategory.inclusion.obj ⦋n⦌) (x₂ := WithInitial.star)
    (y₁ := AugmentedSimplexCategory.inclusion.obj ⦋a⦌)
    (y₂ := AugmentedSimplexCategory.inclusion.obj ⦋b⦌)
    (AugmentedSimplexCategory.inclusion.map ψ)
    (WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋b⦌))
  rw [show AugmentedSimplexCategory.inl (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)
        WithInitial.star = 𝟙 _ from rfl, Category.id_comp] at h
  rw [h]; rfl

/-- RESIDUAL 1 (all-right star case): `tensorHom (star→of a) (inc ψ) = inc (ψ ≫ inr')`. -/
theorem tensorHom_star_right (a b n : ℕ) (ψ : ⦋n⦌ ⟶ ⦋b⦌) :
    MonoidalCategoryStruct.tensorHom
        (WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
        (AugmentedSimplexCategory.inclusion.map ψ)
      = AugmentedSimplexCategory.inclusion.map (ψ ≫ AugmentedSimplexCategory.inr' ⦋a⦌ ⦋b⦌) := by
  have h := AugmentedSimplexCategory.inr_comp_tensorHom
    (x₁ := WithInitial.star) (x₂ := AugmentedSimplexCategory.inclusion.obj ⦋n⦌)
    (y₁ := AugmentedSimplexCategory.inclusion.obj ⦋a⦌)
    (y₂ := AugmentedSimplexCategory.inclusion.obj ⦋b⦌)
    (WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋a⦌))
    (AugmentedSimplexCategory.inclusion.map ψ)
  rw [show AugmentedSimplexCategory.inr WithInitial.star
        (AugmentedSimplexCategory.inclusion.obj ⦋n⦌) = 𝟙 _ from rfl, Category.id_comp] at h
  rw [h]; rfl

variable {X Y : SSet.{u}}

/-- `clsOO` on an all-left factorization computes to the `X`-summand. -/
theorem clsOO_left {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌) (ψ : ⦋n⦌ ⟶ ⦋a⦌)
    (hψ : φ = ψ ≫ inl' ⦋a⦌ ⦋b⦌) (x : X _⦋a⦌) (y : Y _⦋b⦌) :
    clsOO (X := X) (Y := Y) n a b φ x y = Sum.inl (X.map ψ.op x) := by
  have hcut : cutOf φ = n + 1 := cutOf_left φ ψ hψ
  have hH : ∀ j : Fin (n+1), ((φ.toOrderHom j : Fin (a+b+2)) : ℕ) < a + 1 := by
    intro j; have h := (cutOf_spec φ).2 j; exact h.2 (by rw [hcut]; exact j.isLt)
  have key : Classical.choose (fact_left φ hH) = ψ := by
    apply inl'_left_cancel (b := b)
    rw [← Classical.choose_spec (fact_left φ hH)]; exact hψ
  unfold clsOO
  rw [dif_neg (show ¬ cutOf φ = 0 by omega), dif_pos hcut]
  show Sum.inl (X.map (Classical.choose (fact_left φ hH)).op x) = Sum.inl (X.map ψ.op x)
  rw [key]

/-- `clsOO` on an all-right factorization computes to the `Y`-summand. -/
theorem clsOO_right {n a b : ℕ} (φ : ⦋n⦌ ⟶ tensorObjOf ⦋a⦌ ⦋b⦌) (ψ : ⦋n⦌ ⟶ ⦋b⦌)
    (hψ : φ = ψ ≫ inr' ⦋a⦌ ⦋b⦌) (x : X _⦋a⦌) (y : Y _⦋b⦌) :
    clsOO (X := X) (Y := Y) n a b φ x y = Sum.inr (Sum.inl (Y.map ψ.op y)) := by
  have hcut : cutOf φ = 0 := cutOf_right φ ψ hψ
  have hH : ∀ j : Fin (n+1), ¬ ((φ.toOrderHom j : Fin (a+b+2)) : ℕ) < a + 1 := by
    intro j hlt; have h := ((cutOf_spec φ).2 j).1 hlt; omega
  have key : Classical.choose (fact_right φ hH) = ψ := by
    apply inr'_left_cancel (a := a)
    rw [← Classical.choose_spec (fact_right φ hH)]; exact hψ
  unfold clsOO
  rw [dif_pos hcut]
  show Sum.inr (Sum.inl (Y.map (Classical.choose (fact_right φ hH)).op y)) = _
  rw [key]

/-! ### Canonical comma terminals and `cls` reductions on them -/

def tLeft (n : ℕ) :
    CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)) :=
  CostructuredArrow.mk (Y := (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌), op WithInitial.star))
    (𝟙 (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)))

def tRight (n : ℕ) :
    CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)) :=
  CostructuredArrow.mk (Y := (op WithInitial.star, op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)))
    (𝟙 (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)))

def tSplit (p q : ℕ) :
    CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋p + q + 1⦌)) :=
  CostructuredArrow.mk (Y := (op (AugmentedSimplexCategory.inclusion.obj ⦋p⦌),
      op (AugmentedSimplexCategory.inclusion.obj ⦋q⦌)))
    (𝟙 (op (AugmentedSimplexCategory.inclusion.obj ⦋p + q + 1⦌)))

theorem cls_tLeft (n : ℕ) (x : X _⦋n⦌) (y : PUnit.{u+1}) :
    cls (X := X) (Y := Y) n (tLeft n) x y = Sum.inl x := by
  show Sum.inl (X.map (WithInitial.down (𝟙 (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))).unop).op x) = Sum.inl x
  rw [show WithInitial.down (𝟙 (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))).unop = 𝟙 ⦋n⦌ from rfl]
  simp

theorem cls_tRight (n : ℕ) (x : PUnit.{u+1}) (y : Y _⦋n⦌) :
    cls (X := X) (Y := Y) n (tRight n) x y = Sum.inr (Sum.inl y) := by
  show Sum.inr (Sum.inl (Y.map (WithInitial.down (𝟙 (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))).unop).op y)) = _
  rw [show WithInitial.down (𝟙 (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))).unop = 𝟙 ⦋n⦌ from rfl]
  simp


/-- `clsOO` on a genuine `tensorHomOf` computes to the split summand. -/
theorem clsOO_split {a b p q : ℕ} (ψL : ⦋p⦌ ⟶ ⦋a⦌) (ψR : ⦋q⦌ ⟶ ⦋b⦌)
    (x : X _⦋a⦌) (y : Y _⦋b⦌) :
    clsOO (X := X) (Y := Y) (p+q+1) a b (tensorHomOf ψL ψR) x y
      = Sum.inr (Sum.inr ⟨⟨(p, q), rfl⟩, (X.map ψL.op x, Y.map ψR.op y)⟩) := by
  have hcut : cutOf (tensorHomOf ψL ψR) = p + 1 := cutOf_tensorHomOf ψL ψR
  have key : ∀ (P1 Q1 : ℕ) (H1 : P1 + Q1 + 1 = p + q + 1)
      (HE : (⦋p+q+1⦌ : SimplexCategory) = tensorObjOf ⦋P1⦌ ⦋Q1⦌)
      (L1 : ⦋P1⦌ ⟶ ⦋a⦌) (R1 : ⦋Q1⦌ ⟶ ⦋b⦌)
      (_ : tensorHomOf ψL ψR = eqToHom HE ≫ tensorHomOf L1 R1),
      (Sum.inr (Sum.inr ⟨⟨(P1, Q1), H1⟩, (X.map L1.op x, Y.map R1.op y)⟩) : joinObj X Y (p+q+1))
        = Sum.inr (Sum.inr ⟨⟨(p, q), rfl⟩, (X.map ψL.op x, Y.map ψR.op y)⟩) := by
    intro P1 Q1 H1 HE L1 R1 hf
    have hP1 : P1 = p := by
      have hc := cutOf_split_form HE L1 R1
      rw [← hf] at hc; omega
    subst hP1
    have hQ1 : Q1 = q := by omega
    subst hQ1
    rw [show eqToHom HE ≫ tensorHomOf L1 R1 = tensorHomOf L1 R1 from by
      rw [Subsingleton.elim HE rfl, eqToHom_refl, Category.id_comp]] at hf
    obtain ⟨hL, hR⟩ := tensorHomOf_injective hf.symm
    subst hL; subst hR
    rfl
  unfold clsOO
  rw [dif_neg (show ¬ cutOf (tensorHomOf ψL ψR) = 0 by rw [hcut]; omega),
      dif_neg (show ¬ cutOf (tensorHomOf ψL ψR) = (p+q+1)+1 by rw [hcut]; omega)]
  exact key _ _ _ _ _ _
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec
        (fact_split (tensorHomOf ψL ψR) (cutOf (tensorHomOf ψL ψR))
          (by rw [hcut]; omega) (by rw [hcut]; simp only [SimplexCategory.len_mk]; omega)
          (cutOf_spec (tensorHomOf ψL ψR)).2))))))

end SSet.JoinDecomp


namespace SSet.JoinDecomp
open CategoryTheory Simplicial Finset
open AugmentedSimplexCategory
variable {X Y : SSet.{u}}

theorem tensorObjOf_hom_ext {x y z : SimplexCategory} (f g : tensorObjOf x y ⟶ z)
    (h₁ : inl' x y ≫ f = inl' x y ≫ g) (h₂ : inr' x y ≫ f = inr' x y ≫ g) : f = g := by
  ext i
  let j : Fin ((x.len + 1) + (y.len + 1)) := i.cast (Nat.succ_add x.len (y.len + 1)).symm
  have hij : i = j.cast (Nat.succ_add x.len (y.len + 1)) := rfl
  rw [hij]
  cases j using Fin.addCases (m := x.len + 1) (n := y.len + 1) with
  | left j =>
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁
    simpa [← inl'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₁ j
  | right j =>
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₂
    simpa [← inr'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₂ j

lemma tensorHomOf_comp {x₁ y₁ z₁ x₂ y₂ z₂ : SimplexCategory}
    (f₁ : x₁ ⟶ y₁) (g₁ : y₁ ⟶ z₁) (f₂ : x₂ ⟶ y₂) (g₂ : y₂ ⟶ z₂) :
    tensorHomOf f₁ f₂ ≫ tensorHomOf g₁ g₂ = tensorHomOf (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply tensorObjOf_hom_ext
  · rw [← Category.assoc, inl'_comp_tensorHomOf, Category.assoc, inl'_comp_tensorHomOf,
        ← Category.assoc, inl'_comp_tensorHomOf]
  · rw [← Category.assoc, inr'_comp_tensorHomOf, Category.assoc, inr'_comp_tensorHomOf,
        ← Category.assoc, inr'_comp_tensorHomOf]

end SSet.JoinDecomp

namespace SSet.JoinDecomp
open CategoryTheory Simplicial Finset
open AugmentedSimplexCategory
variable {X Y : SSet.{u}}

/-- `tensorHomOf gA gB` preserves left-block membership. -/
lemma tensorHomOf_lt_iff {a0 b0 a0' b0' : ℕ} (gA : ⦋a0'⦌ ⟶ ⦋a0⦌) (gB : ⦋b0'⦌ ⟶ ⦋b0⦌)
    (w : Fin (a0'+b0'+2)) :
    (((tensorHomOf gA gB).toOrderHom w : Fin (a0+b0+2)) : ℕ) < a0+1 ↔ (w:ℕ) < a0'+1 := by
  by_cases hw : (w:ℕ) < a0'+1
  · have hwe : w = (inl' ⦋a0'⦌ ⦋b0'⦌).toOrderHom ⟨w.val, by simpa using hw⟩ := by
      apply Fin.ext; rw [inl'_eval]; simp
    have hval : (((tensorHomOf gA gB).toOrderHom w : Fin (a0+b0+2)) : ℕ) < a0+1 := by
      rw [hwe, inl'_tensorHomOf_apply]; exact (gA.toOrderHom _).isLt
    exact iff_of_true hval hw
  · have hwq : (w:ℕ) - (a0'+1) < b0' + 1 := by have := w.isLt; omega
    have hwe : w = (inr' ⦋a0'⦌ ⦋b0'⦌).toOrderHom ⟨w.val - (a0'+1), hwq⟩ := by
      apply Fin.ext; rw [inr'_eval]; simp only [Fin.val_natAdd, Fin.val_cast]; omega
    have hval : ¬ (((tensorHomOf gA gB).toOrderHom w : Fin (a0+b0+2)) : ℕ) < a0+1 := by
      rw [hwe, inr'_tensorHomOf_apply]; omega
    exact iff_of_false hval hw

lemma cutOf_comp_tensorHomOf {n a0 b0 a0' b0' : ℕ} (φ' : ⦋n⦌ ⟶ tensorObjOf ⦋a0'⦌ ⦋b0'⦌)
    (gA : ⦋a0'⦌ ⟶ ⦋a0⦌) (gB : ⦋b0'⦌ ⟶ ⦋b0⦌) :
    cutOf (φ' ≫ tensorHomOf gA gB) = cutOf φ' := by
  have hspec' := cutOf_spec φ'
  have hspecc := cutOf_spec (φ' ≫ tensorHomOf gA gB)
  refine cut_unique (n := n) (i := cutOf (φ' ≫ tensorHomOf gA gB)) (i' := cutOf φ')
    hspecc.1 hspec'.1 hspecc.2 (fun j => ?_)
  rw [← hspec'.2 j, SimplexCategory.comp_toOrderHom]
  simp only [OrderHom.comp_coe, Function.comp_apply]
  exact tensorHomOf_lt_iff gA gB _

end SSet.JoinDecomp

namespace SSet.JoinDecomp
open CategoryTheory Simplicial Finset
open AugmentedSimplexCategory
variable {X Y : SSet.{u}}

/-- Naturality of the deterministic `(of,of)` classifier under block maps. -/
lemma clsOO_naturality {n a0 b0 a0' b0' : ℕ} (φ' : ⦋n⦌ ⟶ tensorObjOf ⦋a0'⦌ ⦋b0'⦌)
    (gA : ⦋a0'⦌ ⟶ ⦋a0⦌) (gB : ⦋b0'⦌ ⟶ ⦋b0⦌) (x : X _⦋a0⦌) (y : Y _⦋b0⦌) :
    clsOO (X := X) (Y := Y) n a0' b0' φ' (X.map gA.op x) (Y.map gB.op y)
      = clsOO (X := X) (Y := Y) n a0 b0 (φ' ≫ tensorHomOf gA gB) x y := by
  rcases mapsInto_trichotomy φ' with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩ | ⟨p, q, hpq, ψL, ψR, hψ⟩
  · -- all-left
    have hfac : φ' ≫ tensorHomOf gA gB = (ψ ≫ gA) ≫ inl' ⦋a0⦌ ⦋b0⦌ := by
      rw [hψ, Category.assoc, inl'_comp_tensorHomOf, ← Category.assoc]
    rw [clsOO_left φ' ψ hψ (X.map gA.op x) (Y.map gB.op y),
        clsOO_left (φ' ≫ tensorHomOf gA gB) (ψ ≫ gA) hfac x y]
    simp only [op_comp, FunctorToTypes.map_comp_apply]
  · -- all-right
    have hfac : φ' ≫ tensorHomOf gA gB = (ψ ≫ gB) ≫ inr' ⦋a0⦌ ⦋b0⦌ := by
      rw [hψ, Category.assoc, inr'_comp_tensorHomOf, ← Category.assoc]
    rw [clsOO_right φ' ψ hψ (X.map gA.op x) (Y.map gB.op y),
        clsOO_right (φ' ≫ tensorHomOf gA gB) (ψ ≫ gB) hfac x y]
    simp only [op_comp, FunctorToTypes.map_comp_apply]
  · -- split
    subst hpq
    have hsimp : φ' = tensorHomOf ψL ψR := by
      rw [hψ]; simp only [eqToHom_refl, Category.id_comp]
    rw [hsimp, clsOO_split ψL ψR (X.map gA.op x) (Y.map gB.op y),
        tensorHomOf_comp ψL gA ψR gB, clsOO_split (ψL ≫ gA) (ψR ≫ gB) x y]
    simp only [op_comp, FunctorToTypes.map_comp_apply]

end SSet.JoinDecomp

namespace SSet
noncomputable section
open CategoryTheory Simplicial Opposite Limits Function
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.DayFunctor
open AugmentedSimplexCategory
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

/-- The comma-category diagram whose colimit gives the pointwise Day-convolution formula for `(X ⋆ Y)_n`. -/
abbrev joinDiagram (X Y : SSet.{u}) (n : ℕ) :
    CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)) ⥤ Type u :=
  CostructuredArrow.proj (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)) ⋙
    ((augmentedDay.obj X).functor ⊠ (augmentedDay.obj Y).functor)

/-- Compatibility alias for the scratch proof port. This is definitionally equal to `joinDiagram`. -/
abbrev joinDiagram' (X Y : SSet.{u}) (n : ℕ) :
    CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)) ⥤ Type u :=
  joinDiagram X Y n

noncomputable def joinCoconeTypes (X Y : SSet.{u}) (n : ℕ) :
    (joinDiagram' X Y n).CoconeTypes where
  pt := joinObj X Y n
  ι := fun j z => JoinDecomp.cls n j z.1 z.2
  ι_naturality := by
    rintro j j' f
    obtain ⟨⟨A, B⟩, ⟨⟨⟩⟩, φ⟩ := j
    obtain ⟨⟨A', B'⟩, ⟨⟨⟩⟩, φ'⟩ := j'
    obtain ⟨Au⟩ := A; obtain ⟨Bu⟩ := B
    obtain ⟨Au'⟩ := A'; obtain ⟨Bu'⟩ := B'
    funext z; obtain ⟨a, b⟩ := z
    have hw := f.w
    simp only [CostructuredArrow.mk_hom_eq_self, Functor.const_obj_obj, Functor.const_obj_map,
      Category.comp_id] at hw
    cases Au with
    | of A0 => cases Bu with
      | of B0 => cases Au' with
        | of A0' => cases Bu' with
          | of B0' =>
            -- MAIN: (of,of)->(of,of)
            show JoinDecomp.clsOO n A0'.len B0'.len (WithInitial.down φ'.unop)
                (X.map (WithInitial.down f.left.1.unop).op a)
                (Y.map (WithInitial.down f.left.2.unop).op b)
              = JoinDecomp.clsOO n A0.len B0.len (WithInitial.down φ.unop) a b
            have h3 : WithInitial.down φ.unop
                = WithInitial.down φ'.unop ≫ tensorHomOf (WithInitial.down f.left.1.unop)
                    (WithInitial.down f.left.2.unop) := by
              rw [← congrArg (fun m => WithInitial.down (Quiver.Hom.unop m)) hw]; rfl
            rw [h3]
            exact JoinDecomp.clsOO_naturality (WithInitial.down φ'.unop)
              (WithInitial.down f.left.1.unop) (WithInitial.down f.left.2.unop) a b
          | star =>
            -- (of,of)->(of,star): right-block collapse
            show Sum.inl (X.map (WithInitial.down φ'.unop).op
                  (X.map (WithInitial.down f.left.1.unop).op a))
                = JoinDecomp.clsOO n A0.len B0.len (WithInitial.down φ.unop) a b
            have he2 : f.left.2.unop
                = WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋B0.len⦌) :=
              WithInitial.starInitial.hom_ext _ _
            have hkey : WithInitial.down ((tensor AC).map f.left).unop
                = WithInitial.down f.left.1.unop ≫ inl' ⦋A0.len⦌ ⦋B0.len⦌ := by
              have hstar := JoinDecomp.tensorHom_star_left A0.len B0.len A0'.len (WithInitial.down f.left.1.unop)
              have hlhs : ((tensor AC).map f.left).unop
                  = MonoidalCategoryStruct.tensorHom
                      (AugmentedSimplexCategory.inclusion.map (WithInitial.down f.left.1.unop))
                      (WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋B0.len⦌)) := by
                rw [← he2]; rfl
              rw [hlhs, hstar]; rfl
            have h3 : WithInitial.down φ.unop
                = (WithInitial.down φ'.unop ≫ WithInitial.down f.left.1.unop) ≫ inl' ⦋A0.len⦌ ⦋B0.len⦌ := by
              rw [← congrArg (fun m => WithInitial.down (Quiver.Hom.unop m)) hw]
              show WithInitial.down φ'.unop ≫ WithInitial.down ((tensor AC).map f.left).unop = _
              rw [hkey, Category.assoc]
            rw [JoinDecomp.clsOO_left (WithInitial.down φ.unop)
                (WithInitial.down φ'.unop ≫ WithInitial.down f.left.1.unop) h3 a b]
            congr 1
            rw [op_comp]
            exact (FunctorToTypes.map_comp_apply X
              (WithInitial.down f.left.1.unop).op (WithInitial.down φ'.unop).op a).symm
        | star => cases Bu' with
          | of B0' =>
            -- (of,of)->(star,of): left-block collapse
            show Sum.inr (Sum.inl (Y.map (WithInitial.down φ'.unop).op
                  (Y.map (WithInitial.down f.left.2.unop).op b)))
                = JoinDecomp.clsOO n A0.len B0.len (WithInitial.down φ.unop) a b
            have he1 : f.left.1.unop
                = WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋A0.len⦌) :=
              WithInitial.starInitial.hom_ext _ _
            have hkey : WithInitial.down ((tensor AC).map f.left).unop
                = WithInitial.down f.left.2.unop ≫ inr' ⦋A0.len⦌ ⦋B0.len⦌ := by
              have hstar := JoinDecomp.tensorHom_star_right A0.len B0.len B0'.len
                (WithInitial.down f.left.2.unop)
              have hlhs : ((tensor AC).map f.left).unop
                  = MonoidalCategoryStruct.tensorHom
                      (WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋A0.len⦌))
                      (AugmentedSimplexCategory.inclusion.map (WithInitial.down f.left.2.unop)) := by
                rw [← he1]; rfl
              rw [hlhs, hstar]; rfl
            have h3 : WithInitial.down φ.unop
                = (WithInitial.down φ'.unop ≫ WithInitial.down f.left.2.unop) ≫ inr' ⦋A0.len⦌ ⦋B0.len⦌ := by
              rw [← congrArg (fun m => WithInitial.down (Quiver.Hom.unop m)) hw]
              show WithInitial.down φ'.unop ≫ WithInitial.down ((tensor AC).map f.left).unop = _
              rw [hkey, Category.assoc]
            rw [JoinDecomp.clsOO_right (WithInitial.down φ.unop)
                (WithInitial.down φ'.unop ≫ WithInitial.down f.left.2.unop) h3 a b]
            congr 2
            rw [op_comp]
            exact (FunctorToTypes.map_comp_apply Y
              (WithInitial.down f.left.2.unop).op (WithInitial.down φ'.unop).op b).symm
          | star => exact (WithInitial.false_of_to_star φ'.unop).elim
      | star => cases Au' with
        | of A0' => cases Bu' with
          | of B0' => exact (WithInitial.false_of_to_star f.left.2.unop).elim
          | star =>
            -- (of,star)->(of,star)
            show Sum.inl (X.map (WithInitial.down φ'.unop).op
                  (X.map (WithInitial.down f.left.1.unop).op a))
                = Sum.inl (X.map (WithInitial.down φ.unop).op a)
            have h3 : WithInitial.down φ.unop
                = WithInitial.down φ'.unop ≫ WithInitial.down f.left.1.unop := by
              rw [← congrArg (fun m => WithInitial.down (Quiver.Hom.unop m)) hw]; rfl
            rw [h3]; simp only [op_comp, FunctorToTypes.map_comp_apply]
        | star => cases Bu' with
          | of B0' => exact (WithInitial.false_of_to_star f.left.2.unop).elim
          | star => exact (WithInitial.false_of_to_star φ'.unop).elim
    | star => cases Bu with
      | of B0 => cases Au' with
        | of A0' => exact (WithInitial.false_of_to_star f.left.1.unop).elim
        | star => cases Bu' with
          | of B0' =>
            -- (star,of)->(star,of)
            show Sum.inr (Sum.inl (Y.map (WithInitial.down φ'.unop).op
                  (Y.map (WithInitial.down f.left.2.unop).op b)))
                = Sum.inr (Sum.inl (Y.map (WithInitial.down φ.unop).op b))
            have h3 : WithInitial.down φ.unop
                = WithInitial.down φ'.unop ≫ WithInitial.down f.left.2.unop := by
              rw [← congrArg (fun m => WithInitial.down (Quiver.Hom.unop m)) hw]; rfl
            rw [h3]; simp only [op_comp, FunctorToTypes.map_comp_apply]
          | star => exact (WithInitial.false_of_to_star φ'.unop).elim
      | star => exact (WithInitial.false_of_to_star φ.unop).elim

end
end SSet


namespace SSet
noncomputable section
open CategoryTheory Simplicial Opposite Limits Function
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.DayFunctor
open AugmentedSimplexCategory
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

/-- The canonical split comma object over `⦋n⦌` for a split index `p+q+1=n`. -/
def jSplitN (n p q : ℕ) (h : p + q + 1 = n) :
    CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)) :=
  CostructuredArrow.mk (Y := (op (AugmentedSimplexCategory.inclusion.obj ⦋p⦌),
      op (AugmentedSimplexCategory.inclusion.obj ⦋q⦌)))
    (eqToHom (by subst h; rfl) :
      (tensor AC).obj (op (AugmentedSimplexCategory.inclusion.obj ⦋p⦌),
        op (AugmentedSimplexCategory.inclusion.obj ⦋q⦌)) ⟶ op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))

/-- Canonical colimit representative of each summand. -/
def rep (X Y : SSet.{u}) (n : ℕ) : joinObj X Y n → (joinDiagram' X Y n).ColimitType
  | Sum.inl x => (joinDiagram' X Y n).ιColimitType (JoinDecomp.tLeft n) (x, PUnit.unit)
  | Sum.inr (Sum.inl y) => (joinDiagram' X Y n).ιColimitType (JoinDecomp.tRight n) (PUnit.unit, y)
  | Sum.inr (Sum.inr ⟨⟨(p, q), h⟩, (x, y)⟩) =>
      (joinDiagram' X Y n).ιColimitType (jSplitN n p q h) (x, y)

/-- Right inverse: `descColimitType c ∘ rep = id`. -/
theorem desc_rep (X Y : SSet.{u}) (n : ℕ) (z : joinObj X Y n) :
    (joinDiagram' X Y n).descColimitType (joinCoconeTypes X Y n) (rep X Y n z) = z := by
  rcases z with x | y | ⟨⟨⟨p, q⟩, h⟩, x, y⟩
  · show JoinDecomp.cls n (JoinDecomp.tLeft n) x PUnit.unit = Sum.inl x
    exact JoinDecomp.cls_tLeft n x PUnit.unit
  · show JoinDecomp.cls n (JoinDecomp.tRight n) PUnit.unit y = Sum.inr (Sum.inl y)
    exact JoinDecomp.cls_tRight n PUnit.unit y
  · subst h
    show JoinDecomp.cls (p+q+1) (jSplitN (p+q+1) p q rfl) x y
      = Sum.inr (Sum.inr ⟨⟨(p, q), rfl⟩, (x, y)⟩)
    rw [show JoinDecomp.cls (p+q+1) (jSplitN (p+q+1) p q rfl) x y
          = JoinDecomp.clsOO (p+q+1) p q (𝟙 (tensorObjOf ⦋p⦌ ⦋q⦌)) x y from rfl,
        ← JoinDecomp.tensorHomOf_id p q, JoinDecomp.clsOO_split]
    simp

end
end SSet

namespace SSet
noncomputable section
open CategoryTheory Simplicial Opposite Limits Function
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.DayFunctor
open AugmentedSimplexCategory
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

theorem keyred (X Y : SSet.{u}) (n : ℕ)
    (j : CostructuredArrow (tensor AC) (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)))
    (x : (augmentedDay.obj X).functor.obj j.left.1)
    (y : (augmentedDay.obj Y).functor.obj j.left.2) :
    rep X Y n (JoinDecomp.cls n j x y) = (joinDiagram' X Y n).ιColimitType j (x, y) := by
  obtain ⟨⟨A, B⟩, ⟨⟨⟩⟩, φ⟩ := j
  obtain ⟨Au⟩ := A; obtain ⟨Bu⟩ := B
  cases Au with
  | of A0 => cases Bu with
    | of B0 =>
      show rep X Y n (JoinDecomp.clsOO n A0.len B0.len (WithInitial.down φ.unop) x y)
        = (joinDiagram' X Y n).ιColimitType
            (CostructuredArrow.mk (Y := (op (WithInitial.of A0), op (WithInitial.of B0))) φ) (x, y)
      rcases JoinDecomp.mapsInto_trichotomy (WithInitial.down φ.unop) with
        ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩ | ⟨p, q, hpq, ψL, ψR, hψ⟩
      · -- all-left → tLeft
        rw [JoinDecomp.clsOO_left (WithInitial.down φ.unop) ψ hψ x y]
        let hpair : (op (WithInitial.of A0), op (WithInitial.of B0))
            ⟶ (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌), op WithInitial.star) :=
          ((AugmentedSimplexCategory.inclusion.map ψ).op,
           (WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋B0.len⦌)).op)
        let g : (CostructuredArrow.mk (Y := (op (WithInitial.of A0), op (WithInitial.of B0))) φ)
            ⟶ JoinDecomp.tLeft n :=
          CostructuredArrow.homMk hpair (by
            apply Quiver.Hom.unop_inj
            show (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))
                ≫ MonoidalCategoryStruct.tensorHom (AugmentedSimplexCategory.inclusion.map ψ)
                    (WithInitial.starInitial.to
                      (AugmentedSimplexCategory.inclusion.obj ⦋B0.len⦌)) = φ.unop
            rw [Category.id_comp, JoinDecomp.tensorHom_star_left A0.len B0.len n ψ, ← hψ]
            rfl)
        rw [← (joinDiagram' X Y n).ιColimitType_map g (x, y)]
        exact rfl
      · -- all-right → tRight
        rw [JoinDecomp.clsOO_right (WithInitial.down φ.unop) ψ hψ x y]
        let hpair : (op (WithInitial.of A0), op (WithInitial.of B0))
            ⟶ (op WithInitial.star, op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌)) :=
          ((WithInitial.starInitial.to (AugmentedSimplexCategory.inclusion.obj ⦋A0.len⦌)).op,
           (AugmentedSimplexCategory.inclusion.map ψ).op)
        let g : (CostructuredArrow.mk (Y := (op (WithInitial.of A0), op (WithInitial.of B0))) φ)
            ⟶ JoinDecomp.tRight n :=
          CostructuredArrow.homMk hpair (by
            apply Quiver.Hom.unop_inj
            show (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))
                ≫ MonoidalCategoryStruct.tensorHom
                    (WithInitial.starInitial.to
                      (AugmentedSimplexCategory.inclusion.obj ⦋A0.len⦌))
                    (AugmentedSimplexCategory.inclusion.map ψ) = φ.unop
            rw [Category.id_comp, JoinDecomp.tensorHom_star_right A0.len B0.len n ψ, ← hψ]
            rfl)
        rw [← (joinDiagram' X Y n).ιColimitType_map g (x, y)]
        exact rfl
      · -- split → jSplitN
        subst hpq
        have hψ' : WithInitial.down φ.unop = tensorHomOf ψL ψR := hψ
        rw [hψ', JoinDecomp.clsOO_split ψL ψR x y]
        let hpair : (op (WithInitial.of A0), op (WithInitial.of B0))
            ⟶ (op (AugmentedSimplexCategory.inclusion.obj ⦋p⦌),
                op (AugmentedSimplexCategory.inclusion.obj ⦋q⦌)) :=
          ((AugmentedSimplexCategory.inclusion.map ψL).op,
           (AugmentedSimplexCategory.inclusion.map ψR).op)
        let g : (CostructuredArrow.mk (Y := (op (WithInitial.of A0), op (WithInitial.of B0))) φ)
            ⟶ jSplitN (p + q + 1) p q rfl :=
          CostructuredArrow.homMk hpair (by
            apply Quiver.Hom.unop_inj
            show (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋p + q + 1⦌))
                ≫ MonoidalCategoryStruct.tensorHom (AugmentedSimplexCategory.inclusion.map ψL)
                    (AugmentedSimplexCategory.inclusion.map ψR) = φ.unop
            rw [Category.id_comp]
            show AugmentedSimplexCategory.inclusion.map (tensorHomOf ψL ψR) = φ.unop
            rw [← hψ']
            rfl)
        rw [← (joinDiagram' X Y (p + q + 1)).ιColimitType_map g (x, y)]
        exact rfl
    | star =>
      let g : (CostructuredArrow.mk (Y := (op (WithInitial.of A0), op WithInitial.star)) φ)
          ⟶ JoinDecomp.tLeft n :=
        CostructuredArrow.homMk (φ, 𝟙 (op WithInitial.star)) (by
          simp only [JoinDecomp.tLeft, CostructuredArrow.mk_hom_eq_self, Category.comp_id,
            MonoidalCategory.tensorHom_id]
          exact MonoidalCategory.whiskerRight_id φ ▸ rfl)
      show rep X Y n (JoinDecomp.cls n (CostructuredArrow.mk
          (Y := (op (WithInitial.of A0), op WithInitial.star)) φ) x y)
        = (joinDiagram' X Y n).ιColimitType (CostructuredArrow.mk
          (Y := (op (WithInitial.of A0), op WithInitial.star)) φ) (x, y)
      rw [← (joinDiagram' X Y n).ιColimitType_map g (x, y)]
      exact rfl
  | star => cases Bu with
    | of B0 =>
      let g : (CostructuredArrow.mk (Y := (op WithInitial.star, op (WithInitial.of B0))) φ)
          ⟶ JoinDecomp.tRight n :=
        CostructuredArrow.homMk (𝟙 (op WithInitial.star), φ) (by
          simp only [JoinDecomp.tRight, CostructuredArrow.mk_hom_eq_self, Category.comp_id,
            MonoidalCategory.id_tensorHom]
          exact MonoidalCategory.id_whiskerLeft φ ▸ rfl)
      show rep X Y n (JoinDecomp.cls n (CostructuredArrow.mk
          (Y := (op WithInitial.star, op (WithInitial.of B0))) φ) x y)
        = (joinDiagram' X Y n).ιColimitType (CostructuredArrow.mk
          (Y := (op WithInitial.star, op (WithInitial.of B0))) φ) (x, y)
      rw [← (joinDiagram' X Y n).ιColimitType_map g (x, y)]
      exact rfl
    | star => exact (WithInitial.false_of_to_star φ.unop).elim

end
end SSet

namespace SSet
noncomputable section
open CategoryTheory Simplicial Opposite Limits Function
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.DayFunctor
open AugmentedSimplexCategory
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

/-- The classifier cocone is a colimit: `descColimitType` is bijective. -/
theorem joinIsColimit (X Y : SSet.{u}) (n : ℕ) :
    (joinCoconeTypes X Y n).IsColimit := by
  refine ⟨fun a b hab => ?_, fun z => ⟨rep X Y n z, desc_rep X Y n z⟩⟩
  obtain ⟨ja, xa, rfl⟩ := (joinDiagram' X Y n).ιColimitType_jointly_surjective a
  obtain ⟨jb, xb, rfl⟩ := (joinDiagram' X Y n).ιColimitType_jointly_surjective b
  have ha : (joinDiagram' X Y n).ιColimitType ja xa = rep X Y n (JoinDecomp.cls n ja xa.1 xa.2) :=
    (keyred X Y n ja xa.1 xa.2).symm
  have hb : (joinDiagram' X Y n).ιColimitType jb xb = rep X Y n (JoinDecomp.cls n jb xb.1 xb.2) :=
    (keyred X Y n jb xb.1 xb.2).symm
  rw [ha, hb]
  exact congrArg (rep X Y n) hab

/-- **The pointwise join formula colimit**: `colimit (joinDiagram' X Y n) ≅ joinObj X Y n`. -/
def colimitJoinIso (X Y : SSet.{u}) (n : ℕ) :
    colimit (joinDiagram' X Y n) ≅ joinObj X Y n :=
  (colimit.isColimit (joinDiagram' X Y n)).coconePointUniqueUpToIso
    (((joinCoconeTypes X Y n).isColimit_iff).1 (joinIsColimit X Y n)).some

end
end SSet

namespace SSet

noncomputable section

open CategoryTheory Simplicial Opposite Limits Function
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.DayFunctor
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

/-- The pointwise left-Kan-extension colimit presentation of `(X ⋆ Y)_n`. -/
def joinObjColimitIso (X Y : SSet.{u}) (n : ℕ) :
    (X ⋆ Y) _⦋n⦌ ≅ colimit (joinDiagram X Y n) :=
  (isoPointwiseLeftKanExtension (augmentedDay.obj X) (augmentedDay.obj Y)).app
    (op (AugmentedSimplexCategory.inclusion.obj ⦋n⦌))

/-- Pointwise description of the simplicial join. -/
def joinObjEquiv (X Y : SSet.{u}) (n : ℕ) :
    (X ⋆ Y) _⦋n⦌ ≃ joinObj X Y n :=
  (joinObjColimitIso X Y n ≪≫ colimitJoinIso X Y n).toEquiv

variable {X X' Y Y' : SSet.{u}}

/-- The explicit summand-wise map on the pointwise join formula. -/
def joinObjMap (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    joinObj X Y n → joinObj X' Y' n :=
  Sum.map (f.app (op ⦋n⦌))
    (Sum.map (g.app (op ⦋n⦌))
      (Sigma.map id (fun p => Prod.map (f.app (op ⦋p.1.1⦌)) (g.app (op ⦋p.1.2⦌)))))

/-- The summand-wise join map is injective when both component maps are levelwise injective. -/
theorem joinObjMap_injective (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (hf : ∀ m, Function.Injective (f.app (op ⦋m⦌)))
    (hg : ∀ m, Function.Injective (g.app (op ⦋m⦌))) :
    Function.Injective (joinObjMap f g n) :=
  (hf n).sumMap ((hg n).sumMap
    (Function.injective_id.sigma_map (fun p => (hf p.1.1).prodMap (hg p.1.2))))

/-- Reduction of `join_mono` to compatibility of the pointwise equivalence with `joinMap`. -/
theorem join_mono_of_joinObjEquiv
    (E : ∀ (X Y : SSet.{u}) (n : ℕ), (X ⋆ Y) _⦋n⦌ ≃ joinObj X Y n)
    (hcompat : ∀ {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
        (z : joinObj X Y n),
        E X' Y' n ((joinMap f g).app (op ⦋n⦌) ((E X Y n).symm z)) = joinObjMap f g n z)
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : Mono f) (hg : Mono g) :
    Mono (joinMap f g) := by
  have hfm : ∀ m, Function.Injective (f.app (op ⦋m⦌)) := fun m =>
    (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app (f := f)).mp hf (op ⦋m⦌))
  have hgm : ∀ m, Function.Injective (g.app (op ⦋m⦌)) := fun m =>
    (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app (f := g)).mp hg (op ⦋m⦌))
  rw [NatTrans.mono_iff_mono_app (f := joinMap f g)]
  intro k
  have hk : k = op ⦋k.unop.len⦌ := by rw [SimplexCategory.mk_len]
  rw [hk, mono_iff_injective]
  set n := k.unop.len
  intro w₁ w₂ hw
  apply (E X Y n).injective
  apply joinObjMap_injective f g n hfm hgm
  rw [← hcompat f g n ((E X Y n) w₁), ← hcompat f g n ((E X Y n) w₂),
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, hw]

/-- Adhesive reduction for the Leibniz join: if the naturality square is a pullback and
the two target-side join maps are monos, then the Leibniz join is mono. -/
theorem leibnizJoin_mono_of_pullback {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    [Mono (joinMap (𝟙 B) g)] [Mono (joinMap f (𝟙 D))]
    (hpb : IsPullback (joinMap f (𝟙 C)) (joinMap (𝟙 A) g)
        (joinMap (𝟙 B) g) (joinMap f (𝟙 D))) :
    Mono (leibnizJoin f g) := by
  have hm : Mono (pushout.desc (joinMap (𝟙 B) g) (joinMap f (𝟙 D)) pullback.condition) :=
    inferInstance
  have e₁ : joinMap f (𝟙 C) ≫ (𝟙 (B ⋆ C)) =
      hpb.isoPullback.hom ≫ pullback.fst (joinMap (𝟙 B) g) (joinMap f (𝟙 D)) := by
    rw [Category.comp_id]; exact hpb.isoPullback_hom_fst.symm
  have e₂ : joinMap (𝟙 A) g ≫ (𝟙 (A ⋆ D)) =
      hpb.isoPullback.hom ≫ pullback.snd (joinMap (𝟙 B) g) (joinMap f (𝟙 D)) := by
    rw [Category.comp_id]; exact hpb.isoPullback_hom_snd.symm
  have hΦiso : IsIso (pushout.map (joinMap f (𝟙 C)) (joinMap (𝟙 A) g)
      (pullback.fst (joinMap (𝟙 B) g) (joinMap f (𝟙 D)))
      (pullback.snd (joinMap (𝟙 B) g) (joinMap f (𝟙 D)))
      (𝟙 (B ⋆ C)) (𝟙 (A ⋆ D)) hpb.isoPullback.hom e₁ e₂) :=
    pushout.map_isIso _ _ _ _ _ _ _ e₁ e₂
  have hfac : leibnizJoin f g =
      (pushout.map (joinMap f (𝟙 C)) (joinMap (𝟙 A) g)
        (pullback.fst (joinMap (𝟙 B) g) (joinMap f (𝟙 D)))
        (pullback.snd (joinMap (𝟙 B) g) (joinMap f (𝟙 D)))
        (𝟙 (B ⋆ C)) (𝟙 (A ⋆ D)) hpb.isoPullback.hom e₁ e₂) ≫
      pushout.desc (joinMap (𝟙 B) g) (joinMap f (𝟙 D)) pullback.condition := by
    apply pushout.hom_ext <;>
      simp only [leibnizJoin, pushout.map, pushout.inl_desc, pushout.inr_desc,
        pushout.inl_desc_assoc, pushout.inr_desc_assoc, Category.id_comp]
  rw [hfac]
  exact mono_comp _ _

end

end SSet
