/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Slices of simplicial sets via the join

This file starts the join-slice adjunction API.  The join functor is valued in
the coslice `Under K` using the right-factor inclusion `K ⟶ Y ⋆ K`; this is the
relative setting where the empty-colimit obstruction for the plain functor
`Y ↦ Y ⋆ K` disappears.
-/

open CategoryTheory Simplicial Opposite Limits
open CategoryTheory.MonoidalCategory
open scoped Simplicial

universe u w w'

namespace SSet

noncomputable section

/-- The plain fixed-right join functor does not preserve the empty colimit. -/
theorem joinFlip_not_preservesInitial :
    ¬ PreservesColimitsOfShape (Discrete PEmpty.{1})
        (joinFunctor.flip.obj (Δ[0] : SSet.{u})) := by
  intro h
  haveI : PreservesColimit (Functor.empty.{0} SSet.{u})
      (joinFunctor.flip.obj (Δ[0] : SSet.{u})) := by
    exact PreservesColimitsOfShape.preservesColimit
  let bad : Δ[0] ⟶ (⊥_ SSet.{u}) :=
    joinInr (⊥_ SSet.{u}) (Δ[0] : SSet.{u}) ≫
      (PreservesInitial.iso (joinFunctor.flip.obj (Δ[0] : SSet.{u}))).hom
  let x := (bad.app (op ⦋0⦌)) (yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  have hInitial : IsInitial ((⊥_ SSet.{u}) _⦋0⦌) := by
    haveI : PreservesColimit (Functor.empty.{0} SSet.{u})
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) :=
      inferInstance
    exact initialIsInitial.isInitialObj
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) (⊥_ SSet.{u})
  haveI : IsEmpty ((⊥_ SSet.{u}) _⦋0⦌) :=
    (Types.initial_iff_empty ((⊥_ SSet.{u}) _⦋0⦌)).mp ⟨hInitial⟩
  exact IsEmpty.false x

/-- The fixed-right join functor lifted to the coslice under the right factor. -/
def joinUnder (K : SSet.{u}) : SSet.{u} ⥤ Under K where
  obj Y := Under.mk (joinInr Y K)
  map {Y Y'} f := Under.homMk ((joinFunctor.map f).app K) (joinInr_naturality_left f K)
  map_id Y := by
    apply Under.UnderMorphism.ext
    show (joinFunctor.map (𝟙 Y)).app K = 𝟙 _
    rw [joinFunctor.map_id]
    rfl
  map_comp {Y Y' Y''} f g := by
    apply Under.UnderMorphism.ext
    show (joinFunctor.map (f ≫ g)).app K =
      (joinFunctor.map f).app K ≫ (joinFunctor.map g).app K
    rw [joinFunctor.map_comp]
    rfl

@[simp]
theorem joinUnder_forget (K : SSet.{u}) :
    joinUnder K ⋙ Under.forget K = joinFunctor.flip.obj K :=
  rfl

theorem joinUnder_preservesConnectedColimits_of_joinFunctor_flip
    (J : Type w) [Category.{w'} J] [IsConnected J] (K : SSet.{u})
    [PreservesColimitsOfShape J (joinFunctor.flip.obj K)] :
    PreservesColimitsOfShape J (joinUnder K) := by
  haveI : PreservesColimitsOfShape J (joinUnder K ⋙ Under.forget K) := by
    change PreservesColimitsOfShape J (joinFunctor.flip.obj K)
    infer_instance
  exact Limits.preservesColimitsOfShape_of_reflects_of_preserves (joinUnder K) (Under.forget K)

theorem joinUnder_preservesConnectedColimits_of_tensorRight
    (J : Type w) [Category.{w'} J] [IsConnected J] [HasColimitsOfShape J (Type u)]
    (K : SSet.{u})
    [PreservesColimitsOfShape J (tensorRight (augmentedDay.obj K))] :
    PreservesColimitsOfShape J (joinUnder K) := by
  haveI : PreservesColimitsOfShape J (joinFunctor.flip.obj K) :=
    joinFunctor_flip_preservesConnectedColimits_of_tensorRight J K
  exact joinUnder_preservesConnectedColimits_of_joinFunctor_flip J K

instance joinInr_initial_isIso (K : SSet.{u}) : IsIso (joinInr (⊥_ SSet.{u}) K) := by
  unfold joinInr
  apply Functor.map_isIso

def joinBotIso (K : SSet.{u}) : (⊥_ SSet.{u}) ⋆ K ≅ K :=
  (asIso (joinInr (⊥_ SSet.{u}) K)).symm

def joinUnderBotIsoInitial (K : SSet.{u}) : (joinUnder K).obj (⊥_ SSet.{u}) ≅ Under.mk (𝟙 K) :=
  Under.isoMk (asIso (joinInr (⊥_ SSet.{u}) K)).symm (by
    show joinInr (⊥_ SSet.{u}) K ≫ inv (joinInr (⊥_ SSet.{u}) K) = 𝟙 K
    simp)

def joinUnderBotIsInitial (K : SSet.{u}) : IsInitial ((joinUnder K).obj (⊥_ SSet.{u})) :=
  IsInitial.ofIso Under.mkIdInitial (joinUnderBotIsoInitial K).symm

instance joinUnder_preservesInitial (K : SSet.{u}) :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (joinUnder K) := by
  haveI : HasInitial (Under K) := (Under.mkIdInitial (X := K)).hasInitial
  haveI : PreservesColimit (Functor.empty.{0} SSet.{u}) (joinUnder K) :=
    preservesInitial_of_iso (joinUnder K)
      ((initialIsInitial (C := Under K)).uniqueUpToIso (joinUnderBotIsInitial K))
  exact preservesColimitsOfShape_pempty_of_preservesInitial _

instance joinUnder_preservesCoequalizers (K : SSet.{u}) :
    PreservesColimitsOfShape WalkingParallelPair (joinUnder K) := by
  exact joinUnder_preservesConnectedColimits_of_tensorRight WalkingParallelPair K

theorem joinUnder_preservesColimitsOfSize_of_preservesCoproducts (K : SSet.{u})
    [∀ (J : Type u), PreservesColimitsOfShape (Discrete J) (joinUnder K)] :
    PreservesColimitsOfSize.{u, u} (joinUnder K) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts (joinUnder K)

theorem joinUnder_preservesColimitsOfShape_of_preservesCoproducts (K : SSet.{u})
    [∀ (I : Type u), PreservesColimitsOfShape (Discrete I) (joinUnder K)]
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (joinUnder K) := by
  haveI : PreservesColimitsOfSize.{u, u} (joinUnder K) :=
    joinUnder_preservesColimitsOfSize_of_preservesCoproducts K
  infer_instance

/-- The equivalence inverse sending a simplicial set to the unique arrow out of the initial
simplicial set. -/
abbrev underInitial : SSet.{u} ⥤ Under (⊥_ SSet.{u}) :=
  (Under.equivalenceOfIsInitial (X := (⊥_ SSet.{u})) initialIsInitial).inverse

/-- A factorization of `joinUnder K` through `Under ⊥` and postcomposition by `(- ⋆ K)`. -/
def joinUnderFactor (K : SSet.{u}) : SSet.{u} ⥤ Under K :=
  underInitial ⋙ Under.post (X := (⊥_ SSet.{u})) (joinFunctor.flip.obj K) ⋙
    Under.map (joinBotIso K).inv

/-- The factorization through `Under ⊥` agrees with the direct definition of `joinUnder`. -/
def joinUnderFactorIso (K : SSet.{u}) : joinUnderFactor K ≅ joinUnder K :=
  NatIso.ofComponents
    (fun Y => Under.isoMk (Iso.refl _) (by
      change (joinBotIso K).inv ≫ (joinFunctor.map (initial.to Y)).app K = joinInr Y K
      rw [show (joinBotIso K).inv = joinInr (⊥_ SSet.{u}) K from rfl]
      rw [joinInr_naturality_left]))
    (by
      intro Y Y' f
      ext n x
      rfl)

theorem joinUnder_preservesColimitsOfShape (K : SSet.{u})
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape (WithInitial J) (Type u)] :
    PreservesColimitsOfShape J (joinUnder K) := by
  haveI : PreservesColimitsOfShape J (underInitial : SSet.{u} ⥤ Under (⊥_ SSet.{u})) :=
    by
      let h := (Under.equivalenceOfIsInitial (X := (⊥_ SSet.{u})) initialIsInitial).symm.toAdjunction.leftAdjoint_preservesColimits
      exact h.preservesColimitsOfShape
  haveI : PreservesColimitsOfShape (WithInitial J) (joinFunctor.flip.obj K) := by
    haveI : HasInitial (WithInitial J) := WithInitial.starInitial.hasInitial
    haveI : IsConnected (WithInitial J) := isConnected_of_hasInitial (WithInitial J)
    haveI : HasColimitsOfShape (WithInitial J) (Type u) := inferInstance
    exact joinFunctor_flip_preservesConnectedColimits_of_tensorRight (WithInitial J) K
  haveI : PreservesColimitsOfShape J
      (Under.post (X := (⊥_ SSet.{u})) (joinFunctor.flip.obj K)) :=
    inferInstance
  haveI : PreservesColimitsOfShape J (Under.map (joinBotIso K).inv) :=
    by
      let h := (Under.mapIso (joinBotIso K).symm).toAdjunction.leftAdjoint_preservesColimits
      exact h.preservesColimitsOfShape
  haveI : PreservesColimitsOfShape J (joinUnderFactor K) := by
    change PreservesColimitsOfShape J
      (underInitial ⋙ Under.post (X := (⊥_ SSet.{u})) (joinFunctor.flip.obj K) ⋙
        Under.map (joinBotIso K).inv)
    infer_instance
  exact preservesColimitsOfShape_of_natIso (joinUnderFactorIso K)

abbrev joinUnderOnSimplex (K : SSet.{u}) : SimplexCategory ⥤ Under K :=
  uliftYoneda.{u} ⋙ joinUnder K

abbrev sliceFunctorRestricted (K : SSet.{u}) : Under K ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (joinUnderOnSimplex K)

instance joinUnder_preservesColimitsOfSize_zero (K : SSet.{u}) :
    PreservesColimitsOfSize.{0, u} (joinUnder K) where
  preservesColimitsOfShape {J} [Category.{0} J] := by
    haveI : HasColimitsOfShape (WithInitial J) (Type u) := inferInstance
    exact joinUnder_preservesColimitsOfShape K J

def joinUnderExtensionUnit (K : SSet.{u}) :
    joinUnderOnSimplex K ⟶ uliftYoneda.{u} ⋙ joinUnder K :=
  𝟙 _

instance joinUnder_isLeftKanExtension (K : SSet.{u}) :
    (joinUnder K).IsLeftKanExtension (joinUnderExtensionUnit K) :=
  Presheaf.isLeftKanExtension_of_preservesColimits.{0} (A := joinUnderOnSimplex K)
    (L := joinUnder K) (Iso.refl _)

def adj₂ (K : SSet.{u}) : joinUnder K ⊣ sliceFunctorRestricted K :=
  Presheaf.uliftYonedaAdjunction.{0} (A := joinUnderOnSimplex K) (L := joinUnder K)
    (joinUnderExtensionUnit K)

/-- Maps out of `joinUnder K` are exactly maps `Y ⋆ K ⟶ C` restricting to `p` on `K`. -/
def overPtEquivUnderHom {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) :
    { q : Y ⋆ K ⟶ C // joinInr Y K ≫ q = p } ≃ ((joinUnder K).obj Y ⟶ Under.mk p) where
  toFun q := Under.homMk q.1 q.2
  invFun g := ⟨g.right, Under.w g⟩
  left_inv q := by
    cases q
    rfl
  right_inv g := by
    ext
    rfl

/-- The set of maps `Y ⋆ K ⟶ C` restricting to `p` on the right factor. -/
abbrev OverPt {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) : Type u :=
  { q : Y ⋆ K ⟶ C // joinInr Y K ≫ q = p }

/-- The slice simplicial set `C_{/p}`.  Its `n`-simplices are maps
`Δ[n] ⋆ K ⟶ C` restricting to `p` on the right factor. -/
def sliceOver {K C : SSet.{u}} (p : K ⟶ C) : SSet.{u} where
  obj n := OverPt p (stdSimplex.obj n.unop)
  map {n m} f :=
    ↾fun q =>
      (⟨(joinFunctor.map (stdSimplex.map f.unop)).app K ≫ q.1, by
        rw [← Category.assoc, joinInr_naturality_left]
        exact q.2⟩ : OverPt p (stdSimplex.obj m.unop))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show (joinFunctor.map (stdSimplex.map (𝟙 n).unop)).app K ≫ q.1 = q.1
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show (joinFunctor.map (stdSimplex.map (f ≫ g).unop)).app K ≫ q.1 =
      (joinFunctor.map (stdSimplex.map g.unop)).app K ≫
        (joinFunctor.map (stdSimplex.map f.unop)).app K ≫ q.1
    simp only [unop_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- The representable case of the join-slice universal property. -/
def sliceHomEquivStdSimplex {K C : SSet.{u}} (p : K ⟶ C) (m : SimplexCategory) :
    (stdSimplex.obj m ⟶ sliceOver p) ≃ OverPt p (stdSimplex.obj m) :=
  yonedaEquiv

def restrictedSliceIso {K C : SSet.{u}} (p : K ⟶ C) :
    (sliceFunctorRestricted K).obj (Under.mk p) ≅ sliceOver p :=
  NatIso.ofComponents
    (fun n => Equiv.toIso
      (Equiv.ulift.trans ((overPtEquivUnderHom p (stdSimplex.obj n.unop)).symm)))
    (by
      intro n m f
      ext g
      cases g
      rfl)

/-- The relative join-slice universal property:
maps `Y ⋆ K ⟶ C` restricting to `p` on `K` are the same as maps `Y ⟶ C_{/p}`. -/
def sliceHomEquiv {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) :
    OverPt p Y ≃ (Y ⟶ sliceOver p) :=
  (overPtEquivUnderHom p Y).trans (((adj₂ K).homEquiv Y (Under.mk p)).trans
    (restrictedSliceIso p).homToEquiv)

end

end SSet
