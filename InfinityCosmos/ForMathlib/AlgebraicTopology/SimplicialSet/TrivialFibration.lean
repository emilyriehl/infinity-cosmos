/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Trivial fibrations of simplicial sets

A trivial fibration of simplicial sets is a map with the right lifting property against the
boundary inclusions. This file records that this class agrees with mathlib's generating
cofibrations, is stable under pullback and Leibniz cotensor with monomorphisms, admits a
section, and that a trivial fibration between quasi-categories is an equivalence of
quasi-categories.
-/

universe u

namespace SSet

open CategoryTheory Limits MorphismProperty Simplicial
open MonoidalCategory MonoidalClosed HomotopicalAlgebra

section trivialFibration

/-- The local class `BoundaryInclusions` agrees with mathlib's generating cofibrations for
simplicial sets. -/
lemma boundaryInclusions_eq_modelCategoryQuillen_I :
    BoundaryInclusions = modelCategoryQuillen.I := by
  ext X Y f
  constructor
  · intro hf
    cases hf with
    | mk n => exact modelCategoryQuillen.boundary_ι_mem_I n
  · intro hf
    rw [modelCategoryQuillen.I, MorphismProperty.ofHoms_iff] at hf
    rcases hf with ⟨n, hn⟩
    cases hn
    exact BoundaryInclusion.mk n

/-- Trivial fibrations of simplicial sets are stable under base change. -/
instance trivialFibration_isStableUnderBaseChange :
    TrivialFibration.IsStableUnderBaseChange := by
  change BoundaryInclusions.rlp.IsStableUnderBaseChange
  infer_instance

/-- Trivial fibrations of simplicial sets are stable under products of a fixed shape. -/
instance trivialFibration_isStableUnderProductsOfShape (J : Type*) :
    TrivialFibration.IsStableUnderProductsOfShape J := by
  change BoundaryInclusions.rlp.IsStableUnderProductsOfShape J
  infer_instance

/-- A trivial fibration has the right lifting property against all monomorphisms. -/
lemma TrivialFibration.rlp_monomorphisms {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : TrivialFibration p) : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
  rw [SSet.rlp_monomorphisms]
  simpa [TrivialFibration, boundaryInclusions_eq_modelCategoryQuillen_I] using hp

/-- Trivial fibrations of simplicial sets are exactly the maps with the right lifting property
against all monomorphisms. -/
lemma trivialFibration_eq_rlp_monomorphisms :
    TrivialFibration = (MorphismProperty.monomorphisms SSet.{u}).rlp := by
  change BoundaryInclusions.rlp = (MorphismProperty.monomorphisms SSet.{u}).rlp
  rw [boundaryInclusions_eq_modelCategoryQuillen_I]
  exact SSet.rlp_monomorphisms.symm

private noncomputable def arrowIsoRange {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Arrow.mk i ≅ Arrow.mk (Subcomplex.range i).ι :=
  Arrow.isoMk' i (Subcomplex.range i).ι (asIso (Subcomplex.toRange i)) (Iso.refl _) (by
    simp)

/-- The pushout-product of a monomorphism with a boundary inclusion is a monomorphism. -/
lemma pushoutProduct_boundary_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    Mono ((Arrow.mk i □ Arrow.mk (∂Δ[n].ι)).hom) := by
  let S : Y.Subcomplex := Subcomplex.range i
  let T : (Δ[n] : SSet.{u}).Subcomplex := ∂Δ[n]
  have htarget : (MorphismProperty.monomorphisms SSet.{u})
      ((Arrow.mk S.ι □ Arrow.mk T.ι).hom) := by
    have hUnion : (MorphismProperty.monomorphisms SSet.{u}) (S.unionProd T).ι := by
      infer_instance
    exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff
      (Subcomplex.unionProd.ιIso S T)).1 hUnion
  have e : (Arrow.mk i □ Arrow.mk T.ι) ≅ (Arrow.mk S.ι □ Arrow.mk T.ι) :=
    ((MonoidalCategory.Arrow.pushoutProduct.mapIso (arrowIsoRange i)).app (Arrow.mk T.ι))
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff e).2 htarget

/-- Trivial fibrations of simplicial sets are stable under pullback. -/
lemma TrivialFibration.of_isPullback {X Y Y' S : SSet.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f)
    (hg : TrivialFibration g) : TrivialFibration g' :=
  MorphismProperty.of_isPullback sq hg

/-- Products of trivial fibrations of simplicial sets are trivial fibrations. -/
lemma TrivialFibration.piMap {J : Type*} {X Y : J → SSet.{u}} [HasProduct X] [HasProduct Y]
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, TrivialFibration (f j)) :
    TrivialFibration (Limits.Pi.map f) := by
  let α : Discrete.functor X ⟶ Discrete.functor Y :=
    Discrete.natTrans (fun j : Discrete J => f j.as)
  change BoundaryInclusions.rlp (limMap α)
  refine MorphismProperty.limMap (W := BoundaryInclusions.rlp) α ?_
  intro j
  change BoundaryInclusions.rlp (f j.as)
  simpa [TrivialFibration] using hf j.as

/-- Pullback-hom projections along monomorphisms preserve trivial fibrations of simplicial sets. -/
lemma TrivialFibration.pullbackObjObjπ {X₁ Y₁ E B : SSet.{u}} {i : X₁ ⟶ Y₁}
    {p : E ⟶ B} [Mono i] (hp : TrivialFibration p)
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    TrivialFibration sq₁₃.π := by
  rw [trivialFibration_eq_rlp_monomorphisms] at hp
  change BoundaryInclusions.rlp sq₁₃.π
  intro A B j hj
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i j) sq₁₃]
  cases hj with
  | mk n =>
      change HasLiftingProperty ((Arrow.mk i □ Arrow.mk (∂Δ[n].ι)).hom) p
      exact hp _ (pushoutProduct_boundary_mono i n)

/-- Every map from the terminal simplex `Δ[0]` is a monomorphism. -/
lemma mono_yonedaEquiv_symm_zero {X : SSet.{u}} (x : X _⦋0⦌) :
    Mono (yonedaEquiv.symm x : Δ[0] ⟶ X) where
  right_cancellation := by
    intro Z g h _w
    exact isTerminalDeltaZero.hom_ext g h

/-- The generating maps for quasi-category isofibrations are monomorphisms of simplicial sets. -/
lemma innerHornIsoInclusions_le_monomorphisms :
    InnerHornIsoInclusions ≤ MorphismProperty.monomorphisms SSet := by
  intro X Y f hf
  rcases hf with h | h | h
  · cases h with
    | mk n i low high => infer_instance
  · cases h with
    | mk =>
        haveI := mono_yonedaEquiv_symm_zero coherentIso.x₀
        exact MorphismProperty.monomorphisms.infer_property _
  · cases h with
    | mk =>
        haveI := mono_yonedaEquiv_symm_zero coherentIso.x₁
        exact MorphismProperty.monomorphisms.infer_property _

/-- A trivial fibration of simplicial sets between quasi-categories is an isofibration. -/
lemma TrivialFibration.toIsofibration {A B : QCat} {p : A ⟶ B}
    (hp : TrivialFibration p.hom) : Isofibration p := by
  exact MorphismProperty.antitone_rlp innerHornIsoInclusions_le_monomorphisms p.hom
    hp.rlp_monomorphisms

/-- A trivial fibration of simplicial sets admits a section. -/
noncomputable def TrivialFibration.section {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : TrivialFibration p) : Y ⟶ X := by
  haveI : Mono (initial.to Y : ⊥_ SSet.{u} ⟶ Y) := inferInstance
  haveI : HasLiftingProperty (initial.to Y : ⊥_ SSet.{u} ⟶ Y) p :=
    hp.rlp_monomorphisms _ (MorphismProperty.monomorphisms.infer_property _)
  let sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) :=
    CommSq.mk (by simp [initial.to_comp])
  exact sq.lift

/-- The section of a trivial fibration is a right inverse. -/
@[reassoc (attr := simp)]
lemma TrivialFibration.section_comp {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : TrivialFibration p) : hp.section ≫ p = 𝟙 Y := by
  unfold TrivialFibration.section
  simp

private noncomputable def TrivialFibration.boundaryHomotopyDomainMap
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    ((coherentIso.boundary.prod (⊤ : A.Subcomplex) : (coherentIso ⊗ A).Subcomplex) : SSet) ⟶
      A where
  app n := by
    classical
    exact ↾(fun x =>
      if (x : (coherentIso ⊗ A).obj n).1 ∈ (Subcomplex.range coherentIso.src).obj n then
        hp.section.app n (p.app n (x : (coherentIso ⊗ A).obj n).2)
      else
        (x : (coherentIso ⊗ A).obj n).2)
  naturality := by
    intro n m α
    ext x
    classical
    let y : (coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.obj m :=
      (coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x
    by_cases hsrc : (x : (coherentIso ⊗ A).obj n).1 ∈
      (Subcomplex.range coherentIso.src).obj n
    · have hsrc_y : (y : (coherentIso ⊗ A).obj m).1 ∈
        (Subcomplex.range coherentIso.src).obj m := by
        change coherentIso.map α (x : (coherentIso ⊗ A).obj n).1 ∈
          (Subcomplex.range coherentIso.src).obj m
        exact (Subcomplex.range coherentIso.src).map α hsrc
      dsimp
      have hsrc_y0 :
          (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
            (coherentIso ⊗ A).obj m).1) ∈
            (Subcomplex.range coherentIso.src).obj m := by
        simpa [y] using hsrc_y
      change
        (if (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
            (coherentIso ⊗ A).obj m).1) ∈ (Subcomplex.range coherentIso.src).obj m then
          hp.section.app m (p.app m
            (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
              (coherentIso ⊗ A).obj m).2))
        else
          (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
            (coherentIso ⊗ A).obj m).2)) =
        A.map α
          (if (x : (coherentIso ⊗ A).obj n).1 ∈
              (Subcomplex.range coherentIso.src).obj n then
            hp.section.app n (p.app n (x : (coherentIso ⊗ A).obj n).2)
          else
            (x : (coherentIso ⊗ A).obj n).2)
      rw [if_pos hsrc_y0, if_pos hsrc]
      change hp.section.app m (p.app m (A.map α (x : (coherentIso ⊗ A).obj n).2)) =
        A.map α (hp.section.app n (p.app n (x : (coherentIso ⊗ A).obj n).2))
      rw [show p.app m (A.map α (x : (coherentIso ⊗ A).obj n).2) =
          B.map α (p.app n (x : (coherentIso ⊗ A).obj n).2) by
        exact ConcreteCategory.congr_hom (p.naturality α) (x : (coherentIso ⊗ A).obj n).2]
      exact ConcreteCategory.congr_hom (hp.section.naturality α)
        (p.app n (x : (coherentIso ⊗ A).obj n).2)
    · have hiff := coherentIso.map_mem_range_src_iff_of_boundary α x.property.left
      have hsrc_y : (y : (coherentIso ⊗ A).obj m).1 ∉
        (Subcomplex.range coherentIso.src).obj m := by
        change coherentIso.map α (x : (coherentIso ⊗ A).obj n).1 ∉
          (Subcomplex.range coherentIso.src).obj m
        intro hm
        exact hsrc (hiff.1 hm)
      dsimp
      have hsrc_y0 :
          ¬ (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
            (coherentIso ⊗ A).obj m).1) ∈
            (Subcomplex.range coherentIso.src).obj m := by
        simpa [y] using hsrc_y
      change
        (if (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
            (coherentIso ⊗ A).obj m).1) ∈ (Subcomplex.range coherentIso.src).obj m then
          hp.section.app m (p.app m
            (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
              (coherentIso ⊗ A).obj m).2))
        else
          (((coherentIso.boundary.prod (⊤ : A.Subcomplex)).toSSet.map α x :
            (coherentIso ⊗ A).obj m).2)) =
        A.map α
          (if (x : (coherentIso ⊗ A).obj n).1 ∈
              (Subcomplex.range coherentIso.src).obj n then
            hp.section.app n (p.app n (x : (coherentIso ⊗ A).obj n).2)
          else
            (x : (coherentIso ⊗ A).obj n).2)
      rw [if_neg hsrc_y0, if_neg hsrc]
      change A.map α (x : (coherentIso ⊗ A).obj n).2 =
        A.map α (x : (coherentIso ⊗ A).obj n).2
      rfl

private lemma TrivialFibration.boundaryHomotopyDomainMap_comp
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    hp.boundaryHomotopyDomainMap ≫ p =
      (coherentIso.boundary.prod (⊤ : A.Subcomplex)).ι ≫
        CartesianMonoidalCategory.snd coherentIso A ≫ p := by
  ext n x
  classical
  by_cases hsrc : (x : (coherentIso ⊗ A).obj n).1 ∈
    (Subcomplex.range coherentIso.src).obj n
  · dsimp [TrivialFibration.boundaryHomotopyDomainMap]
    rw [if_pos hsrc]
    change p.app n (hp.section.app n (p.app n (x : (coherentIso ⊗ A).obj n).2)) =
      p.app n (x : (coherentIso ⊗ A).obj n).2
    exact congrFun (congrArg (fun q => q.app n) hp.section_comp)
      (p.app n (x : (coherentIso ⊗ A).obj n).2)
  · dsimp [TrivialFibration.boundaryHomotopyDomainMap]
    rw [if_neg hsrc]
    rfl

private noncomputable def TrivialFibration.leftHomotopyUncurry
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    coherentIso ⊗ A ⟶ A := by
  haveI : HasLiftingProperty (coherentIso.boundary.prod (⊤ : A.Subcomplex)).ι p :=
    hp.rlp_monomorphisms _ (MorphismProperty.monomorphisms.infer_property _)
  let sq : CommSq hp.boundaryHomotopyDomainMap
      (coherentIso.boundary.prod (⊤ : A.Subcomplex)).ι
      p
      (CartesianMonoidalCategory.snd coherentIso A ≫ p) :=
    CommSq.mk (by
      exact hp.boundaryHomotopyDomainMap_comp)
  exact sq.lift

private lemma TrivialFibration.leftHomotopyUncurry_fac_left
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    (coherentIso.boundary.prod (⊤ : A.Subcomplex)).ι ≫ hp.leftHomotopyUncurry =
      hp.boundaryHomotopyDomainMap := by
  unfold TrivialFibration.leftHomotopyUncurry
  simp

private noncomputable def coherentIso.boundarySrcCylinder (A : SSet.{u}) :
    A ⟶ (coherentIso.boundary.prod (⊤ : A.Subcomplex) : SSet.{u}) :=
  (coherentIso.boundary.prod (⊤ : A.Subcomplex)).lift
    ((λ_ A).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ A))
    (by
      rintro n _ ⟨x, rfl⟩
      constructor
      · exact Or.inl ⟨_, rfl⟩
      · simp)

@[reassoc (attr := simp)]
private lemma coherentIso.boundarySrcCylinder_ι (A : SSet.{u}) :
    coherentIso.boundarySrcCylinder A ≫
      (coherentIso.boundary.prod (⊤ : A.Subcomplex)).ι =
      (λ_ A).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ A) := by
  simp [coherentIso.boundarySrcCylinder]

private noncomputable def coherentIso.boundaryTgtCylinder (A : SSet.{u}) :
    A ⟶ (coherentIso.boundary.prod (⊤ : A.Subcomplex) : SSet.{u}) :=
  (coherentIso.boundary.prod (⊤ : A.Subcomplex)).lift
    ((λ_ A).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.tgt) ▷ A))
    (by
      rintro n _ ⟨x, rfl⟩
      constructor
      · exact Or.inr ⟨_, rfl⟩
      · simp)

@[reassoc (attr := simp)]
private lemma coherentIso.boundaryTgtCylinder_ι (A : SSet.{u}) :
    coherentIso.boundaryTgtCylinder A ≫
      (coherentIso.boundary.prod (⊤ : A.Subcomplex)).ι =
      (λ_ A).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.tgt) ▷ A) := by
  simp [coherentIso.boundaryTgtCylinder]

private lemma TrivialFibration.boundarySrcCylinder_boundaryHomotopyDomainMap
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    coherentIso.boundarySrcCylinder A ≫ hp.boundaryHomotopyDomainMap =
      p ≫ hp.section := by
  ext n x
  classical
  dsimp [coherentIso.boundarySrcCylinder, TrivialFibration.boundaryHomotopyDomainMap]
  rw [if_pos]
  · rfl
  · exact ⟨_, rfl⟩

private lemma TrivialFibration.boundaryTgtCylinder_boundaryHomotopyDomainMap
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    coherentIso.boundaryTgtCylinder A ≫ hp.boundaryHomotopyDomainMap =
      𝟙 A := by
  ext n x
  classical
  dsimp [coherentIso.boundaryTgtCylinder, TrivialFibration.boundaryHomotopyDomainMap]
  rw [if_neg]
  · rfl
  · intro hsrc
    exact coherentIso.not_mem_range_src_of_mem_range_tgt ⟨_, rfl⟩ hsrc

private lemma TrivialFibration.leftHomotopyUncurry_src
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    (λ_ A).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ A) ≫
      hp.leftHomotopyUncurry =
      p ≫ hp.section := by
  rw [← coherentIso.boundarySrcCylinder_ι_assoc]
  rw [hp.leftHomotopyUncurry_fac_left]
  exact hp.boundarySrcCylinder_boundaryHomotopyDomainMap

private lemma TrivialFibration.leftHomotopyUncurry_tgt
    {A B : SSet.{u}} {p : A ⟶ B} (hp : TrivialFibration p) :
    (λ_ A).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.tgt) ▷ A) ≫
      hp.leftHomotopyUncurry =
      𝟙 A := by
  rw [← coherentIso.boundaryTgtCylinder_ι_assoc]
  rw [hp.leftHomotopyUncurry_fac_left]
  exact hp.boundaryTgtCylinder_boundaryHomotopyDomainMap

/-- A trivial fibration of simplicial sets has a homotopy from `p` followed by its chosen
section to the identity. -/
noncomputable def TrivialFibration.leftHomotopy {A B : SSet.{u}} {p : A ⟶ B}
    (hp : TrivialFibration p) : Homotopy (I := coherentIso) (p ≫ hp.section) (𝟙 A) where
  homotopy := MonoidalClosed.curry hp.leftHomotopyUncurry
  source_eq := by
    change MonoidalClosed.curry hp.leftHomotopyUncurry ≫
        (MonoidalClosed.pre coherentIso.src).app A ≫ A.expPointIsoSelf.hom =
      p ≫ hp.section
    rw [SSet.curry_endpoint_eval]
    exact hp.leftHomotopyUncurry_src
  target_eq := by
    change MonoidalClosed.curry hp.leftHomotopyUncurry ≫
        (MonoidalClosed.pre coherentIso.tgt).app A ≫ A.expPointIsoSelf.hom =
      𝟙 A
    rw [SSet.curry_endpoint_eval]
    exact hp.leftHomotopyUncurry_tgt

/-- A trivial fibration of simplicial sets between quasi-categories is an equivalence of
quasi-categories. -/
noncomputable def TrivialFibration.toQCatEquiv {A B : QCat} {p : A ⟶ B}
    (hp : TrivialFibration p.hom) :
    @QCat.Equiv A.obj B.obj A.property B.property where
  toFun := p.hom
  invFun := hp.section
  left_inv := hp.leftHomotopy
  right_inv := by
    rw [hp.section_comp]
    exact Homotopy.refl (I := coherentIso) (𝟙 B.obj)

/-- The equivalence induced by a trivial fibration has the original map as its forward map. -/
lemma TrivialFibration.toQCatEquiv_toFun {A B : QCat} {p : A ⟶ B}
    (hp : TrivialFibration p.hom) :
    hp.toQCatEquiv.toFun = p.hom := rfl

/-- Existence form of `TrivialFibration.toQCatEquiv`. -/
lemma TrivialFibration.toQCatEquiv_exists {A B : QCat} {p : A ⟶ B}
    (hp : TrivialFibration p.hom) :
    ∃ e : @QCat.Equiv A.obj B.obj A.property B.property, e.toFun = p.hom :=
  ⟨hp.toQCatEquiv, rfl⟩

end trivialFibration

end SSet
