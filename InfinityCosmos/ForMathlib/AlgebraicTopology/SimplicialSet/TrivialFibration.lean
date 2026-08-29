module

/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/

public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

@[expose] public section

/-!
# A trivial fibration between quasi-categories is an equivalence

A trivial fibration of simplicial sets is a map with the right lifting property against the
boundary inclusions `∂Δ[n] ↪ Δ[n]`. Such a map admits a section, and lifting the pair
(section-after-`p`, identity) against `∂ⁱ ⊗ A ↪ ⨰ ⊗ A`, where `∂ⁱ` is the two-endpoint
subcomplex `SSet.coherentIso.boundary`, produces a homotopy over the coherent isomorphism from
`p ≫ section` to the identity. For quasi-categories that is exactly the data of an equivalence.

## Main results

* `SSet.TrivialFibration.section`: a trivial fibration admits a section.
* `SSet.TrivialFibration.leftHomotopy`: the section is a homotopy inverse over `coherentIso`.
* `SSet.TrivialFibration.toQCatEquiv`: a trivial fibration between quasi-categories is an
  equivalence of quasi-categories.
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

/-- A trivial fibration has the right lifting property against all monomorphisms. -/
lemma TrivialFibration.rlp_monomorphisms {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : TrivialFibration p) : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
  rw [SSet.rlp_monomorphisms]
  simpa [TrivialFibration, boundaryInclusions_eq_modelCategoryQuillen_I] using hp

/-- A trivial fibration of simplicial sets admits a section, obtained by lifting against the
monomorphism `⊥ ↪ Y`. -/
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

/-- The map out of `∂ⁱ ⊗ A` that a homotopy `p ≫ section ⇒ 𝟙 A` must restrict to: it is
`section ∘ p` on the source endpoint and the identity on the target endpoint.

The case split is on whether the `coherentIso` coordinate lies in the source endpoint. It is
natural because on the boundary a simplicial operator neither creates nor destroys membership
in the source endpoint, which is `coherentIso.map_mem_range_src_iff_of_boundary`. -/
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

/-- The boundary data lies over `A ⟶ B`, so it is one corner of a lifting problem against `p`. -/
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

/-- The uncurried homotopy, obtained by solving the lifting problem
`∂ⁱ ⊗ A ↪ ⨰ ⊗ A` against `p`. -/
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

/-- The source endpoint of the cylinder, viewed as landing in the boundary subcomplex. -/
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

/-- The target endpoint of the cylinder, viewed as landing in the boundary subcomplex. -/
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

/-- A trivial fibration of simplicial sets has a homotopy over the coherent isomorphism from `p`
followed by its chosen section to the identity. -/
@[no_expose]
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
@[no_expose]
noncomputable def TrivialFibration.toQCatEquiv {A B : QCat} {p : A ⟶ B}
    (hp : TrivialFibration p.hom) :
    @QCat.Equiv A.obj B.obj A.property B.property where
  toFun := p.hom
  invFun := hp.section
  left_inv := hp.leftHomotopy
  right_inv := by
    rw [hp.section_comp]
    exact Homotopy.refl (I := coherentIso) (𝟙 B.obj)

/-- Existence form of `TrivialFibration.toQCatEquiv`, recording that the equivalence produced
has the original map as its forward direction. -/
lemma TrivialFibration.toQCatEquiv_exists {A B : QCat} {p : A ⟶ B}
    (hp : TrivialFibration p.hom) :
    ∃ e : @QCat.Equiv A.obj B.obj A.property B.property, e.toFun = p.hom :=
  ⟨hp.toQCatEquiv, rfl⟩

end trivialFibration

end SSet
