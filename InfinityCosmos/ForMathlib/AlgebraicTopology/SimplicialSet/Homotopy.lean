/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import Architect
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.AlgebraicTopology.Quasicategory.Basic

universe u v w

namespace SSet

open CategoryTheory Simplicial SimplicialCategory Limits

/-- An interval is a simplicial set equipped with two endpoints.-/
class Interval (I : SSet.{u}) : Type u where
  src : Δ[0] ⟶ I
  tgt : Δ[0] ⟶ I

/-- The interval relevant to the theory of Kan complexes.-/
instance arrowInterval : Interval Δ[1] where
  src := stdSimplex.δ (n := 0) (1)
  tgt := stdSimplex.δ (n := 0) (0)

/-- The interval relevant to the theory of quasi-categories. -/
instance isoInterval : Interval coherentIso where
  src := yonedaEquiv.symm (coherentIso.x₀)
  tgt := yonedaEquiv.symm (coherentIso.x₁)

open MonoidalCategory
noncomputable def pointIsUnit : Δ[0] ≅ (𝟙_ SSet) :=
  IsTerminal.uniqueUpToIso isTerminalDeltaZero (IsTerminal.ofUnique (𝟙_ SSet))

/-- The right unit comparison through `Δ[0]` agrees with the left unit comparison followed by
the braiding. -/
lemma rightUnitor_inv_pointIsUnit_inv (Y : SSet.{u}) :
    (ρ_ Y).inv ≫ Y ◁ pointIsUnit.inv =
      (λ_ Y).inv ≫ pointIsUnit.inv ▷ Y ≫ (β_ (Δ[0] : SSet.{u}) Y).hom := by
  ext n x
  cases n using Opposite.rec
  rfl

noncomputable def expUnitNatIso : ihom (𝟙_ SSet) ≅ 𝟭 SSet :=
  (conjugateIsoEquiv (Adjunction.id (C := SSet)) (ihom.adjunction _)
    (leftUnitorNatIso _)).symm

noncomputable def expPointNatIso : ihom Δ[0] ≅ 𝟭 SSet := by
  refine ?_ ≪≫ expUnitNatIso
  exact {
    hom := MonoidalClosed.pre pointIsUnit.inv
    inv := MonoidalClosed.pre pointIsUnit.hom
    hom_inv_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.hom_inv_id]
      exact MonoidalClosed.pre_id _
    inv_hom_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.inv_hom_id]
      exact MonoidalClosed.pre_id _
  }

noncomputable def expPointIsoSelf (X : SSet) : sHom Δ[0] X ≅ X := expPointNatIso.app X

namespace coherentIso

/-- A contraction of the coherent isomorphism from the constant source path to the identity.

The first factor is the homotopy parameter and the second factor is the path parameter. -/
noncomputable def srcContraction : coherentIso ⊗ coherentIso ⟶ coherentIso where
  app n := by
    exact ↾(fun (x : (coherentIso ⊗ coherentIso).obj n) => by
      cases n using Opposite.rec
      refine coherentIso.equivFun.symm ?_
      intro i
      exact if (coherentIso.equivFun x.1 i).as.down then coherentIso.equivFun x.2 i else WalkingIso.zero)
  naturality := by
    intro n m α
    ext x
    cases n using Opposite.rec
    cases m using Opposite.rec
    rfl

/-- At the source endpoint, `srcContraction` is the constant source path. -/
lemma srcContraction_src :
    ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ coherentIso) ≫ srcContraction =
      (λ_ coherentIso).hom ≫ SSet.isTerminalDeltaZero.from coherentIso ≫ coherentIso.src := by
  ext n x
  cases n using Opposite.rec
  rfl

/-- At the target endpoint, `srcContraction` is the identity. -/
lemma srcContraction_tgt :
    ((SSet.pointIsUnit.inv ≫ coherentIso.tgt) ▷ coherentIso) ≫ srcContraction =
      (λ_ coherentIso).hom := by
  ext n x
  cases n using Opposite.rec
  rfl

end coherentIso

/-- The source vertex inclusion evaluates to the constant-zero simplex of `coherentIso`. -/
@[simp]
lemma coherentIso_src_app_equivFun_zero {n : SimplexCategoryᵒᵖ}
    (x : (Δ[0] : SSet.{u}).obj n) :
    coherentIso.equivFun ((coherentIso.src.app n) x) = fun _ => WalkingIso.zero := by
  exact coherentIso.mem_range_src_const ⟨x, rfl⟩

/-- If the path variable is fixed at the source vertex, the source contraction stays at the
source vertex. -/
lemma coherentIso_srcContraction_path_src :
    (coherentIso ◁ coherentIso.src) ≫ coherentIso.srcContraction =
      CartesianMonoidalCategory.snd coherentIso (Δ[0] : SSet.{u}) ≫ coherentIso.src := by
  have hsymm : ∀ {m : ℕ} (g : Fin (m + 1) → WalkingIso.{u}) (j : Fin (m + 1)),
      (coherentIso.equivFun.symm g).obj j = g j := fun _ _ => rfl
  ext n x
  cases n using Opposite.rec with
  | op n =>
    simp [coherentIso.srcContraction, hsymm]
    split <;> rfl

open MonoidalClosed

/-- Evaluating a curried map out of the tensor unit agrees with precomposition by the left
unitor. -/
lemma curry_unitIsoSelf_hom {A B : SSet.{u}} (H : 𝟙_ SSet.{u} ⊗ A ⟶ B) :
    MonoidalClosed.curry H ≫ (MonoidalClosed.unitIsoSelf (C := SSet.{u}) (X := B)).hom =
      (λ_ A).inv ≫ H := by
  change MonoidalClosed.curry H ≫ (MonoidalClosed.unitNatIso.app B).inv = (λ_ A).inv ≫ H
  change MonoidalClosed.curry H ≫ (λ_ ((ihom (𝟙_ SSet.{u})).obj B)).inv ≫
      (ihom.ev (𝟙_ SSet.{u})).app B = (λ_ A).inv ≫ H
  rw [leftUnitor_inv_naturality_assoc]
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  rfl

/-- Evaluating a curried map out of `Δ[0]` agrees with precomposition by the canonical
`A ⟶ Δ[0] ⊗ A`. -/
lemma curry_expPointIsoSelf_hom {A B : SSet.{u}} (H : Δ[0] ⊗ A ⟶ B) :
    MonoidalClosed.curry H ≫ B.expPointIsoSelf.hom =
      (λ_ A).inv ≫ (SSet.pointIsUnit.inv ▷ A) ≫ H := by
  change MonoidalClosed.curry H ≫
      ((MonoidalClosed.pre SSet.pointIsUnit.inv).app B ≫
        (MonoidalClosed.unitIsoSelf (C := SSet.{u}) (X := B)).hom) =
      (λ_ A).inv ≫ (SSet.pointIsUnit.inv ▷ A) ≫ H
  slice_lhs 1 2 => rw [MonoidalClosed.curry_pre_app]
  exact curry_unitIsoSelf_hom ((SSet.pointIsUnit.inv ▷ A) ≫ H)

set_option backward.isDefEq.respectTransparency false in
/-- The uncurried inverse point-evaluation isomorphism is evaluation through the unit comparison
`Δ[0] ≅ 𝟙_ SSet`. -/
lemma uncurry_expPointIsoSelf_inv (Y : SSet.{u}) :
    MonoidalClosed.uncurry Y.expPointIsoSelf.inv =
      (SSet.pointIsUnit.hom ▷ Y) ≫ (λ_ Y).hom := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_uncurry]
  apply (cancel_mono Y.expPointIsoSelf.hom).mp
  change Y.expPointIsoSelf.inv ≫ Y.expPointIsoSelf.hom =
    MonoidalClosed.curry ((SSet.pointIsUnit.hom ▷ Y) ≫ (λ_ Y).hom) ≫
      Y.expPointIsoSelf.hom
  rw [SSet.curry_expPointIsoSelf_hom]
  simp only [Iso.inv_hom_id]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp

/-- Evaluating a curried cylinder at a chosen endpoint. -/
lemma curry_endpoint_eval {I A B : SSet.{u}} (endpoint : Δ[0] ⟶ I) (H : I ⊗ A ⟶ B) :
    MonoidalClosed.curry H ≫ (MonoidalClosed.pre endpoint).app B ≫ B.expPointIsoSelf.hom =
      (λ_ A).inv ≫ (SSet.pointIsUnit.inv ≫ endpoint) ▷ A ≫ H := by
  rw [← Category.assoc]
  slice_lhs 1 2 => rw [MonoidalClosed.curry_pre_app]
  rw [curry_expPointIsoSelf_hom]
  rw [comp_whiskerRight]
  rfl

section

variable {I : SSet.{u}} [Interval I]

@[nolint unusedArguments]
noncomputable def pathSpace {I : SSet.{u}} [Interval I] (X : SSet.{u}) : SSet.{u} := sHom I X

noncomputable def pathSpace.src (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.src).app X ≫ X.expPointIsoSelf.hom)

noncomputable def pathSpace.tgt (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.tgt).app X ≫ X.expPointIsoSelf.hom)

/-- The constant path map from a simplicial set to its path space. -/
noncomputable def pathSpace.const (X : SSet.{u}) : X ⟶ pathSpace (I := I) X :=
  X.expPointIsoSelf.inv ≫
    (MonoidalClosed.pre (isTerminalDeltaZero.from I : I ⟶ Δ[0])).app X

omit [Interval I] in
private lemma pathSpace.const_endpoint_aux (X : SSet.{u}) (endpoint : Δ[0] ⟶ I) :
    X.expPointIsoSelf.inv ≫
        (MonoidalClosed.pre (isTerminalDeltaZero.from I : I ⟶ Δ[0])).app X ≫
        (MonoidalClosed.pre endpoint).app X ≫ X.expPointIsoSelf.hom = 𝟙 X := by
  let t : I ⟶ Δ[0] := isTerminalDeltaZero.from I
  let a := (MonoidalClosed.pre t).app X
  let b := (MonoidalClosed.pre endpoint).app X
  let e := X.expPointIsoSelf
  have ht : endpoint ≫ t = 𝟙 Δ[0] := isTerminalDeltaZero.hom_ext _ _
  have hab : a ≫ b = 𝟙 _ := by
    dsimp [a, b, t]
    have hpre := congrArg (fun η => η.app X)
      (MonoidalClosed.pre_map endpoint (isTerminalDeltaZero.from I : I ⟶ Δ[0]))
    simpa [NatTrans.comp_app, ht, MonoidalClosed.pre_id] using hpre.symm
  have hab' : a ≫ b = 𝟙 (sHom Δ[0] X) := by
    change a ≫ b = 𝟙 _
    exact hab
  change e.inv ≫ (a ≫ b) ≫ e.hom = 𝟙 X
  calc
    e.inv ≫ (a ≫ b) ≫ e.hom = e.inv ≫ 𝟙 (sHom Δ[0] X) ≫ e.hom := by
      exact congrArg (fun h => e.inv ≫ h ≫ e.hom) hab'
    _ = 𝟙 X := by
      simp [e]

/-- The constant path evaluates at the source endpoint to the identity. -/
@[reassoc (attr := simp)]
lemma pathSpace.const_src (X : SSet.{u}) :
    pathSpace.const (I := I) X ≫ pathSpace.src X = 𝟙 X := by
  exact pathSpace.const_endpoint_aux (I := I) X Interval.src

/-- The constant path evaluates at the target endpoint to the identity. -/
@[reassoc (attr := simp)]
lemma pathSpace.const_tgt (X : SSet.{u}) :
    pathSpace.const (I := I) X ≫ pathSpace.tgt X = 𝟙 X := by
  exact pathSpace.const_endpoint_aux (I := I) X Interval.tgt


/-- TODO: Figure out how to allow `I` to be an a different universe from `A` and `B`?-/
structure Homotopy {A B : SSet.{u}} (f g : A ⟶ B) : Type u
    where
  homotopy : A ⟶ sHom I B
  source_eq : homotopy ≫ pathSpace.src B = f
  target_eq : homotopy ≫ pathSpace.tgt B = g

/-- The constant homotopy from a map to itself. -/
noncomputable def Homotopy.refl {A B : SSet.{u}} (f : A ⟶ B) : Homotopy (I := I) f f where
  homotopy := f ≫ pathSpace.const (I := I) B
  source_eq := by
    change f ≫ (pathSpace.const (I := I) B ≫ pathSpace.src (I := I) B) = f
    rw [pathSpace.const_src (I := I) B, Category.comp_id]
  target_eq := by
    change f ≫ (pathSpace.const (I := I) B ≫ pathSpace.tgt (I := I) B) = f
    rw [pathSpace.const_tgt (I := I) B, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Source evaluation from a path space is natural in the target. -/
lemma pathSpace.src_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom I).map f ≫ pathSpace.src (I := I) Y = pathSpace.src (I := I) X ≫ f := by
  dsimp [pathSpace.src, expPointIsoSelf]
  have hpre : (MonoidalClosed.pre Interval.src).app X ≫ (ihom Δ[0]).map f =
      (ihom I).map f ≫ (MonoidalClosed.pre Interval.src).app Y := by
    exact MonoidalClosed.pre_comm_ihom_map (W := Δ[0]) (X := I) Interval.src f
  calc
    ((ihom I).map f ≫ (MonoidalClosed.pre Interval.src).app Y) ≫
        (expPointNatIso.app Y).hom =
        ((MonoidalClosed.pre Interval.src).app X ≫ (ihom Δ[0]).map f) ≫
          (expPointNatIso.app Y).hom := by
          exact congrArg (fun q => q ≫ (expPointNatIso.app Y).hom) hpre.symm
    _ = (MonoidalClosed.pre Interval.src).app X ≫
        ((ihom Δ[0]).map f ≫ (expPointNatIso.app Y).hom) := by rw [Category.assoc]
    _ = (MonoidalClosed.pre Interval.src).app X ≫ ((expPointNatIso.app X).hom ≫ f) := by
          exact congrArg (fun q => (MonoidalClosed.pre Interval.src).app X ≫ q)
            (expPointNatIso.hom.naturality f)
    _ = ((MonoidalClosed.pre Interval.src).app X ≫ (expPointNatIso.app X).hom) ≫ f := by
          rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Target evaluation from a path space is natural in the target. -/
lemma pathSpace.tgt_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom I).map f ≫ pathSpace.tgt (I := I) Y = pathSpace.tgt (I := I) X ≫ f := by
  dsimp [pathSpace.tgt, expPointIsoSelf]
  have hpre : (MonoidalClosed.pre Interval.tgt).app X ≫ (ihom Δ[0]).map f =
      (ihom I).map f ≫ (MonoidalClosed.pre Interval.tgt).app Y := by
    exact MonoidalClosed.pre_comm_ihom_map (W := Δ[0]) (X := I) Interval.tgt f
  calc
    ((ihom I).map f ≫ (MonoidalClosed.pre Interval.tgt).app Y) ≫
        (expPointNatIso.app Y).hom =
        ((MonoidalClosed.pre Interval.tgt).app X ≫ (ihom Δ[0]).map f) ≫
          (expPointNatIso.app Y).hom := by
          exact congrArg (fun q => q ≫ (expPointNatIso.app Y).hom) hpre.symm
    _ = (MonoidalClosed.pre Interval.tgt).app X ≫
        ((ihom Δ[0]).map f ≫ (expPointNatIso.app Y).hom) := by rw [Category.assoc]
    _ = (MonoidalClosed.pre Interval.tgt).app X ≫ ((expPointNatIso.app X).hom ≫ f) := by
          exact congrArg (fun q => (MonoidalClosed.pre Interval.tgt).app X ≫ q)
            (expPointNatIso.hom.naturality f)
    _ = ((MonoidalClosed.pre Interval.tgt).app X ≫ (expPointNatIso.app X).hom) ≫ f := by
          rw [Category.assoc]

/-- Precomposition preserves homotopies. -/
noncomputable def Homotopy.precomp {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : Homotopy (I := I) f g) (h : C ⟶ A) : Homotopy (I := I) (h ≫ f) (h ≫ g) where
  homotopy := h ≫ H.homotopy
  source_eq := by rw [Category.assoc, H.source_eq]
  target_eq := by rw [Category.assoc, H.target_eq]

/-- Postcomposition preserves homotopies. -/
noncomputable def Homotopy.postcomp {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : Homotopy (I := I) f g) (h : B ⟶ C) : Homotopy (I := I) (f ≫ h) (g ≫ h) where
  homotopy := H.homotopy ≫ (ihom I).map h
  source_eq := by
    calc
      (H.homotopy ≫ (ihom I).map h) ≫ pathSpace.src (I := I) C =
          H.homotopy ≫ ((ihom I).map h ≫ pathSpace.src (I := I) C) := by
            rw [Category.assoc]
      _ = H.homotopy ≫ (pathSpace.src (I := I) B ≫ h) := by
            exact congrArg (fun q => H.homotopy ≫ q) (pathSpace.src_naturality h)
      _ = (H.homotopy ≫ pathSpace.src (I := I) B) ≫ h := by
            rw [Category.assoc]
      _ = f ≫ h := by
            exact congrArg (fun q => q ≫ h) H.source_eq
  target_eq := by
    calc
      (H.homotopy ≫ (ihom I).map h) ≫ pathSpace.tgt (I := I) C =
          H.homotopy ≫ ((ihom I).map h ≫ pathSpace.tgt (I := I) C) := by
            rw [Category.assoc]
      _ = H.homotopy ≫ (pathSpace.tgt (I := I) B ≫ h) := by
            exact congrArg (fun q => H.homotopy ≫ q) (pathSpace.tgt_naturality h)
      _ = (H.homotopy ≫ pathSpace.tgt (I := I) B) ≫ h := by
            rw [Category.assoc]
      _ = g ≫ h := by
            exact congrArg (fun q => q ≫ h) H.target_eq

namespace pathSpace

private lemma srcContraction_path_src_aux (P : SSet.{u}) :
    (λ_ (coherentIso ⊗ P)).inv ≫
        ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ (coherentIso ⊗ P)) ≫
        (α_ coherentIso coherentIso P).inv ≫
        ((β_ coherentIso coherentIso).hom ▷ P) ≫
        (coherentIso.srcContraction ▷ P) =
      CartesianMonoidalCategory.snd coherentIso P ≫
        (λ_ P).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ P) := by
  have hsymm : ∀ {m : ℕ} (g : Fin (m + 1) → WalkingIso.{u}) (j : Fin (m + 1)),
      (coherentIso.equivFun.symm g).obj j = g j := fun _ _ => rfl
  ext n x
  · cases n using Opposite.rec with
    | op n =>
      simp [coherentIso.srcContraction, hsymm]
      split <;> rfl
  · aesop_cat

/-- Evaluating the source contraction of `coherentIso` on paths in `X`. -/
noncomputable def srcContractionEval (X : SSet.{u}) :
    coherentIso ⊗ pathSpace (I := coherentIso) X ⟶ pathSpace (I := coherentIso) X :=
  MonoidalClosed.curry
    ((α_ coherentIso coherentIso (pathSpace (I := coherentIso) X)).inv ≫
      ((β_ coherentIso coherentIso).hom ▷ pathSpace (I := coherentIso) X) ≫
      (coherentIso.srcContraction ▷ pathSpace (I := coherentIso) X) ≫
      (ihom.ev coherentIso).app X)

set_option backward.isDefEq.respectTransparency false in
/-- The contraction of coherent-isomorphism paths keeps the source endpoint fixed. -/
lemma srcContractionEval_path_src (X : SSet.{u}) :
    srcContractionEval X ≫ pathSpace.src (I := coherentIso) X =
      CartesianMonoidalCategory.snd coherentIso (pathSpace (I := coherentIso) X) ≫
        pathSpace.src (I := coherentIso) X := by
  let P : SSet.{u} := pathSpace (I := coherentIso) X
  let G : coherentIso ⊗ P ⟶ pathSpace (I := coherentIso) X := srcContractionEval X
  change G ≫ (MonoidalClosed.pre coherentIso.src).app X ≫ X.expPointIsoSelf.hom =
    CartesianMonoidalCategory.snd coherentIso P ≫
      ((MonoidalClosed.pre coherentIso.src).app X ≫ X.expPointIsoSelf.hom)
  dsimp [G, srcContractionEval]
  rw [SSet.curry_endpoint_eval]
  change
    (((λ_ (coherentIso ⊗ P)).inv ≫
        ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ (coherentIso ⊗ P)) ≫
        (α_ coherentIso coherentIso P).inv ≫
        ((β_ coherentIso coherentIso).hom ▷ P) ≫
        (coherentIso.srcContraction ▷ P)) ≫ (ihom.ev coherentIso).app X) =
      ((CartesianMonoidalCategory.snd coherentIso P ≫
        (λ_ P).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ P)) ≫
        (ihom.ev coherentIso).app X)
  exact congrArg (fun q => q ≫ (ihom.ev coherentIso).app X)
    (srcContraction_path_src_aux P)

set_option backward.isDefEq.respectTransparency false in
/-- The source endpoint of `srcContractionEval` is source evaluation followed by constants. -/
lemma srcContractionEval_src (X : SSet.{u}) :
    (λ_ (pathSpace (I := coherentIso) X)).inv ≫
      ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ pathSpace (I := coherentIso) X) ≫
      srcContractionEval X =
    pathSpace.src (I := coherentIso) X ≫ pathSpace.const (I := coherentIso) X := by
  change (λ_ ((ihom coherentIso).obj X)).inv ≫
      ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ (ihom coherentIso).obj X) ≫
      srcContractionEval X =
    ((MonoidalClosed.pre coherentIso.src).app X ≫ X.expPointIsoSelf.hom) ≫
      (X.expPointIsoSelf.inv ≫
        (MonoidalClosed.pre (isTerminalDeltaZero.from coherentIso : coherentIso ⟶ Δ[0])).app X)
  slice_rhs 2 3 => rw [Iso.hom_inv_id]
  simp only [Category.id_comp]
  let P : SSet.{u} := (ihom coherentIso).obj X
  let a : P ⟶ coherentIso ⊗ P :=
    (λ_ P).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.src) ▷ P)
  let G : coherentIso ⊗ (coherentIso ⊗ P) ⟶ X :=
    (α_ coherentIso coherentIso P).inv ≫
      ((β_ coherentIso coherentIso).hom ▷ P) ≫
      (coherentIso.srcContraction ▷ P) ≫
      (ihom.ev coherentIso).app X
  change a ≫ MonoidalClosed.curry G =
    (MonoidalClosed.pre coherentIso.src).app X ≫
      (MonoidalClosed.pre (isTerminalDeltaZero.from coherentIso : coherentIso ⟶ Δ[0])).app X
  apply MonoidalClosed.uncurry_injective (A := coherentIso)
  change MonoidalClosed.uncurry (a ≫ MonoidalClosed.curry G) =
    MonoidalClosed.uncurry ((MonoidalClosed.pre coherentIso.src).app X ≫
      (MonoidalClosed.pre (isTerminalDeltaZero.from coherentIso : coherentIso ⟶ Δ[0])).app X)
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_pre_app]
  dsimp [a, G, P]
  simp [MonoidalClosed.uncurry_curry]
  ext n x
  cases n using Opposite.rec
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The target endpoint of `srcContractionEval` is the identity. -/
lemma srcContractionEval_tgt (X : SSet.{u}) :
    (λ_ (pathSpace (I := coherentIso) X)).inv ≫
      ((SSet.pointIsUnit.inv ≫ coherentIso.tgt) ▷ pathSpace (I := coherentIso) X) ≫
      srcContractionEval X = 𝟙 (pathSpace (I := coherentIso) X) := by
  change (λ_ ((ihom coherentIso).obj X)).inv ≫
      ((SSet.pointIsUnit.inv ≫ coherentIso.tgt) ▷ (ihom coherentIso).obj X) ≫
      srcContractionEval X = 𝟙 ((ihom coherentIso).obj X)
  let P : SSet.{u} := (ihom coherentIso).obj X
  let a : P ⟶ coherentIso ⊗ P :=
    (λ_ P).inv ≫ ((SSet.pointIsUnit.inv ≫ coherentIso.tgt) ▷ P)
  let G : coherentIso ⊗ (coherentIso ⊗ P) ⟶ X :=
    (α_ coherentIso coherentIso P).inv ≫
      ((β_ coherentIso coherentIso).hom ▷ P) ≫
      (coherentIso.srcContraction ▷ P) ≫
      (ihom.ev coherentIso).app X
  change a ≫ MonoidalClosed.curry G = 𝟙 P
  apply MonoidalClosed.uncurry_injective (A := coherentIso)
  change MonoidalClosed.uncurry (a ≫ MonoidalClosed.curry G) =
    MonoidalClosed.uncurry (𝟙 ((ihom coherentIso).obj X))
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_id_eq_ev]
  dsimp [a, G, P]
  simp [MonoidalClosed.uncurry_curry]
  ext n x
  cases n using Opposite.rec
  rfl

/-- Source evaluation from the coherent-isomorphism path space is a homotopy equivalence. -/
noncomputable def srcLeftHomotopy (X : SSet.{u}) :
    Homotopy (I := coherentIso)
      (pathSpace.src (I := coherentIso) X ≫ pathSpace.const (I := coherentIso) X)
      (𝟙 (pathSpace (I := coherentIso) X)) where
  homotopy := MonoidalClosed.curry (srcContractionEval X)
  source_eq := by
    change MonoidalClosed.curry (srcContractionEval X) ≫
        (MonoidalClosed.pre coherentIso.src).app (pathSpace (I := coherentIso) X) ≫
        (pathSpace (I := coherentIso) X).expPointIsoSelf.hom =
      pathSpace.src (I := coherentIso) X ≫ pathSpace.const (I := coherentIso) X
    rw [SSet.curry_endpoint_eval]
    exact srcContractionEval_src X
  target_eq := by
    change MonoidalClosed.curry (srcContractionEval X) ≫
        (MonoidalClosed.pre coherentIso.tgt).app (pathSpace (I := coherentIso) X) ≫
        (pathSpace (I := coherentIso) X).expPointIsoSelf.hom =
      𝟙 (pathSpace (I := coherentIso) X)
    rw [SSet.curry_endpoint_eval]
    exact srcContractionEval_tgt X

end pathSpace

/-- For the correct interval, this defines a good notion of equivalences for both Kan complexes and quasi-categories.-/
structure Equiv (A B : SSet.{u}) : Type u where
  toFun : A ⟶ B
  invFun : B ⟶ A
  left_inv : Homotopy (I := I) (toFun ≫ invFun) (𝟙 A)
  right_inv : Homotopy (I := I) (invFun ≫ toFun) (𝟙 B)

namespace Equiv

/-- Transport a simplicial homotopy equivalence across strict isomorphisms. -/
noncomputable def congrIso {A B A' B' : SSet.{u}} (eA : A' ≅ A) (eB : B' ≅ B)
    (e : Equiv (I := I) A B) : Equiv (I := I) A' B' where
  toFun := eA.hom ≫ e.toFun ≫ eB.inv
  invFun := eB.hom ≫ e.invFun ≫ eA.inv
  left_inv := by
    have H := (e.left_inv.precomp eA.hom).postcomp eA.inv
    convert H using 1
    · simp
    · simp
  right_inv := by
    have H := (e.right_inv.precomp eB.hom).postcomp eB.inv
    convert H using 1
    · simp
    · simp

end Equiv

namespace pathSpace

/-- Source evaluation from the coherent-isomorphism path space is a homotopy equivalence. -/
noncomputable def srcEquiv (X : SSet.{u}) :
    SSet.Equiv (I := coherentIso) (pathSpace (I := coherentIso) X) X where
  toFun := pathSpace.src (I := coherentIso) X
  invFun := pathSpace.const (I := coherentIso) X
  left_inv := srcLeftHomotopy X
  right_inv := by
    rw [pathSpace.const_src (I := coherentIso) X]
    exact Homotopy.refl (I := coherentIso) (𝟙 X)

end pathSpace

end

end SSet

namespace Kan

open SSet Simplicial

attribute [blueprint
  "defn:kan-complex"
  (title := "Kan complex")
  (statement := /--
  A \textbf{Kan complex} is a simplicial set admitting extensions as in \eqref{eq:qcat-defn} along
  all horn inclusions $n \geq 1, 0 \leq k \leq n$.
  -/)]
  KanComplex

/-- Equivalence of Kan Complexes. -/
@[nolint unusedArguments]
def Equiv (A B : SSet.{u}) [KanComplex A] [KanComplex B] :=
    SSet.Equiv (I := Δ[1]) A B

end Kan

namespace QCat

open SSet

/-- Equivalence of quasi-categories. -/
@[nolint unusedArguments, blueprint
  "defn:qcat-equivalence"
  (title := "equivalences of quasi-categories")
  (statement := /--
  w=

    A map $f \colon A \to B$ between quasi-categories is an \textbf{equivalence} if it extends to
    the data of a ``homotopy equivalence'' with the free-living isomorphism $\iso$ serving as the
    interval: that is, if there exist maps $g \colon B \to A$,
    \begin{center}
    \begin{tikzcd} & A & &  & B \\ A \arrow[ur, equals] \arrow[dr, "gf"'] \arrow[r, "\alpha"] &
    A^\iso  \arrow[u, "\ev_0"'] \arrow[d, "\ev_1"] & \text{and} &  B \arrow[dr, equals] \arrow[r,
    "\beta"] \arrow[ur, "fg"] & B^\iso \arrow[u, "\ev_0"'] \arrow[d, "\ev_1"] \\ & A & &  & B
    \end{tikzcd}
    \end{center}
    We write ``$\we$'' to decorate equivalences and $A \simeq B$ to indicate the presence of an
    equivalence $A \we B$.
  -/)]
def Equiv (A B : SSet.{u}) [Quasicategory A] [Quasicategory B] :=
    SSet.Equiv (I := coherentIso) A B

end QCat


namespace SSet
section

open CategoryTheory Simplicial SimplexCategory

variable {A : SSet.{u}} (f g : A _⦋1⦌)

structure HomotopyL where
  simplex : A _⦋2⦌
  δ₀_eq : A.δ 0 simplex = A.σ 0 (A.δ 0 f)
  δ₁_eq : A.δ 1 simplex = g
  δ₂_eq : A.δ 2 simplex = f

structure HomotopyR where
  simplex : A _⦋2⦌
  δ₀_eq : A.δ 0 simplex = f
  δ₁_eq : A.δ 1 simplex = g
  δ₂_eq : A.δ 2 simplex = A.σ 0 (A.δ 1 f)

def HomotopicL : Prop :=
    Nonempty (HomotopyL f g)

def HomotopicR : Prop :=
    Nonempty (HomotopyR f g)

def HomotopyL.refl : HomotopyL f f where
  simplex := A.σ 1 f
  δ₀_eq := by
    change _ = (A.δ 0 ≫ A.σ 0) _
    rw [← A.δ_comp_σ_of_le (by simp)]; simp
  δ₁_eq := by
    change (A.σ 1 ≫ A.δ 1) _ = _
    rw [A.δ_comp_σ_self' (by simp)]; simp
  δ₂_eq := by
    change (A.σ 1 ≫ A.δ 2) _ = _
    rw [A.δ_comp_σ_succ' (by simp)]
    rfl

-- -- need a better name
-- noncomputable def HomotopyL.ofHomotopyLOfHomotopyL {f g h : A _⦋1⦌}
--   (H₁ : HomotopyL f g) (H₂ : HomotopyL f h) :
--     HomotopyL g h := by
--   let σ : (Λ[3, 1] : SSet.{u}) ⟶ A := sorry
--   let τ : A _⦋3⦌ := sorry
--     -- BUILD FAILS:
--     -- A.yonedaEquiv _ (Classical.choose $ Quasicategory.hornFilling
--     --   (by simp) (by simp [Fin.lt_iff_val_lt_val]) σ)
--   have τ₀ : A.δ 0 τ = (A.δ 0 ≫ A.σ 0≫ A.σ 0) g := sorry
--   have τ₂ : A.δ 2 τ = H₂.simplex := sorry
--   have τ₃ : A.δ 3 τ = H₁.simplex := sorry
--   use A.δ 1 τ
--   . change (A.δ 1 ≫ A.δ 0) _ = _
--     rw [A.δ_comp_δ' (by simp)]; simp [τ₀]
--     change (A.σ 0 ≫ A.δ 0) _ = _
--     rw [A.δ_comp_σ_self' (by simp)]; simp
--   . rw [← H₂.δ₁_eq, ← τ₂]
--     change _ = (A.δ 2 ≫ A.δ 1) _
--     rw [A.δ_comp_δ' (by simp)]; rfl
--   . rw [← H₁.δ₁_eq, ← τ₃]
--     change _ = (A.δ 3 ≫ A.δ 1) _
--     rw [A.δ_comp_δ' (by simp)]; rfl

-- lemma HomotopyL.equiv :
--     Equivalence (fun f g : A _⦋1⦌ ↦ HomotopicL f g) where
--   refl f := ⟨HomotopyL.refl f⟩
--   symm := by
--     intro f g ⟨H⟩
--     exact ⟨H.ofHomotopyLOfHomotopyL (HomotopyL.refl f)⟩
--   trans := by
--     intro f g h ⟨H₁⟩ ⟨H₂⟩
--     exact ⟨(H₁.ofHomotopyLOfHomotopyL (HomotopyL.refl f)).ofHomotopyLOfHomotopyL H₂⟩

-- lemma homotopicL_iff_homotopicR [Quasicategory A] :
--     HomotopicL f g ↔ HomotopicR f g := sorry

-- lemma HomotopyR.equiv [Quasicategory A] :
--     Equivalence (fun f g : A _⦋1⦌ ↦ HomotopicR f g) := by
--   simp [← homotopicL_iff_homotopicR, HomotopyL.equiv]

end

end SSet
