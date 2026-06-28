/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JHU Category Theory Seminar
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Isofibrations

open scoped Simplicial

/-!
# Equivalences are homotopy equivalences

This file develops the blueprint lemma `lem:equiv-htpy-equiv` ("equivalences are homotopy
equivalences"): a map `f : A ⟶ B` between ∞-categories in an ∞-cosmos `K` is an equivalence if and
only if it extends to the data of a "homotopy equivalence" with the free-living isomorphism
`⟨iso⟩` (`SSet.coherentIso`) serving as the interval.

We package that data as `InfinityCosmos.HomotopyEquiv f`: a one-sided inverse `g : B ⟶ A`
together with cotensor-valued homotopies `α : A ⟶ coherentIso ⋔ₛ A` and `β : B ⟶ coherentIso ⋔ₛ B`
whose evaluations at the two endpoints `ev₀`, `ev₁` of `⟨iso⟩` give
`ev₀ ∘ α = 1_A`, `ev₁ ∘ α = g ∘ f`, `ev₀ ∘ β = f ∘ g`, `ev₁ ∘ β = 1_B`.

The main result here is the converse ("easy") direction of `lem:equiv-htpy-equiv`,
`HomotopyEquiv.equivalence`: such data makes `f` an equivalence. The argument is the Yoneda-style
observation that the simplicial cotensor commutes with each functor space `Fun(X, -)`, so applying
`representableMap X` to a homotopy equivalence produces a homotopy equivalence of quasi-categories
in the sense of `SSet.Equiv (I := coherentIso)`, i.e. a `QCat.Equiv`.

The forward direction ("equivalence implies homotopy-equivalence data") is the harder half of the
iff; it routes through the homotopy-category characterization of equivalences of quasi-categories
(`lem:qcat-htpy-cat-equiv`) and `SSet.coherentIso.lift` (`prop:coherent-iso`), and is not built
here.
-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos
open MonoidalCategory BraidedCategory MonoidalClosed

local notation3:1024 U:1024 " ⋔ₛ " A:1024 =>
  CategoryTheory.SimplicialCategory.cotensor.obj U A

variable {K : Type u} [Category.{v} K] [InfinityCosmos.{0} K]

/-- Source evaluation `ev₀ : A^⟨iso⟩ → A` of the coherent-isomorphism cotensor, landing in `A`
via the identification `Δ[0] ⋔ₛ A ≅ A`. -/
noncomputable def coherentIsoEv₀ (A : K) : SSet.coherentIso ⋔ₛ A ⟶ A :=
  cotensorContraMap SSet.coherentIso.src A ≫ cotensorPointIsoHom A

/-- Target evaluation `ev₁ : A^⟨iso⟩ → A` of the coherent-isomorphism cotensor, landing in `A`
via the identification `Δ[0] ⋔ₛ A ≅ A`. -/
noncomputable def coherentIsoEv₁ (A : K) : SSet.coherentIso ⋔ₛ A ⟶ A :=
  cotensorContraMap SSet.coherentIso.tgt A ≫ cotensorPointIsoHom A

/-- On the functor space `Fun(X, -)`, the cotensor comparison isomorphism followed by source
evaluation in the path space is `representableMap X ev₀`: the simplicial cotensor commutes with
`Fun(X, -)`. -/
lemma cotensorIso_hom_pathSpaceSrc (A X : K) :
    (cotensor.iso SSet.coherentIso A X).hom ≫
        SSet.pathSpace.src (I := SSet.coherentIso) (sHom X A) =
      representableMap X (coherentIsoEv₀ A) := by
  have hnat : representableMap X (cotensorContraMap SSet.coherentIso.src A) ≫
        (cotensor.iso (Δ[0] : SSet.{v}) A X).hom =
      (cotensor.iso SSet.coherentIso A X).hom ≫
        (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X A) :=
    cotensor_iso_hom_naturality_precompose SSet.coherentIso.src A X
  dsimp only [coherentIsoEv₀]
  rw [representableMap_comp, representableMap_cotensorPointIsoHom, ← Category.assoc, hnat,
    Category.assoc]
  rfl

/-- On the functor space `Fun(X, -)`, the cotensor comparison isomorphism followed by target
evaluation in the path space is `representableMap X ev₁`. -/
lemma cotensorIso_hom_pathSpaceTgt (A X : K) :
    (cotensor.iso SSet.coherentIso A X).hom ≫
        SSet.pathSpace.tgt (I := SSet.coherentIso) (sHom X A) =
      representableMap X (coherentIsoEv₁ A) := by
  have hnat : representableMap X (cotensorContraMap SSet.coherentIso.tgt A) ≫
        (cotensor.iso (Δ[0] : SSet.{v}) A X).hom =
      (cotensor.iso SSet.coherentIso A X).hom ≫
        (MonoidalClosed.pre SSet.coherentIso.tgt).app (sHom X A) :=
    cotensor_iso_hom_naturality_precompose SSet.coherentIso.tgt A X
  dsimp only [coherentIsoEv₁]
  rw [representableMap_comp, representableMap_cotensorPointIsoHom, ← Category.assoc, hnat,
    Category.assoc]
  rfl

/-- The data exhibiting a map `f : A ⟶ B` in an ∞-cosmos as a **homotopy equivalence** with the
free-living isomorphism `⟨iso⟩` as interval: a map `inv : B ⟶ A` together with cotensor-valued
homotopies `fwd : A ⟶ A^⟨iso⟩` and `bwd : B ⟶ B^⟨iso⟩` whose endpoint evaluations exhibit
`inv` as a two-sided homotopy inverse of `f`. -/
structure HomotopyEquiv {A B : K} (f : A ⟶ B) where
  /-- The homotopy inverse of `f`. -/
  inv : B ⟶ A
  /-- The coherent-isomorphism homotopy on `A`, from `1_A` to `inv ∘ f`. -/
  fwd : A ⟶ SSet.coherentIso ⋔ₛ A
  /-- The coherent-isomorphism homotopy on `B`, from `f ∘ inv` to `1_B`. -/
  bwd : B ⟶ SSet.coherentIso ⋔ₛ B
  /-- `ev₀ ∘ fwd = 1_A`. -/
  fwd_src : fwd ≫ coherentIsoEv₀ A = 𝟙 A
  /-- `ev₁ ∘ fwd = inv ∘ f` (in diagrammatic order `f ≫ inv`). -/
  fwd_tgt : fwd ≫ coherentIsoEv₁ A = f ≫ inv
  /-- `ev₀ ∘ bwd = f ∘ inv` (in diagrammatic order `inv ≫ f`). -/
  bwd_src : bwd ≫ coherentIsoEv₀ B = inv ≫ f
  /-- `ev₁ ∘ bwd = 1_B`. -/
  bwd_tgt : bwd ≫ coherentIsoEv₁ B = 𝟙 B

/-- The converse ("easy") direction of `lem:equiv-htpy-equiv`: a map equipped with the data of a
homotopy equivalence relative to `⟨iso⟩` is an equivalence in the ∞-cosmos. The simplicial cotensor
commutes with each functor space `Fun(X, -)`, so `representableMap X` carries the homotopy
equivalence data to an equivalence of quasi-categories. -/
theorem HomotopyEquiv.equivalence {A B : K} {f : A ⟶ B} (h : HomotopyEquiv f) :
    Equivalence f := by
  intro X
  haveI : SSet.Quasicategory (sHom X A) := (Fun X A).property
  have Hα_src : (representableMap X h.fwd ≫ (cotensor.iso SSet.coherentIso A X).hom) ≫
        SSet.pathSpace.src (I := SSet.coherentIso) (sHom X A) = 𝟙 (sHom X A) := by
    rw [Category.assoc, cotensorIso_hom_pathSpaceSrc A X, ← representableMap_comp, h.fwd_src,
      representableMap_id]
  have Hα_tgt : (representableMap X h.fwd ≫ (cotensor.iso SSet.coherentIso A X).hom) ≫
        SSet.pathSpace.tgt (I := SSet.coherentIso) (sHom X A) =
      representableMap X f ≫ representableMap X h.inv := by
    rw [Category.assoc, cotensorIso_hom_pathSpaceTgt A X, ← representableMap_comp, h.fwd_tgt,
      representableMap_comp]
  have Hβ_src : (representableMap X h.bwd ≫ (cotensor.iso SSet.coherentIso B X).hom) ≫
        SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) =
      representableMap X h.inv ≫ representableMap X f := by
    rw [Category.assoc, cotensorIso_hom_pathSpaceSrc B X, ← representableMap_comp, h.bwd_src,
      representableMap_comp]
  have Hβ_tgt : (representableMap X h.bwd ≫ (cotensor.iso SSet.coherentIso B X).hom) ≫
        SSet.pathSpace.tgt (I := SSet.coherentIso) (sHom X B) = 𝟙 (sHom X B) := by
    rw [Category.assoc, cotensorIso_hom_pathSpaceTgt B X, ← representableMap_comp, h.bwd_tgt,
      representableMap_id]
  let Hα : SSet.Homotopy (I := SSet.coherentIso) (𝟙 (sHom X A))
      (representableMap X f ≫ representableMap X h.inv) :=
    { homotopy := representableMap X h.fwd ≫ (cotensor.iso SSet.coherentIso A X).hom
      source_eq := Hα_src
      target_eq := Hα_tgt }
  let Hβ : SSet.Homotopy (I := SSet.coherentIso)
      (representableMap X h.inv ≫ representableMap X f) (𝟙 (sHom X B)) :=
    { homotopy := representableMap X h.bwd ≫ (cotensor.iso SSet.coherentIso B X).hom
      source_eq := Hβ_src
      target_eq := Hβ_tgt }
  let e : @QCat.Equiv (Fun X A).obj (Fun X B).obj (Fun X A).property (Fun X B).property :=
    { toFun := representableMap X f
      invFun := representableMap X h.inv
      left_inv := Hα.symm
      right_inv := Hβ }
  exact ⟨e, rfl⟩

end InfinityCosmos
