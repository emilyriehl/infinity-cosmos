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

namespace SSet

open CategoryTheory Simplicial SimplicialCategory MonoidalCategory MonoidalClosed

universe u

/-- **`lem:qcat-htpy-cat-equiv` (faithfulness on the homotopy category).** An equivalence of
quasi-categories `e : C ≃ D` reflects homotopies: if two maps `u, v : A ⟶ C` become homotopic
after composing with `e.toFun`, then they are already homotopic. Equivalently, the induced functor
`ho(C) ⥤ ho(D)` is faithful (and, by `Equiv.symm`, conservative): a `coherentIso`-homotopy between
`e ∘ u` and `e ∘ v` descends to one between `u` and `v` by transporting along the homotopy inverse
`e.invFun` and the left-inverse homotopy `e.left_inv`. -/
noncomputable def Equiv.reflectsHomotopy {C D : SSet.{u}} [Quasicategory C]
    (e : SSet.Equiv (I := coherentIso) C D) {A : SSet.{u}} {u v : A ⟶ C}
    (H : Homotopy (I := coherentIso) (u ≫ e.toFun) (v ≫ e.toFun)) :
    Homotopy (I := coherentIso) u v := by
  have h1 : Homotopy (I := coherentIso) ((u ≫ e.toFun) ≫ e.invFun) u := by
    have H' := e.left_inv.precomp u
    convert H' using 1
    · rw [Category.assoc]
    · rw [Category.comp_id]
  have h2 : Homotopy (I := coherentIso)
      ((u ≫ e.toFun) ≫ e.invFun) ((v ≫ e.toFun) ≫ e.invFun) := H.postcomp e.invFun
  have h3 : Homotopy (I := coherentIso) ((v ≫ e.toFun) ≫ e.invFun) v := by
    have H' := e.left_inv.precomp v
    convert H' using 1
    · rw [Category.assoc]
    · rw [Category.comp_id]
  exact (h1.symm).trans (h2.trans h3)

/-- The point-evaluation isomorphism `sHom Δ[0] Z ≅ Z` composed after the name of a map
`g : Δ[0] ⟶ Z` returns `g`. -/
lemma eHomEquiv_comp_expPointIsoSelf {Z : SSet.{u}} (g : Δ[0] ⟶ Z) :
    eHomEquiv SSet g ≫ (expPointIsoSelf Z).hom = SSet.pointIsUnit.inv ≫ g := by
  ext n a
  aesop_cat

private lemma deltaZeroZero_subsingleton (a b : (Δ[0] : SSet.{u}) _⦋0⦌) : a = b := by
  apply (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := Opposite.op ⦋0⦌)).injective
  apply SimplexCategory.Hom.ext
  ext x
  have ha : ((SSet.stdSimplex.objEquiv a).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  have hb : ((SSet.stdSimplex.objEquiv b).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  rw [ha, hb]

/-- The point-evaluation isomorphism `sHom Δ[0] Z ≅ Z` reads a `0`-simplex of `sHom Δ[0] Z`,
viewed via `homEquiv'` as a map `Δ[0] ⟶ Z`, as the `0`-simplex of `Z` it names. -/
lemma expPointIsoSelf_hom_homEquiv' {Z : SSet.{u}} (u : Δ[0] ⟶ Z) :
    (expPointIsoSelf Z).hom.app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' Δ[0] Z u) = SSet.yonedaEquiv u := by
  have h0 : SimplicialCategory.homEquiv' Δ[0] Z u
      = (eHomEquiv SSet u).app (Opposite.op ⦋0⦌) PUnit.unit := rfl
  rw [h0, ← NatTrans.comp_app_apply, eHomEquiv_comp_expPointIsoSelf,
    show SSet.yonedaEquiv u = u.app _ (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) from by
      rw [← SSet.yonedaEquiv_comp, Category.id_comp]]
  rw [NatTrans.comp_app_apply]
  congr 1
  apply deltaZeroZero_subsingleton

/-- A `coherentIso`-homotopy between two vertices `u v : Δ[0] ⟶ C` internalises to a map
`coherentIso ⟶ C`, i.e. an invertible arrow of `C` from `u` to `v`. -/
noncomputable def Homotopy.toCoherentIsoMap₀ {C : SSet.{u}} {u v : Δ[0] ⟶ C}
    (H : Homotopy (I := coherentIso) u v) : coherentIso ⟶ C :=
  H.toCoherentIsoMap ≫ (expPointIsoSelf C).hom

/-- The source endpoint of `toCoherentIsoMap₀` is the `0`-arrow `u`. -/
lemma Homotopy.toCoherentIsoMap₀_src {C : SSet.{u}} {u v : Δ[0] ⟶ C}
    (H : Homotopy (I := coherentIso) u v) :
    SSet.yonedaEquiv (coherentIso.src ≫ H.toCoherentIsoMap₀) = SSet.yonedaEquiv u := by
  have hu : SSet.yonedaEquiv (coherentIso.src ≫ H.toCoherentIsoMap)
      = SimplicialCategory.homEquiv' Δ[0] C u := by
    apply (SimplicialCategory.homEquiv' Δ[0] C).symm.injective
    rw [Equiv.symm_apply_apply]
    exact H.toCoherentIsoMap_src
  rw [Homotopy.toCoherentIsoMap₀, ← Category.assoc, SSet.yonedaEquiv_comp, hu]
  exact expPointIsoSelf_hom_homEquiv' u

/-- The target endpoint of `toCoherentIsoMap₀` is the `0`-arrow `v`. -/
lemma Homotopy.toCoherentIsoMap₀_tgt {C : SSet.{u}} {u v : Δ[0] ⟶ C}
    (H : Homotopy (I := coherentIso) u v) :
    SSet.yonedaEquiv (coherentIso.tgt ≫ H.toCoherentIsoMap₀) = SSet.yonedaEquiv v := by
  have hv : SSet.yonedaEquiv (coherentIso.tgt ≫ H.toCoherentIsoMap)
      = SimplicialCategory.homEquiv' Δ[0] C v := by
    apply (SimplicialCategory.homEquiv' Δ[0] C).symm.injective
    rw [Equiv.symm_apply_apply]
    exact H.toCoherentIsoMap_tgt
  rw [Homotopy.toCoherentIsoMap₀, ← Category.assoc, SSet.yonedaEquiv_comp, hv]
  exact expPointIsoSelf_hom_homEquiv' v

end SSet

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

/-- Post-composing with the point-cotensor comparison `Δ[0] ⋔ₛ B ≅ B` reads off the 0-simplex of
`sHom B' B` named by `cotensor.iso.underlying`: that is, `cotensorPointIsoHom` is the inverse of
the point-cotensor identification at the level of vertices. -/
lemma cotensorPointIsoHom_underlying {B' B : K} (δ : B' ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B) :
    δ ≫ cotensorPointIsoHom B =
      (homEquiv' B' B).symm
        (SSet.yonedaEquiv ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B B') δ)) := by
  apply (eHomEquiv SSet).injective
  rw [← eHomEquiv_comp_eHomWhiskerRight, cotensorPointIsoHom_homEquiv]
  have hrhs : eHomEquiv SSet
      ((homEquiv' B' B).symm
        (SSet.yonedaEquiv ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B B') δ))) =
      SSet.pointIsUnit.inv ≫ (cotensor.iso.underlying (Δ[0] : SSet.{v}) B B') δ := by
    have hsymm : (homEquiv' B' B).symm
        (SSet.yonedaEquiv ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B B') δ)) =
        (eHomEquiv SSet).symm
          ((SSet.unitHomEquiv (sHom B' B)).symm
            (SSet.yonedaEquiv ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B B') δ))) := rfl
    rw [hsymm, Equiv.apply_symm_apply, SSet.unitHomEquiv_symm_yonedaEquiv]
  rw [hrhs, cotensor_iso_underlying_eq_cone]
  change (SSet.pointIsUnit.inv ≫ cotensor.cone (Δ[0] : SSet.{v}) B) ≫
      eHomWhiskerRight SSet δ B =
    SSet.pointIsUnit.inv ≫
      (getCotensor (Δ[0] : SSet.{v}) B).cone ≫ eHomWhiskerRight SSet δ B
  rw [Category.assoc]
  rfl

/-- The source endpoint of an internalised coherent-isomorphism homotopy. If `β` is the morphism
`B ⟶ coherentIso ⋔ₛ B` named by `Ft : coherentIso ⟶ sHom B B`, then `ev₀ ∘ β` is the 0-arrow
`coherentIso.src ≫ Ft` of `Fun(B, B)`. -/
lemma coherentIsoEv₀_underlying (B : K) (Ft : SSet.coherentIso ⟶ sHom B B) :
    (cotensor.iso.underlying SSet.coherentIso B B).symm Ft ≫ coherentIsoEv₀ B =
      (homEquiv' B B).symm (SSet.yonedaEquiv (SSet.coherentIso.src ≫ Ft)) := by
  set β := (cotensor.iso.underlying SSet.coherentIso B B).symm Ft with hβ
  rw [coherentIsoEv₀, ← Category.assoc, cotensorPointIsoHom_underlying]
  congr 2
  have hpre := cotensor_iso_underlying_precompose SSet.coherentIso.src B B β
  rw [hpre, hβ, Equiv.apply_symm_apply]

/-- The target endpoint of an internalised coherent-isomorphism homotopy. -/
lemma coherentIsoEv₁_underlying (B : K) (Ft : SSet.coherentIso ⟶ sHom B B) :
    (cotensor.iso.underlying SSet.coherentIso B B).symm Ft ≫ coherentIsoEv₁ B =
      (homEquiv' B B).symm (SSet.yonedaEquiv (SSet.coherentIso.tgt ≫ Ft)) := by
  set β := (cotensor.iso.underlying SSet.coherentIso B B).symm Ft with hβ
  rw [coherentIsoEv₁, ← Category.assoc, cotensorPointIsoHom_underlying]
  congr 2
  have hpre := cotensor_iso_underlying_precompose SSet.coherentIso.tgt B B β
  rw [hpre, hβ, Equiv.apply_symm_apply]

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

/-! ### The forward direction: an equivalence is a homotopy equivalence -/

/-- A `0`-arrow `k : X ⟶ A` viewed as a vertex `Δ[0] ⟶ Fun(X, A)` of the functor space. -/
noncomputable def vtx {X A : K} (k : X ⟶ A) : (Δ[0] : SSet.{v}) ⟶ sHom X A :=
  SSet.yonedaEquiv.symm (homEquiv' X A k)

@[simp]
lemma yonedaEquiv_vtx {X A : K} (k : X ⟶ A) :
    SSet.yonedaEquiv (vtx k) = homEquiv' X A k := by
  rw [vtx, Equiv.apply_symm_apply]

/-- Whiskering on the left realises postcomposition on the named vertex. -/
lemma eHomEquiv_comp_eHomWhiskerLeft {X A B : K} (k : X ⟶ A) (g : A ⟶ B) :
    eHomEquiv SSet k ≫ eHomWhiskerLeft SSet X g = eHomEquiv SSet (k ≫ g) := by
  rw [eHomWhiskerLeft, eHomEquiv_comp]
  simp only [tensorHom_def, Category.assoc, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, MonoidalCategory.whisker_assoc]
  rfl

/-- The covariant representable sends the vertex of `k` to the vertex of `k ≫ g`. -/
lemma vtx_postcomp {X A B : K} (k : X ⟶ A) (g : A ⟶ B) :
    vtx k ≫ representableMap X g = vtx (k ≫ g) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, yonedaEquiv_vtx, yonedaEquiv_vtx]
  change (eHomWhiskerLeft SSet X g).app _ ((eHomEquiv SSet k).app _ PUnit.unit) = _
  rw [← NatTrans.comp_app_apply, eHomEquiv_comp_eHomWhiskerLeft]
  rfl

/-- The contravariant representable sends the vertex of `g` to the vertex of `h ≫ g`. -/
lemma vtx_precomp {X Y Z : K} (h : X ⟶ Y) (g : Y ⟶ Z) :
    vtx g ≫ sHomWhiskerRight h Z = vtx (h ≫ g) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, yonedaEquiv_vtx, yonedaEquiv_vtx]
  exact (homEquiv'_comp h g).symm

/-- **Forward direction of `lem:equiv-htpy-equiv` (`lem:equivadj`).** An equivalence `f` in an
∞-cosmos extends to the data of a homotopy equivalence with `⟨iso⟩` as interval. The homotopy
inverse `g` is named by the inverse equivalence on `Fun(B, -)` applied to `id_B`; the homotopy
`β : f ∘ g ⇒ 1_B` comes from the right-inverse homotopy of `Fun(B, f)` at `id_B`; and the homotopy
`α : 1_A ⇒ g ∘ f` is produced from `β` by transport along `f` and the faithfulness of
`Fun(A, f)` on the homotopy category (`SSet.Equiv.reflectsHomotopy`, i.e.
`lem:qcat-htpy-cat-equiv`). -/
noncomputable def Equivalence.homotopyEquiv {A B : K} {f : A ⟶ B} (hf : Equivalence f) :
    HomotopyEquiv f := by
  haveI hqBB : SSet.Quasicategory (sHom B B) := (Fun B B).property
  haveI hqBA : SSet.Quasicategory (sHom B A) := (Fun B A).property
  haveI hqAA : SSet.Quasicategory (sHom A A) := (Fun A A).property
  haveI hqAB : SSet.Quasicategory (sHom A B) := (Fun A B).property
  let eB : SSet.Equiv (I := SSet.coherentIso) (sHom B A) (sHom B B) := Classical.choose (hf B)
  let eA : SSet.Equiv (I := SSet.coherentIso) (sHom A A) (sHom A B) := Classical.choose (hf A)
  have heB : eB.toFun = representableMap B f := Classical.choose_spec (hf B)
  have heA : eA.toFun = representableMap A f := Classical.choose_spec (hf A)
  -- The homotopy inverse, named by `eB.invFun (id_B)`.
  set g : B ⟶ A :=
    (homEquiv' B A).symm (SSet.yonedaEquiv (vtx (𝟙 B) ≫ eB.invFun)) with hg
  have hgvtx : vtx g = vtx (𝟙 B) ≫ eB.invFun := by
    show SSet.yonedaEquiv.symm (homEquiv' B A g) = vtx (𝟙 B) ≫ eB.invFun
    rw [hg, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  -- The homotopy `β`, internalised as a homotopy of vertices of `Fun(B, B)`.
  have hub : vtx (𝟙 B) ≫ (eB.invFun ≫ eB.toFun) = vtx (g ≫ f) := by
    rw [heB, ← Category.assoc, ← hgvtx]
    exact vtx_postcomp g f
  have hvb : vtx (𝟙 B) ≫ 𝟙 (sHom B B) = vtx (𝟙 B) := Category.comp_id _
  have Hbwd : SSet.Homotopy (I := SSet.coherentIso) (vtx (g ≫ f)) (vtx (𝟙 B)) := by
    convert eB.right_inv.precomp (vtx (𝟙 B)) using 2
    · exact hub.symm
    · exact hvb.symm
  -- Transport `β` along `f` and reflect through `Fun(A, f)` to obtain `α`.
  have hs : vtx (g ≫ f) ≫ sHomWhiskerRight f B = vtx (f ≫ g ≫ f) := vtx_precomp f (g ≫ f)
  have ht : vtx (𝟙 B) ≫ sHomWhiskerRight f B = vtx f :=
    (vtx_precomp f (𝟙 B)).trans (by rw [Category.comp_id])
  have Ka : SSet.Homotopy (I := SSet.coherentIso)
      (vtx (𝟙 A) ≫ eA.toFun) (vtx (f ≫ g) ≫ eA.toFun) := by
    have hua : vtx (𝟙 A) ≫ eA.toFun = vtx f := by
      rw [heA]
      exact (vtx_postcomp (𝟙 A) f).trans (by rw [Category.id_comp])
    have hva : vtx (f ≫ g) ≫ eA.toFun = vtx (f ≫ g ≫ f) := by
      rw [heA]
      exact (vtx_postcomp (f ≫ g) f).trans (by rw [Category.assoc])
    rw [hua, hva]
    convert (Hbwd.postcomp (sHomWhiskerRight f B)).symm using 2
    · exact ht.symm
    · exact hs.symm
  have Hfwd : SSet.Homotopy (I := SSet.coherentIso) (vtx (𝟙 A)) (vtx (f ≫ g)) :=
    eA.reflectsHomotopy Ka
  refine
    { inv := g
      bwd := (cotensor.iso.underlying SSet.coherentIso B B).symm Hbwd.toCoherentIsoMap₀
      fwd := (cotensor.iso.underlying SSet.coherentIso A A).symm Hfwd.toCoherentIsoMap₀
      fwd_src := ?_
      fwd_tgt := ?_
      bwd_src := ?_
      bwd_tgt := ?_ }
  · rw [coherentIsoEv₀_underlying, Hfwd.toCoherentIsoMap₀_src, yonedaEquiv_vtx,
      Equiv.symm_apply_apply]
  · rw [coherentIsoEv₁_underlying, Hfwd.toCoherentIsoMap₀_tgt, yonedaEquiv_vtx,
      Equiv.symm_apply_apply]
  · rw [coherentIsoEv₀_underlying, Hbwd.toCoherentIsoMap₀_src, yonedaEquiv_vtx,
      Equiv.symm_apply_apply]
  · rw [coherentIsoEv₁_underlying, Hbwd.toCoherentIsoMap₀_tgt, yonedaEquiv_vtx,
      Equiv.symm_apply_apply]

/-- **`lem:equiv-htpy-equiv` (issue #116).** A map `f` in an ∞-cosmos is an equivalence if and only
if it underlies the data of a homotopy equivalence with the free-living isomorphism as interval. -/
theorem equivalence_iff_nonempty_homotopyEquiv {A B : K} (f : A ⟶ B) :
    Equivalence f ↔ Nonempty (HomotopyEquiv f) :=
  ⟨fun hf => ⟨Equivalence.homotopyEquiv hf⟩, fun ⟨h⟩ => HomotopyEquiv.equivalence h⟩

end InfinityCosmos
