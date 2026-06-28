/-
The `i = last` special-outer-horn filler, assembled.

Builds on the outer-horn / Leibniz-join arrow-iso (M11) and the coslice Leibniz
filler (M10) to produce, for a quasicategory `A`:
  * `cancelComp_left/right` (edge-iso cancellation), `isIsoSimplex_δ₀/δ₂_of_outer`;
  * `SpecialOuterHorn.initialEdge` / `finalEdge`;
  * `filler_mem_isoCore_outer`, `isoCore_outerHornFiller_of_producer` (the producer);
  * `fillerLast`, `fillBase`, and `SpecialOuterHorn.fill_last` (Kerodon 019F, i = last).
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.SpecialOuterHornFillerLeibniz
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.OuterHornLastDecomposition
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CosliceProjLeftFibration
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCoreKan
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

open CategoryTheory Simplicial Opposite Finset SSet.Truncated SimplexCategory.Truncated Limits MorphismProperty AugmentedSimplexCategory

universe u

namespace SSet

/-! ## Horn-form transport scaffolding for the `n ≥ 1` case (steps 2). -/

abbrev jbM (M : ℕ) := (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
abbrev gfM := (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι
abbrev gdM : (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) := stdSimplex.δ (0 : Fin 2)

/-- The face-form `{0}ᶜ ↪ Δ[1]` to `δ0`-form arrow-iso. -/
noncomputable def bridgeM : Arrow.mk (gfM.{u}) ≅ Arrow.mk (gdM.{u}) :=
  Arrow.isoMk (stdSimplex.faceSingletonComplIso (0 : Fin 2)).symm (Iso.refl _) (by
    have hfac : (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι =
        (stdSimplex.faceSingletonComplIso (0 : Fin 2)).inv ≫ stdSimplex.δ (0 : Fin 2) := by
      rw [← boundary.ι_ι (0 : Fin 2), ← Category.assoc,
        boundary.faceSingletonComplIso_inv_ι (0 : Fin 2)]
      exact (boundary.faceι_ι (0 : Fin 2)).symm
    simp only [Arrow.mk_hom, Iso.symm_hom]
    exact hfac.symm)

/-- The `sqLeibCo`-form face→δ0 bridge, via `ι_iso_of_iso_right`. -/
noncomputable def cornerBridgeM (M : ℕ) :
    Arrow.mk (sqLeibCo (jbM.{u} M) (gfM.{u})).ι ≅ Arrow.mk (sqLeibCo (jbM.{u} M) (gdM.{u})).ι :=
  Functor.PushoutObjObj.ι_iso_of_iso_right
    (F := joinFunctor) (f₁ := Arrow.mk (jbM.{u} M))
    (f₂ := Arrow.mk (gfM.{u})) (f₂' := Arrow.mk (gdM.{u}))
    (sqLeibCo (jbM.{u} M) (gfM.{u})) (sqLeibCo (jbM.{u} M) (gdM.{u})) bridgeM.{u}

/-- The full horn-form transport: `Λ[M+3,last].ι ≅ (sqLeibCo (∂Δ[M+1].ι) δ0).ι`. -/
noncomputable def transM (M : ℕ) :
    Arrow.mk (Λ[M + 1 + 1 + 1, joinRightVertex (M + 1) 1 1].ι) ≅
      Arrow.mk (sqLeibCo (jbM.{u} M) (gdM.{u})).ι :=
  (outerHornLast_iso_leibnizJoin.{u} M) ≪≫
    (cornerIso (jbM.{u} M) (gfM.{u})) ≪≫
    (cornerBridgeM.{u} M)

/-- `transM` retyped with the missing vertex as `Fin.last` (defeq to `joinRightVertex (M+1) 1 1`). -/
noncomputable def transLast (M : ℕ) :
    Arrow.mk (Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι) ≅
      Arrow.mk (sqLeibCo (jbM.{u} M) (gdM.{u})).ι :=
  transM.{u} M

lemma arrowMk_iso_hom_right {X Y : SSet.{u}} (g : X ⟶ Y) [Mono g]
    {A : Y.Subcomplex} (h : Subcomplex.range g = A) :
    (arrowMk_iso_of_mono_range g h).hom.right = 𝟙 Y := by
  subst h; simp [arrowMk_iso_of_mono_range, Arrow.isoMk']

lemma outerHornLast_inv_right (M : ℕ) :
    (outerHornLast_iso_leibnizJoin.{u} M).inv.right = (joinStdSimplex.{u} (M+1) 1).hom := by
  haveI := genCellOuterLast_mono.{u} M
  haveI : Mono (leibnizJoin (jbM.{u} M) (gfM.{u}) ≫ (joinStdSimplex.{u} (M+1) 1).hom) :=
    inferInstance
  have harrow : (arrowMk_iso_of_mono_range
      (leibnizJoin (jbM.{u} M) (gfM.{u}) ≫ (joinStdSimplex.{u} (M+1) 1).hom)
      (genCellOuterLast_range_image_identity.{u} M)).hom.right = 𝟙 _ :=
    arrowMk_iso_hom_right _ _
  show (genCellOuterLast_iso_targetHornOuterLast.{u} M).hom.right = _
  unfold genCellOuterLast_iso_targetHornOuterLast
  simp only [Iso.trans_hom, Arrow.comp_right, Arrow.isoMk_hom_right, harrow]
  exact Category.comp_id _

lemma cornerBridge_inv_right (M : ℕ) : (cornerBridgeM.{u} M).inv.right = 𝟙 _ := by
  unfold cornerBridgeM
  simp only [Functor.PushoutObjObj.ι_iso_of_iso_right_inv, Functor.PushoutObjObj.mapArrowRight_right,
    bridgeM, Arrow.isoMk_inv_right, Iso.refl_inv]
  exact CategoryTheory.Functor.map_id _ _

lemma cornerIso_inv_right (M : ℕ) : (cornerIso (jbM.{u} M) (gfM.{u})).inv.right = 𝟙 _ := by
  simp only [cornerIso, Iso.trans_inv, Arrow.comp_right, pushoutObjObj_ι_arrowIso,
    Arrow.isoMk_inv_right, Iso.refl_inv, eqToIso.inv, Arrow.eqToHom_right, Category.id_comp]
  rfl

lemma einv_right (M : ℕ) :
    (transLast.{u} M).inv.right = (joinStdSimplex.{u} (M+1) 1).hom := by
  unfold transLast transM
  simp only [Iso.trans_inv, Arrow.comp_right, outerHornLast_inv_right, cornerBridge_inv_right,
    cornerIso_inv_right]
  cat_disch

attribute [irreducible] transLast

/-! ## Replay of the 2-out-of-3 duals brick (isoduals_1.lean)

These are proven in `/Users/robsneiderman/Desktop/n5-bricks/isoduals_1.lean`; replayed here
verbatim since the brick is scratch (not yet in the tracked tree). -/

namespace Edge

namespace IsIso

variable {X : SSet} [Quasicategory X] {x₀ x₁ x₂ : X _⦋0⦌}

/-- In the homotopy category, an iso edge composes with its inverse to the identity. -/
lemma homMk_comp_inv {e : Edge x₀ x₁} (I : IsIso e) :
    HomotopyCategory₂.homMk e.toTruncated ≫ HomotopyCategory₂.homMk I.inv.toTruncated
      = 𝟙 (({ pt := x₀ } : HomotopyCategory₂ ((truncation 2).obj X))) := by
  rw [I.homInvId.toTruncated.homotopyCategory₂_fac]
  exact HomotopyCategory₂.homMk_id (({ pt := x₀ } : HomotopyCategory₂ ((truncation 2).obj X)))

/-- In the homotopy category, the inverse of an iso edge composes with it to the identity. -/
lemma homMk_inv_comp {e : Edge x₀ x₁} (I : IsIso e) :
    HomotopyCategory₂.homMk I.inv.toTruncated ≫ HomotopyCategory₂.homMk e.toTruncated
      = 𝟙 (({ pt := x₁ } : HomotopyCategory₂ ((truncation 2).obj X))) := by
  rw [I.invHomId.toTruncated.homotopyCategory₂_fac]
  exact HomotopyCategory₂.homMk_id (({ pt := x₁ } : HomotopyCategory₂ ((truncation 2).obj X)))

/-- 2-out-of-3 (right factor): if `k` is a composite of `f` and `g`, and `f` and `k`
are isomorphism edges, then `g` is an isomorphism edge. -/
noncomputable def cancelComp_left {f : Edge x₀ x₁} {g : Edge x₁ x₂} {k : Edge x₀ x₂}
    (c : CompStruct f g k) (hf : IsIso f) (hk : IsIso k) : IsIso g where
  inv := Edge.comp hk.inv f
  homInvId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have cfac : HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated
        = HomotopyCategory₂.homMk k.toTruncated := c.toTruncated.homotopyCategory₂_fac
    have hcomp : HomotopyCategory₂.homMk hk.inv.toTruncated ≫ HomotopyCategory₂.homMk f.toTruncated
        = HomotopyCategory₂.homMk (Edge.comp hk.inv f).toTruncated :=
      (Edge.compStruct hk.inv f).toTruncated.homotopyCategory₂_fac
    have hkki := homMk_comp_inv hk
    have hfif := homMk_inv_comp hf
    have hG : HomotopyCategory₂.homMk g.toTruncated
        = HomotopyCategory₂.homMk hf.inv.toTruncated ≫ HomotopyCategory₂.homMk k.toTruncated := by
      have h1 : HomotopyCategory₂.homMk hf.inv.toTruncated ≫
          (HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated)
            = HomotopyCategory₂.homMk hf.inv.toTruncated ≫ HomotopyCategory₂.homMk k.toTruncated := by
        rw [cfac]
      rwa [← Category.assoc, hfif, Category.id_comp] at h1
    calc HomotopyCategory₂.homMk g.toTruncated ≫
            HomotopyCategory₂.homMk (Edge.comp hk.inv f).toTruncated
        = HomotopyCategory₂.homMk g.toTruncated ≫
            (HomotopyCategory₂.homMk hk.inv.toTruncated ≫
              HomotopyCategory₂.homMk f.toTruncated) := by rw [← hcomp]
      _ = (HomotopyCategory₂.homMk hf.inv.toTruncated ≫ HomotopyCategory₂.homMk k.toTruncated) ≫
            (HomotopyCategory₂.homMk hk.inv.toTruncated ≫
              HomotopyCategory₂.homMk f.toTruncated) := by rw [hG]
      _ = HomotopyCategory₂.homMk hf.inv.toTruncated ≫
            ((HomotopyCategory₂.homMk k.toTruncated ≫ HomotopyCategory₂.homMk hk.inv.toTruncated) ≫
              HomotopyCategory₂.homMk f.toTruncated) := by simp only [Category.assoc]
      _ = HomotopyCategory₂.homMk hf.inv.toTruncated ≫
            (𝟙 _ ≫ HomotopyCategory₂.homMk f.toTruncated) := by rw [hkki]
      _ = HomotopyCategory₂.homMk hf.inv.toTruncated ≫ HomotopyCategory₂.homMk f.toTruncated := by
            rw [Category.id_comp]
      _ = 𝟙 (({ pt := x₁ } : HomotopyCategory₂ ((truncation 2).obj X))) := hfif
      _ = HomotopyCategory₂.homMk (Edge.id x₁).toTruncated :=
            (HomotopyCategory₂.homMk_id (({ pt := x₁ } : HomotopyCategory₂ ((truncation 2).obj X)))).symm
  invHomId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have cfac : HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated
        = HomotopyCategory₂.homMk k.toTruncated := c.toTruncated.homotopyCategory₂_fac
    have hcomp : HomotopyCategory₂.homMk hk.inv.toTruncated ≫ HomotopyCategory₂.homMk f.toTruncated
        = HomotopyCategory₂.homMk (Edge.comp hk.inv f).toTruncated :=
      (Edge.compStruct hk.inv f).toTruncated.homotopyCategory₂_fac
    have hkik := homMk_inv_comp hk
    calc HomotopyCategory₂.homMk (Edge.comp hk.inv f).toTruncated ≫
            HomotopyCategory₂.homMk g.toTruncated
        = (HomotopyCategory₂.homMk hk.inv.toTruncated ≫ HomotopyCategory₂.homMk f.toTruncated) ≫
            HomotopyCategory₂.homMk g.toTruncated := by rw [← hcomp]
      _ = HomotopyCategory₂.homMk hk.inv.toTruncated ≫
            (HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated) := by
            rw [Category.assoc]
      _ = HomotopyCategory₂.homMk hk.inv.toTruncated ≫ HomotopyCategory₂.homMk k.toTruncated := by
            rw [cfac]
      _ = 𝟙 (({ pt := x₂ } : HomotopyCategory₂ ((truncation 2).obj X))) := hkik
      _ = HomotopyCategory₂.homMk (Edge.id x₂).toTruncated :=
            (HomotopyCategory₂.homMk_id (({ pt := x₂ } : HomotopyCategory₂ ((truncation 2).obj X)))).symm

/-- 2-out-of-3 (left factor): if `k` is a composite of `f` and `g`, and `g` and `k`
are isomorphism edges, then `f` is an isomorphism edge. -/
noncomputable def cancelComp_right {f : Edge x₀ x₁} {g : Edge x₁ x₂} {k : Edge x₀ x₂}
    (c : CompStruct f g k) (hg : IsIso g) (hk : IsIso k) : IsIso f where
  inv := Edge.comp g hk.inv
  homInvId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have cfac : HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated
        = HomotopyCategory₂.homMk k.toTruncated := c.toTruncated.homotopyCategory₂_fac
    have hcomp : HomotopyCategory₂.homMk g.toTruncated ≫ HomotopyCategory₂.homMk hk.inv.toTruncated
        = HomotopyCategory₂.homMk (Edge.comp g hk.inv).toTruncated :=
      (Edge.compStruct g hk.inv).toTruncated.homotopyCategory₂_fac
    have hkki := homMk_comp_inv hk
    calc HomotopyCategory₂.homMk f.toTruncated ≫
            HomotopyCategory₂.homMk (Edge.comp g hk.inv).toTruncated
        = HomotopyCategory₂.homMk f.toTruncated ≫
            (HomotopyCategory₂.homMk g.toTruncated ≫
              HomotopyCategory₂.homMk hk.inv.toTruncated) := by rw [← hcomp]
      _ = (HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated) ≫
            HomotopyCategory₂.homMk hk.inv.toTruncated := by rw [← Category.assoc]
      _ = HomotopyCategory₂.homMk k.toTruncated ≫ HomotopyCategory₂.homMk hk.inv.toTruncated := by
            rw [cfac]
      _ = 𝟙 (({ pt := x₀ } : HomotopyCategory₂ ((truncation 2).obj X))) := hkki
      _ = HomotopyCategory₂.homMk (Edge.id x₀).toTruncated :=
            (HomotopyCategory₂.homMk_id (({ pt := x₀ } : HomotopyCategory₂ ((truncation 2).obj X)))).symm
  invHomId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have cfac : HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated
        = HomotopyCategory₂.homMk k.toTruncated := c.toTruncated.homotopyCategory₂_fac
    have hcomp : HomotopyCategory₂.homMk g.toTruncated ≫ HomotopyCategory₂.homMk hk.inv.toTruncated
        = HomotopyCategory₂.homMk (Edge.comp g hk.inv).toTruncated :=
      (Edge.compStruct g hk.inv).toTruncated.homotopyCategory₂_fac
    have hkik := homMk_inv_comp hk
    have hggi := homMk_comp_inv hg
    have hF : HomotopyCategory₂.homMk f.toTruncated
        = HomotopyCategory₂.homMk k.toTruncated ≫ HomotopyCategory₂.homMk hg.inv.toTruncated := by
      have h1 : (HomotopyCategory₂.homMk f.toTruncated ≫ HomotopyCategory₂.homMk g.toTruncated) ≫
          HomotopyCategory₂.homMk hg.inv.toTruncated
            = HomotopyCategory₂.homMk k.toTruncated ≫
              HomotopyCategory₂.homMk hg.inv.toTruncated := by rw [cfac]
      rwa [Category.assoc, hggi, Category.comp_id] at h1
    calc HomotopyCategory₂.homMk (Edge.comp g hk.inv).toTruncated ≫
            HomotopyCategory₂.homMk f.toTruncated
        = (HomotopyCategory₂.homMk g.toTruncated ≫ HomotopyCategory₂.homMk hk.inv.toTruncated) ≫
            HomotopyCategory₂.homMk f.toTruncated := by rw [← hcomp]
      _ = (HomotopyCategory₂.homMk g.toTruncated ≫ HomotopyCategory₂.homMk hk.inv.toTruncated) ≫
            (HomotopyCategory₂.homMk k.toTruncated ≫
              HomotopyCategory₂.homMk hg.inv.toTruncated) := by rw [hF]
      _ = HomotopyCategory₂.homMk g.toTruncated ≫
            ((HomotopyCategory₂.homMk hk.inv.toTruncated ≫ HomotopyCategory₂.homMk k.toTruncated) ≫
              HomotopyCategory₂.homMk hg.inv.toTruncated) := by simp only [Category.assoc]
      _ = HomotopyCategory₂.homMk g.toTruncated ≫
            (𝟙 _ ≫ HomotopyCategory₂.homMk hg.inv.toTruncated) := by rw [hkik]
      _ = HomotopyCategory₂.homMk g.toTruncated ≫ HomotopyCategory₂.homMk hg.inv.toTruncated := by
            rw [Category.id_comp]
      _ = 𝟙 (({ pt := x₁ } : HomotopyCategory₂ ((truncation 2).obj X))) := hggi
      _ = HomotopyCategory₂.homMk (Edge.id x₁).toTruncated :=
            (HomotopyCategory₂.homMk_id (({ pt := x₁ } : HomotopyCategory₂ ((truncation 2).obj X)))).symm

end IsIso

end Edge

/-- Closure for a single `2`-simplex: in a quasicategory, if the faces `δ 1` and `δ 2`
of a `2`-simplex are iso 1-simplices, then so is the outer face `δ 0`. -/
theorem isIsoSimplex_δ₀_of_outer {A : SSet} [Quasicategory A] (σ : A _⦋2⦌)
    (h₁ : IsIsoSimplex (A.δ 1 σ)) (h₂ : IsIsoSimplex (A.δ 2 σ)) :
    IsIsoSimplex (A.δ 0 σ) := by
  obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, c, hc⟩ := Edge.CompStruct.exists_of_simplex σ
  subst hc
  rw [c.d₀]
  rw [c.d₂] at h₂
  rw [c.d₁] at h₁
  obtain ⟨hf⟩ := Edge.isIso_of_isIsoSimplex e₀₁ h₂
  obtain ⟨hk⟩ := Edge.isIso_of_isIsoSimplex e₀₂ h₁
  exact isIsoSimplex_of_edge (Edge.IsIso.cancelComp_left c hf hk)

/-- Closure for a single `2`-simplex: in a quasicategory, if the faces `δ 0` and `δ 1`
of a `2`-simplex are iso 1-simplices, then so is the outer face `δ 2`. -/
theorem isIsoSimplex_δ₂_of_outer {A : SSet} [Quasicategory A] (σ : A _⦋2⦌)
    (h₀ : IsIsoSimplex (A.δ 0 σ)) (h₁ : IsIsoSimplex (A.δ 1 σ)) :
    IsIsoSimplex (A.δ 2 σ) := by
  obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, c, hc⟩ := Edge.CompStruct.exists_of_simplex σ
  subst hc
  rw [c.d₂]
  rw [c.d₀] at h₀
  rw [c.d₁] at h₁
  obtain ⟨hg⟩ := Edge.isIso_of_isIsoSimplex e₁₂ h₀
  obtain ⟨hk⟩ := Edge.isIso_of_isIsoSimplex e₀₂ h₁
  exact isIsoSimplex_of_edge (Edge.IsIso.cancelComp_right c hg hk)

/-! ## Replay of the special-outer-horn distinguished edges (sj_joyal_assemble.lean) -/

namespace SpecialOuterHorn

/-- The initial edge `[0,1]` of the special outer horn `Λ[n+2, 0]`. -/
def initialEdge {n : ℕ} : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by
    have hset : ({(0 : Fin (n + 3)), 0, 1} : Finset (Fin (n + 3))) = {0, 1} := by
      ext x; simp
    rw [hset, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]; omega)

/-- The final edge `[n+1, n+2]` of the special outer horn `Λ[n+2, last]`. -/
def finalEdge {n : ℕ} :
    (Λ[n + 2, (Fin.last (n + 2))] : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) (Fin.last (n + 2)) ⟨n + 1, by omega⟩ (Fin.last (n + 2))
    (by simp [Fin.le_def]) (by
    have hset : ({(Fin.last (n + 2)), (⟨n + 1, by omega⟩ : Fin (n + 3)),
        (Fin.last (n + 2))} : Finset (Fin (n + 3))) = {⟨n + 1, by omega⟩, Fin.last (n + 2)} := by
      ext x; simp [or_comm]
    rw [hset, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]; omega)

end SpecialOuterHorn

/-! ## B2 closure helper: a producer filler of an outer horn lands in `isoCore A` -/

/-- Outer-horn closure: a filler `g` of an outer horn (`i = 0` or `i = last`) in `A` whose
boundary lands in `isoCore A` has its top simplex land in `isoCore A` as well.  Mirrors the
inner-horn `filler_mem_isoCore`; the missing edge for dimension `2` is supplied by the
2-out-of-3 closure lemmas `isIsoSimplex_δ₀_of_outer` / `isIsoSimplex_δ₂_of_outer`. -/
theorem filler_mem_isoCore_outer {A : SSet} [Quasicategory A] {d : ℕ} {i : Fin (d + 3)}
    (hi : i = 0 ∨ i = Fin.last (d + 2))
    {τ : (Λ[d + 2, i] : SSet) ⟶ (isoCore A : SSet)} {g : Δ[d + 2] ⟶ A}
    (hg : τ ≫ (isoCore A).ι = Λ[d + 2, i].ι ≫ g) :
    yonedaEquiv g ∈ (isoCore A).obj (op ⦋d + 2⦌) := by
  rw [mem_isoCore_obj_iff]
  intro f
  by_cases hmem : stdSimplex.objEquiv.symm f ∈ Λ[d + 2, i].obj (op ⦋1⦌)
  · rw [map_yonedaEquiv]
    exact (mem_isoCore_obj_one_iff _).mp (app_mem_isoCore_of_mem_horn hg ⟨_, hmem⟩)
  · by_cases hd2 : 1 + 1 < d + 2
    · rw [horn_obj_eq_univ i 1 hd2] at hmem
      exact absurd (Set.mem_univ _) hmem
    · have hd0 : d = 0 := by omega
      subst hd0
      rcases hi with rfl | rfl
      · -- i = 0, horn `Λ[2,0]`, missing edge `δ 0`
        have hf0 : f = SimplexCategory.δ 0 := by
          rw [mem_horn_iff, not_not, stdSimplex.coe_asOrderHom_objEquiv_symm] at hmem
          have m1 : (1 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f) := by
            have h : (1 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f) ∪ ({0} : Set (Fin 3)) :=
              hmem ▸ Set.mem_univ _
            rcases h with h | h
            · exact h
            · exact absurd h (by decide)
          have m2 : (2 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f) := by
            have h : (2 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f) ∪ ({0} : Set (Fin 3)) :=
              hmem ▸ Set.mem_univ _
            rcases h with h | h
            · exact h
            · exact absurd h (by decide)
          obtain ⟨k1, hk1⟩ := m1
          obtain ⟨k2, hk2⟩ := m2
          have hmono : ((ConcreteCategory.hom f) 0).val ≤ ((ConcreteCategory.hom f) 1).val :=
            (ConcreteCategory.hom f).monotone' (show (0 : Fin 2) ≤ 1 by decide)
          have v1 := congrArg Fin.val hk1
          have v2 := congrArg Fin.val hk2
          have hval : ((ConcreteCategory.hom f) 0).val = 1 ∧
              ((ConcreteCategory.hom f) 1).val = 2 := by
            fin_cases k1 <;> fin_cases k2 <;> simp_all
          obtain ⟨hv0, hv1⟩ := hval
          apply SimplexCategory.Hom.ext
          ext k
          fin_cases k
          · show ((ConcreteCategory.hom f) 0).val = _
            rw [hv0]; decide
          · show ((ConcreteCategory.hom f) 1).val = _
            rw [hv1]; decide
        subst hf0
        apply isIsoSimplex_δ₀_of_outer
        · show IsIsoSimplex (A.map (SimplexCategory.δ 1).op (yonedaEquiv g))
          rw [map_yonedaEquiv]
          have hm1 : stdSimplex.objEquiv.symm (SimplexCategory.δ (1 : Fin 3))
              ∈ Λ[2, 0].obj (op ⦋1⦌) := by
            rw [objEquiv_symm_δ_mem_horn_iff]; decide
          exact (mem_isoCore_obj_one_iff _).mp (app_mem_isoCore_of_mem_horn hg ⟨_, hm1⟩)
        · show IsIsoSimplex (A.map (SimplexCategory.δ 2).op (yonedaEquiv g))
          rw [map_yonedaEquiv]
          have hm2 : stdSimplex.objEquiv.symm (SimplexCategory.δ (2 : Fin 3))
              ∈ Λ[2, 0].obj (op ⦋1⦌) := by
            rw [objEquiv_symm_δ_mem_horn_iff]; decide
          exact (mem_isoCore_obj_one_iff _).mp (app_mem_isoCore_of_mem_horn hg ⟨_, hm2⟩)
      · -- i = last 2 = 2, horn `Λ[2,2]`, missing edge `δ 2`
        have hf2 : f = SimplexCategory.δ 2 := by
          rw [mem_horn_iff, not_not, stdSimplex.coe_asOrderHom_objEquiv_symm] at hmem
          have m0 : (0 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f) := by
            have h : (0 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f)
                ∪ ({Fin.last 2} : Set (Fin 3)) := hmem ▸ Set.mem_univ _
            rcases h with h | h
            · exact h
            · exact absurd h (by decide)
          have m1 : (1 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f) := by
            have h : (1 : Fin 3) ∈ Set.range ⇑(ConcreteCategory.hom f)
                ∪ ({Fin.last 2} : Set (Fin 3)) := hmem ▸ Set.mem_univ _
            rcases h with h | h
            · exact h
            · exact absurd h (by decide)
          obtain ⟨k0, hk0⟩ := m0
          obtain ⟨k1, hk1⟩ := m1
          have hmono : ((ConcreteCategory.hom f) 0).val ≤ ((ConcreteCategory.hom f) 1).val :=
            (ConcreteCategory.hom f).monotone' (show (0 : Fin 2) ≤ 1 by decide)
          have v0 := congrArg Fin.val hk0
          have v1 := congrArg Fin.val hk1
          have hval : ((ConcreteCategory.hom f) 0).val = 0 ∧
              ((ConcreteCategory.hom f) 1).val = 1 := by
            fin_cases k0 <;> fin_cases k1 <;> simp_all
          obtain ⟨hv0, hv1⟩ := hval
          apply SimplexCategory.Hom.ext
          ext k
          fin_cases k
          · show ((ConcreteCategory.hom f) 0).val = _
            rw [hv0]; decide
          · show ((ConcreteCategory.hom f) 1).val = _
            rw [hv1]; decide
        subst hf2
        apply isIsoSimplex_δ₂_of_outer
        · show IsIsoSimplex (A.map (SimplexCategory.δ 0).op (yonedaEquiv g))
          rw [map_yonedaEquiv]
          have hm0 : stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 3))
              ∈ Λ[2, Fin.last 2].obj (op ⦋1⦌) := by
            rw [objEquiv_symm_δ_mem_horn_iff]; decide
          exact (mem_isoCore_obj_one_iff _).mp (app_mem_isoCore_of_mem_horn hg ⟨_, hm0⟩)
        · show IsIsoSimplex (A.map (SimplexCategory.δ 1).op (yonedaEquiv g))
          rw [map_yonedaEquiv]
          have hm1 : stdSimplex.objEquiv.symm (SimplexCategory.δ (1 : Fin 3))
              ∈ Λ[2, Fin.last 2].obj (op ⦋1⦌) := by
            rw [objEquiv_symm_δ_mem_horn_iff]; decide
          exact (mem_isoCore_obj_one_iff _).mp (app_mem_isoCore_of_mem_horn hg ⟨_, hm1⟩)

/-! ## LAYER-1 wrapper: producer ⟹ `IsoCoreOuterHornFiller A` -/

/-- From the special-outer-horn producers (`fill_zero`/`fill_last`, taken as hypotheses), the
outer-horn filler interface for `isoCore A` follows.  Once the producers land in the tree this
discharges by `isoCore_outerHornFiller_of_producer fill_zero fill_last`. -/
theorem isoCore_outerHornFiller_of_producer {A : SSet.{u}} [Quasicategory A]
    (hfill_zero : ∀ {n : ℕ} (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ A),
        IsIsoSimplex (σ₀.app (op ⦋1⦌) SpecialOuterHorn.initialEdge) →
        ∃ σ : Δ[n + 2] ⟶ A, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ)
    (hfill_last : ∀ {n : ℕ} (σ₀ : (Λ[n + 2, (Fin.last (n + 2))] : SSet.{u}) ⟶ A),
        IsIsoSimplex (σ₀.app (op ⦋1⦌) SpecialOuterHorn.finalEdge) →
        ∃ σ : Δ[n + 2] ⟶ A, σ₀ = Λ[n + 2, (Fin.last (n + 2))].ι ≫ σ) :
    IsoCoreOuterHornFiller A := by
  intro n
  obtain _ | k := n
  · -- B3: dimension 1 base case (`Λ[1, i]`); fill with the degenerate edge.
    intro i hi τ
    rcases hi with rfl | rfl
    · -- `Λ[1, 0]`; distinguished vertex is `1`.
      refine ⟨stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) ≫ horn.ι 0 1 (by decide) ≫ τ, ?_⟩
      apply horn.hom_ext
      intro j hj
      have hjeq : j = 1 := by
        fin_cases j
        · exact absurd rfl hj
        · rfl
      subst hjeq
      rw [← horn.yonedaEquiv_ι 0 1 hj, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
      apply congrArg
      rw [← Category.assoc, horn.ι_ι, ← Category.assoc]
      have hcollapse : stdSimplex.δ (1 : Fin 2)
          ≫ stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) = 𝟙 _ := by
        show stdSimplex.map (SimplexCategory.δ 1) ≫ stdSimplex.map _ = 𝟙 _
        rw [← Functor.map_comp,
          Subsingleton.elim (SimplexCategory.δ 1 ≫ SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌),
          CategoryTheory.Functor.map_id]
      rw [hcollapse, Category.id_comp]
    · -- `Λ[1, last 1]`; distinguished vertex is `0`.
      refine ⟨stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)
          ≫ horn.ι (Fin.last 1) 0 (by decide) ≫ τ, ?_⟩
      apply horn.hom_ext
      intro j hj
      have hjeq : j = 0 := by
        fin_cases j
        · rfl
        · exact absurd rfl hj
      subst hjeq
      rw [← horn.yonedaEquiv_ι (Fin.last 1) 0 hj, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
      apply congrArg
      rw [← Category.assoc, horn.ι_ι, ← Category.assoc]
      have hcollapse : stdSimplex.δ (0 : Fin 2)
          ≫ stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) = 𝟙 _ := by
        show stdSimplex.map (SimplexCategory.δ 0) ≫ stdSimplex.map _ = 𝟙 _
        rw [← Functor.map_comp,
          Subsingleton.elim (SimplexCategory.δ 0 ≫ SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌),
          CategoryTheory.Functor.map_id]
      rw [hcollapse, Category.id_comp]
  · -- B1 + B2: dimension `k + 2 ≥ 2`; apply the producer, then close via `filler_mem_isoCore_outer`.
    intro i hi τ
    rcases hi with rfl | rfl
    · -- outer horn at `0`
      have hedge : IsIsoSimplex ((τ ≫ (isoCore A).ι).app (op ⦋1⦌)
          SpecialOuterHorn.initialEdge) := by
        have hval : (τ ≫ (isoCore A).ι).app (op ⦋1⦌) SpecialOuterHorn.initialEdge
            = (τ.app (op ⦋1⦌) SpecialOuterHorn.initialEdge).val := by simp
        rw [hval]
        exact (mem_isoCore_obj_one_iff _).mp (τ.app (op ⦋1⦌) SpecialOuterHorn.initialEdge).property
      obtain ⟨g, hg⟩ := hfill_zero (τ ≫ (isoCore A).ι) hedge
      have hg' : τ ≫ (isoCore A).ι = Λ[k + 2, (0 : Fin (k + 3))].ι ≫ g := hg
      refine ⟨Subcomplex.lift g ?_, ?_⟩
      · intro m y hy
        rcases hy with ⟨x, rfl⟩
        change g.app m x ∈ (isoCore A).obj m
        have hval : A.map (stdSimplex.objEquiv x).op (yonedaEquiv g) = g.app m x := by
          rw [stdSimplex.map_objEquiv_op_apply, Equiv.symm_apply_apply]
        rw [← hval]
        exact (isoCore A).map (stdSimplex.objEquiv x).op
          (filler_mem_isoCore_outer (Or.inl rfl) hg')
      · apply (cancel_mono (isoCore A).ι).mp
        rw [Category.assoc, Subcomplex.lift_ι]
        exact hg'
    · -- outer horn at `last`
      have hedge : IsIsoSimplex ((τ ≫ (isoCore A).ι).app (op ⦋1⦌)
          SpecialOuterHorn.finalEdge) := by
        have hval : (τ ≫ (isoCore A).ι).app (op ⦋1⦌) SpecialOuterHorn.finalEdge
            = (τ.app (op ⦋1⦌) SpecialOuterHorn.finalEdge).val := by simp
        rw [hval]
        exact (mem_isoCore_obj_one_iff _).mp (τ.app (op ⦋1⦌) SpecialOuterHorn.finalEdge).property
      obtain ⟨g, hg⟩ := hfill_last (τ ≫ (isoCore A).ι) hedge
      have hg' : τ ≫ (isoCore A).ι = Λ[k + 2, (Fin.last (k + 2))].ι ≫ g := hg
      refine ⟨Subcomplex.lift g ?_, ?_⟩
      · intro m y hy
        rcases hy with ⟨x, rfl⟩
        change g.app m x ∈ (isoCore A).obj m
        have hval : A.map (stdSimplex.objEquiv x).op (yonedaEquiv g) = g.app m x := by
          rw [stdSimplex.map_objEquiv_op_apply, Equiv.symm_apply_apply]
        rw [← hval]
        exact (isoCore A).map (stdSimplex.objEquiv x).op
          (filler_mem_isoCore_outer (Or.inr rfl) hg')
      · apply (cancel_mono (isoCore A).ι).mp
        rw [Category.assoc, Subcomplex.lift_ι]
        exact hg'

open SpecialOuterHorn

/-- The edge identity: the right-block inclusion `inr'` is the (transported) final edge. -/
lemma inr'_eq_finalEdge_map (M : ℕ) :
    stdSimplex.map (inr' ⦋M + 1⦌ ⦋1⦌)
      = yonedaEquiv.symm (finalEdge (n := M + 1)
          : (Λ[M + 1 + 2, Fin.last (M + 1 + 2)] : SSet.{u}) _⦋1⦌).1 := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_map, Equiv.apply_symm_apply]
  show stdSimplex.objEquiv.symm (inr' ⦋M + 1⦌ ⦋1⦌)
    = (horn.edge (M + 1 + 2) (Fin.last (M + 1 + 2)) ⟨M + 1 + 1, by omega⟩ (Fin.last (M + 1 + 2)) _ _).1
  rw [horn.edge_coe]
  apply stdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply SimplexCategory.Hom.ext
  ext i
  rw [stdSimplex.objEquiv_toOrderHom_apply, inr'_eval]
  fin_cases i <;> rfl

/-- **`hedge`**: the encoded edge transported back through the arrow-iso is the final edge. -/
lemma hedge_lemma (M : ℕ) :
    yonedaEquiv (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u})
        ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left)
      = (finalEdge (n := M + 1)
          : (Λ[M + 1 + 2, Fin.last (M + 1 + 2)] : SSet.{u}) _⦋1⦌) := by
  have hmap : joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u})
        ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left
      = yonedaEquiv.symm (finalEdge (n := M + 1)
          : (Λ[M + 1 + 2, Fin.last (M + 1 + 2)] : SSet.{u}) _⦋1⦌) := by
    apply (cancel_mono (Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι)).mp
    have hw : (transLast.{u} M).inv.left ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι
        = (sqLeibCo (jbM.{u} M) (gdM.{u})).ι ≫ (transLast.{u} M).inv.right := (transLast.{u} M).inv.w
    have hRHS : yonedaEquiv.symm (finalEdge (n := M + 1)
          : (Λ[M + 1 + 2, Fin.last (M + 1 + 2)] : SSet.{u}) _⦋1⦌)
          ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι = stdSimplex.map (inr' ⦋M + 1⦌ ⦋1⦌) := by
      rw [yonedaEquiv_symm_comp]; exact (inr'_eq_finalEdge_map M).symm
    have hLHS : (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u})
          ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left)
          ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι = stdSimplex.map (inr' ⦋M + 1⦌ ⦋1⦌) := by
      have h1 : (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left) ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι
          = joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ((sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left) ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι := Category.assoc _ _ _
      have h2 : joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ((sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left) ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι
          = joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι := congrArg (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ·) (Category.assoc _ _ _)
      have h3 : joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (transLast.{u} M).inv.left ≫ Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι
          = joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).ι ≫ (transLast.{u} M).inv.right := congrArg (fun t => joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ t) hw
      have h4 : joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).ι ≫ (transLast.{u} M).inv.right
          = joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ((sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).ι) ≫ (transLast.{u} M).inv.right := congrArg (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ·) (Category.assoc _ _ _).symm
      have h5 : joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ((sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).ι) ≫ (transLast.{u} M).inv.right
          = joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (joinFunctor.map (jbM.{u} M)).app (Δ[1] : SSet.{u}) ≫ (transLast.{u} M).inv.right :=
        congrArg (fun t => joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ t ≫ (transLast.{u} M).inv.right)
          (Functor.PushoutObjObj.inr_ι (sqLeibCo (jbM.{u} M) (gdM.{u})))
      have h6 : joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (joinFunctor.map (jbM.{u} M)).app (Δ[1] : SSet.{u}) ≫ (transLast.{u} M).inv.right
          = (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (joinFunctor.map (jbM.{u} M)).app (Δ[1] : SSet.{u})) ≫ (transLast.{u} M).inv.right := (Category.assoc _ _ _).symm
      have h7 : (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (joinFunctor.map (jbM.{u} M)).app (Δ[1] : SSet.{u})) ≫ (transLast.{u} M).inv.right
          = joinInr (Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (transLast.{u} M).inv.right :=
        congrArg (· ≫ (transLast.{u} M).inv.right) (joinInr_naturality_left (jbM.{u} M) (Δ[1] : SSet.{u}))
      have h8 : joinInr (Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (transLast.{u} M).inv.right = joinInr (Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (joinStdSimplex.{u} (M + 1) 1).hom := congrArg (joinInr (Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ ·) (einv_right M)
      have h9 : joinInr (Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (joinStdSimplex.{u} (M + 1) 1).hom = stdSimplex.map (inr' ⦋M + 1⦌ ⦋1⦌) := joinInr_joinStdSimplex (M + 1) 1
      exact h1.trans <| h2.trans <| h3.trans <| h4.trans <| h5.trans <| h6.trans <|
        h7.trans <| h8.trans h9
    rw [hRHS]; exact hLHS
  exact (congrArg yonedaEquiv hmap).trans (Equiv.apply_symm_apply yonedaEquiv _)

/-- Step 2: the `n = M+1 ≥ 1` case of `fill_last`, via horn-form transport. -/
theorem fillerLast {A : SSet.{u}} [Quasicategory A] (M : ℕ)
    (σ₀ : (Λ[M + 1 + 2, Fin.last (M + 1 + 2)] : SSet.{u}) ⟶ A)
    (h_final : IsIsoSimplex (σ₀.app (op ⦋1⦌) (finalEdge (n := M + 1)))) :
    ∃ σ : Δ[M + 1 + 2] ⟶ A, σ₀ = Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι ≫ σ := by
  haveI : Quasicategory (Δ[0] : SSet.{u}) :=
    (quasicategory_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u})) stdSimplex.isTerminalObj₀).mpr
      inferInstance
  set e := transLast.{u} M with he
  set q : A ⟶ (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.from A with hq
  haveI : InnerFibration q :=
    (quasicategory_iff_of_isTerminal q stdSimplex.isTerminalObj₀).mp inferInstance
  set top : (sqLeibCo (jbM.{u} M) (gdM.{u})).pt ⟶ A := e.inv.left ≫ σ₀ with htop
  set bot : (joinFunctor.obj (Δ[M + 1] : SSet.{u})).obj (Δ[1] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.from _ with hbot
  have hsq : (sqLeibCo (jbM.{u} M) (gdM.{u})).ι ≫ bot = top ≫ q :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  -- hinv: the encoded θ-edge is invertible because it IS the (transported) final edge
  have hedge : yonedaEquiv (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u})
      ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ e.inv.left) = (finalEdge (n := M + 1)) := by
    rw [he]; exact hedge_lemma M
  have hθ : IsIsoSimplex (((encEdge (jbM.{u} M) top q bot hsq).map
      (thetaMap (jbM.{u} M) (encF (jbM.{u} M) (gdM.{u}) top) q)).edge) := by
    rw [encThetaEdge_eq, htop]
    have hassoc : joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u})
          ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ e.inv.left ≫ σ₀
        = (joinInr (∂Δ[M + 1] : SSet.{u}) (Δ[1] : SSet.{u})
            ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).inr ≫ e.inv.left) ≫ σ₀ := by
      simp only [Category.assoc]
    rw [hassoc, yonedaEquiv_comp, hedge]
    exact h_final
  obtain ⟨filler, hfill_top, _⟩ :=
    specialOuterHornFiller_last_leibniz (jbM.{u} M) top q bot hsq
      (Edge.isIso_of_isIsoSimplex _ hθ)
  refine ⟨e.hom.right ≫ filler, ?_⟩
  have hw_clean : Λ[M + 1 + 2, Fin.last (M + 1 + 2)].ι ≫ e.hom.right
      = e.hom.left ≫ (sqLeibCo (jbM.{u} M) (gdM.{u})).ι := e.hom.w.symm
  have hli : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Arrow.comp_left, e.hom_inv_id]; simp
  have hft : (sqLeibCo (jbM.{u} M) (gdM.{u})).ι ≫ filler = top := hfill_top
  exact
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ filler) hw_clean).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (e.hom.left ≫ ·) hft).trans
            ((congrArg (e.hom.left ≫ ·) htop).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (· ≫ σ₀) hli).trans (Category.id_comp σ₀)))))))).symm

/-- The `[0,2]` edge of `Λ[2, 2]`. -/
def edge02 : (Λ[2, (Fin.last 2)] : SSet.{u}) _⦋1⦌ :=
  horn.edge 2 (Fin.last 2) 0 (Fin.last 2) (by simp [Fin.le_def]) (by decide)

/-- Step 3: the `n = 0` (`Λ[2,2]`) base case of `fill_last`, by direct simplicial filling. -/
theorem fillBase {A : SSet.{u}} [Quasicategory A]
    (σ₀ : (Λ[0 + 2, Fin.last (0 + 2)] : SSet.{u}) ⟶ A)
    (h_final : IsIsoSimplex (σ₀.app (op ⦋1⦌) (finalEdge (n := 0)))) :
    ∃ σ : Δ[0 + 2] ⟶ A, σ₀ = Λ[0 + 2, Fin.last (0 + 2)].ι ≫ σ := by
  have hf0 : horn.face (Fin.last 2) (0 : Fin 3) (by decide)
      = (finalEdge (n := 0) : (Λ[2, Fin.last 2] : SSet.{u}) _⦋1⦌) := by
    apply Subtype.ext; apply (stdSimplex.objEquiv).injective; decide
  have hf1 : horn.face (Fin.last 2) (1 : Fin 3) (by decide)
      = (edge02 : (Λ[2, Fin.last 2] : SSet.{u}) _⦋1⦌) := by
    apply Subtype.ext; apply (stdSimplex.objEquiv).injective; decide
  let e12 : Edge (A.δ 1 (σ₀.app (op ⦋1⦌) (finalEdge (n := 0))))
      (A.δ 0 (σ₀.app (op ⦋1⦌) (finalEdge (n := 0)))) := Edge.mk' (σ₀.app (op ⦋1⦌) (finalEdge (n := 0)))
  let e02 : Edge (A.δ 1 (σ₀.app (op ⦋1⦌) edge02)) (A.δ 0 (σ₀.app (op ⦋1⦌) edge02)) :=
    Edge.mk' (σ₀.app (op ⦋1⦌) edge02)
  have hshare : A.δ 0 (σ₀.app (op ⦋1⦌) (finalEdge (n := 0))) = A.δ 0 (σ₀.app (op ⦋1⦌) edge02) := by
    have hn : ∀ (x : (Λ[2, Fin.last 2] : SSet.{u}) _⦋1⦌),
        A.δ (0 : Fin 2) (σ₀.app (op ⦋1⦌) x)
          = σ₀.app (op ⦋0⦌) ((Λ[2, Fin.last 2] : SSet.{u}).δ (0 : Fin 2) x) :=
      fun x => (NatTrans.naturality_apply σ₀ (SimplexCategory.δ (0 : Fin 2)).op x).symm
    rw [hn, hn]
    congr 1
  obtain ⟨hiso⟩ := Edge.isIso_of_isIsoSimplex e12 (by rw [Edge.mk'_edge]; exact h_final)
  let e02' : Edge (A.δ 1 (σ₀.app (op ⦋1⦌) edge02)) (A.δ 0 (σ₀.app (op ⦋1⦌) (finalEdge (n := 0)))) :=
    e02.ofEq rfl hshare.symm
  let e21 := hiso.inv
  let k := Edge.comp e02' e21
  have hfac : HomotopyCategory₂.homMk k.toTruncated ≫ HomotopyCategory₂.homMk e12.toTruncated
      = HomotopyCategory₂.homMk e02'.toTruncated := by
    have hkc : HomotopyCategory₂.homMk k.toTruncated
        = HomotopyCategory₂.homMk e02'.toTruncated ≫ HomotopyCategory₂.homMk e21.toTruncated :=
      (Edge.compStruct e02' e21).toTruncated.homotopyCategory₂_fac.symm
    have hinv : HomotopyCategory₂.homMk e21.toTruncated ≫ HomotopyCategory₂.homMk e12.toTruncated
        = 𝟙 _ := by
      rw [hiso.invHomId.toTruncated.homotopyCategory₂_fac]
      exact HomotopyCategory₂.homMk_id _
    rw [hkc, Category.assoc, hinv, Category.comp_id]
  let cs : Edge.CompStruct k e12 e02' :=
    Edge.CompStruct.ofTruncated (SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac hfac)
  refine ⟨yonedaEquiv.symm cs.simplex, ?_⟩
  apply horn.hom_ext
  intro j hj
  have hR : (Λ[2, Fin.last 2].ι ≫ yonedaEquiv.symm cs.simplex).app (op ⦋1⦌)
        (horn.face (Fin.last 2) j hj) = A.δ j cs.simplex := by
    rw [show (Λ[2, Fin.last 2].ι ≫ yonedaEquiv.symm cs.simplex).app (op ⦋1⦌)
            (horn.face (Fin.last 2) j hj)
          = yonedaEquiv (horn.ι (Fin.last 2) j hj ≫ Λ[2, Fin.last 2].ι
              ≫ yonedaEquiv.symm cs.simplex) from by
        rw [yonedaEquiv_comp, horn.yonedaEquiv_ι]]
    rw [horn.ι_ι_assoc,
      show (stdSimplex.δ j : Δ[1] ⟶ Δ[2]) = stdSimplex.map (SimplexCategory.δ j) from rfl,
      yonedaEquiv_symm_naturality, Equiv.apply_symm_apply]
    rfl
  rw [hR]
  rcases (by decide : ∀ j : Fin 3, j ≠ Fin.last 2 → j = 0 ∨ j = 1) j hj with rfl | rfl
  · rw [hf0, cs.d₀, Edge.mk'_edge]
  · rw [hf1, cs.d₁]
    show σ₀.app (op ⦋1⦌) edge02 = e02'.edge
    rfl

namespace SpecialOuterHorn

theorem fill_last {A : SSet.{u}} [Quasicategory A] {n : ℕ}
    (σ₀ : (Λ[n + 2, (Fin.last (n + 2))] : SSet) ⟶ A)
    (h_final : IsIsoSimplex (σ₀.app (op ⦋1⦌) finalEdge)) :
    ∃ σ : Δ[n + 2] ⟶ A, σ₀ = Λ[n + 2, (Fin.last (n + 2))].ι ≫ σ := by
  obtain _ | M := n
  · exact fillBase σ₀ h_final
  · exact fillerLast M σ₀ h_final

end SpecialOuterHorn

end SSet
