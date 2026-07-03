/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Isofibrations
import InfinityCosmos.ForMathlib.InfinityCosmos.CotensorPointIso
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy

open scoped Simplicial

/-!
# The Brown factorization construction

Given a morphism `f : A ⟶ B` in an ∞-cosmos, this file builds the Brown factorization object as a
pullback along the source endpoint of the coherent-isomorphism path object `coherentIso ⋔ B`, and
records the section `brownFactorizationSection f` together with the right map
`brownFactorizationRight f`. The headline identity `brownFactorization_fac` states that the section
followed by the right map recovers `f`.

The construction reuses the point-cotensor comparison `cotensorPointIso` from `CotensorPointIso` to
identify the right endpoint `Δ[0] ⋔ B` with `B`. Only the factorization data is built here; the
downstream claim that the left projection is a trivial fibration is left to a later API (see the
note at the end of this file).
-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos
open HasConicalTerminal

variable {K : Type u} [Category.{v} K] [InfinityCosmos K]

/-- The source vertex inclusion of the coherent isomorphism is a monomorphism. -/
instance coherentIsoSrc_mono : Mono SSet.coherentIso.src := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b _h
  apply (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := n)).injective
  apply SimplexCategory.Hom.ext
  ext x
  have ha : ((SSet.stdSimplex.objEquiv a).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  have hb : ((SSet.stdSimplex.objEquiv b).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  rw [ha, hb]

/-- The target vertex inclusion of the coherent isomorphism is a monomorphism. -/
instance coherentIsoTgt_mono : Mono SSet.coherentIso.tgt := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b _h
  apply (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := n)).injective
  apply SimplexCategory.Hom.ext
  ext x
  have ha : ((SSet.stdSimplex.objEquiv a).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  have hb : ((SSet.stdSimplex.objEquiv b).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  rw [ha, hb]

/-- The constant coherent-isomorphism path corresponding to an ordinary morphism. -/
noncomputable def coherentIsoPathMap {A B : K} (f : A ⟶ B) : A ⟶ SSet.coherentIso ⋔ B :=
  (cotensor.iso.underlying SSet.coherentIso B A).symm
    ((SSet.isTerminalDeltaZero.from SSet.coherentIso ≫ SSet.pointIsUnit.hom) ≫
      (eHomEquiv SSet f : MonoidalCategoryStruct.tensorUnit SSet ⟶ sHom A B))

/-- The source endpoint of the constant coherent-isomorphism path is `f`. -/
lemma coherentIsoPathMap_src {A B : K} (f : A ⟶ B) :
    coherentIsoPathMap f ≫ cotensorContraMap SSet.coherentIso.src B = cotensorPointMap f := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A).injective
  rw [cotensor_iso_underlying_precompose]
  simp [coherentIsoPathMap, cotensorPointMap]
  have hsrc :
      SSet.coherentIso.src ≫ SSet.isTerminalDeltaZero.from SSet.coherentIso =
        𝟙 (Δ[0] : SSet.{v}) :=
    SSet.isTerminalDeltaZero.hom_ext _ _
  rw [← Category.assoc, hsrc, Category.id_comp]

/-- The target endpoint of the constant coherent-isomorphism path is also `f`. -/
lemma coherentIsoPathMap_tgt {A B : K} (f : A ⟶ B) :
    coherentIsoPathMap f ≫ cotensorContraMap SSet.coherentIso.tgt B = cotensorPointMap f := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A).injective
  rw [cotensor_iso_underlying_precompose]
  simp [coherentIsoPathMap, cotensorPointMap]
  have htgt :
      SSet.coherentIso.tgt ≫ SSet.isTerminalDeltaZero.from SSet.coherentIso =
        𝟙 (Δ[0] : SSet.{v}) :=
    SSet.isTerminalDeltaZero.hom_ext _ _
  rw [← Category.assoc, htgt, Category.id_comp]

/-- The source-endpoint evaluation of the coherent-isomorphism path object, valued directly in `B`
through the point-cotensor identification `Δ[0] ⋔ B ≅ B`. It is an isofibration: the contravariant
cotensor isofibration `cotensorContraIsofibration coherentIso.src B` composed with the isomorphism
`cotensorPointIso B`. -/
noncomputable def brownFactorizationSrc (B : K) : (SSet.coherentIso ⋔ B) ↠ B :=
  compIsofibration (cotensorContraIsofibration SSet.coherentIso.src B)
    ⟨(cotensorPointIso B).hom, iso_isIsofibration _⟩

@[simp]
lemma brownFactorizationSrc_map (B : K) :
    (brownFactorizationSrc B).1 =
      cotensorContraMap SSet.coherentIso.src B ≫ (cotensorPointIso B).hom := rfl

/-- The pullback used to define the Brown factorization object exists. The Brown factorization is
the pullback of the source-endpoint evaluation `brownFactorizationSrc` and `f`. -/
noncomputable instance brownFactorization_hasPullback {A B : K} (f : A ⟶ B) :
    HasPullback (cotensorContraMap SSet.coherentIso.src B ≫ (cotensorPointIso B).hom) f := by
  have : HasConicalPullback SSet
      (cotensorContraMap SSet.coherentIso.src B ≫ (cotensorPointIso B).hom) f :=
    has_isofibration_pullbacks (brownFactorizationSrc B) f
  infer_instance

/-- The Brown factorization pullback object: the pullback of the source-endpoint evaluation (valued
in `B` through `Δ[0] ⋔ B ≅ B`) and `f`. -/
noncomputable def brownFactorizationObj {A B : K} (f : A ⟶ B) : K :=
  pullback (cotensorContraMap SSet.coherentIso.src B ≫ (cotensorPointIso B).hom) f

/-- The projection from the Brown factorization object to the coherent-isomorphism path object. -/
noncomputable def brownFactorizationPath {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ SSet.coherentIso ⋔ B :=
  pullback.fst (cotensorContraMap SSet.coherentIso.src B ≫ (cotensorPointIso B).hom) f

/-- The left projection from the Brown factorization object. -/
noncomputable def brownFactorizationLeft {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ A :=
  pullback.snd (cotensorContraMap SSet.coherentIso.src B ≫ (cotensorPointIso B).hom) f

/-- The Brown factorization square is a pullback of the source-endpoint evaluation and `f`. This
falls out of the definition of `brownFactorizationObj` as that pullback. -/
lemma brownFactorization_isPullback {A B : K} (f : A ⟶ B) :
    IsPullback (brownFactorizationPath f) (brownFactorizationLeft f)
      (cotensorContraMap SSet.coherentIso.src B ≫ (cotensorPointIso B).hom) f :=
  IsPullback.of_hasPullback _ _

/-- The right endpoint map from the Brown factorization object, valued in the point cotensor. -/
noncomputable def brownFactorizationRightPoint {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ (Δ[0] : SSet.{v}) ⋔ B :=
  brownFactorizationPath f ≫ cotensorContraMap SSet.coherentIso.tgt B

/-- The section of the Brown factorization map induced by the constant path. -/
noncomputable def brownFactorizationSection {A B : K} (f : A ⟶ B) :
    A ⟶ brownFactorizationObj f :=
  pullback.lift (coherentIsoPathMap f) (𝟙 A) (by
    rw [Category.id_comp, ← Category.assoc, coherentIsoPathMap_src]
    exact cotensorPointMap_comp_cotensorPointIsoHom f)

/-- The path projection of the Brown section is the constant coherent-isomorphism path. -/
lemma brownFactorizationSection_path {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationPath f = coherentIsoPathMap f := by
  unfold brownFactorizationSection brownFactorizationPath
  exact pullback.lift_fst _ _ _

/-- The left projection of the Brown section is the identity. -/
lemma brownFactorizationSection_left {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationLeft f = 𝟙 A := by
  unfold brownFactorizationSection brownFactorizationLeft
  exact pullback.lift_snd _ _ _

/-- The right endpoint of the Brown section is the point-cotensor map of `f`. -/
lemma brownFactorizationSection_rightPoint {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationRightPoint f = cotensorPointMap f := by
  rw [brownFactorizationRightPoint, ← Category.assoc, brownFactorizationSection_path,
    coherentIsoPathMap_tgt]

/-- The right map of the Brown factorization, after identifying `Δ[0] ⋔ B` with `B`. -/
noncomputable def brownFactorizationRight {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ B :=
  brownFactorizationRightPoint f ≫ (cotensorPointIso B).hom

/-- The Brown section followed by the right map is the original morphism. -/
lemma brownFactorization_fac {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationRight f = f := by
  unfold brownFactorizationRight
  rw [← Category.assoc, brownFactorizationSection_rightPoint]
  exact cotensorPointMap_comp_cotensorPointIsoHom f

/-
This file only proves the Brown factorization construction. The conclusion needed to finish
Lemma 1.5.12 is intentionally not asserted here: the missing downstream statement is that
`brownFactorizationLeft f` is a trivial fibration, and hence that the section above exhibits the
left map as an equivalence. In a later API this would have the shape
`brownFactorizationLeft_trivialFibration (f) : IsTrivialFibration (brownFactorizationLeft f)`.
That statement depends on the stability of trivial fibrations under products, pullbacks, and
inverse limits of towers from #114, and under Leibniz cotensors with monomorphisms from #115.
-/

end InfinityCosmos
