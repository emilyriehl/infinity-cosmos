/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Isofibrations
import InfinityCosmos.ForMathlib.InfinityCosmos.TrivialFibrationLimits

/-!
# Stability of the representable trivial-fibration class under Leibniz cotensor with monomorphisms

This file proves the ∞-cosmos half of infinity-cosmos issue #115 (blueprint 1.5.7 / axiom SM7,
"easy" direction). The genuine closure statement is for the class `RepresentableTrivialFibration`:
if `i : U ⟶ V` is a monomorphism of simplicial sets and `f : A ↠ B` is an isofibration that is
representably trivial, then the Leibniz cotensor `leibnizCotensorMap i f` is again representably
trivial (`representableTrivialFibration_leibnizCotensorMap`). The def-form statement
`trivialFibration_leibnizCotensorMap` is a corollary that repackages this as an
`InfinityCosmos.TrivialFibration`.

The argument is the representable bridge used throughout the #114 stability results. The Leibniz
cotensor is already known to be an isofibration (the ∞-cosmos axiom
`leibniz_cotensor_isIsofibration`, packaged as `leibnizCotensorIsofibration`); what remains is that
it is representably trivial. We obtain this from the simplicial-set result: applying the covariant
representable `Fun(X, -)` to the Leibniz cotensor pullback square produces, after the cotensor
isomorphisms `sHom X (U ⋔ A) ≅ (ihom U).obj (sHom X A)`, the internal-hom pullback square of `i`
against `representableMap X f.1`. The representable of `leibnizCotensorMap i f` is then identified
(up to a cotensor isomorphism on its source) with the comparison map `π` of that square, which is a
trivial fibration of simplicial sets by `SSet.TrivialFibration.pullbackObjObjπ`, the simplicial half
of issue #115, already in the tree.

## Main results

* `representableLeibnizPullbackObjObj`: the internal-hom `PullbackObjObj` structure on `SSet`
  obtained by transporting the representable Leibniz cotensor pullback square along the cotensor
  isomorphisms.
* `representableTrivialFibration_leibnizCotensorMap` (**issue #115, class closure**): the Leibniz
  cotensor of a monomorphism with a representably-trivial isofibration is representably trivial.
  Hypothesis and conclusion are both `RepresentableTrivialFibration`.
* `trivialFibration_leibnizCotensorMap` (**issue #115, corollary form**): the Leibniz cotensor of a
  monomorphism with an isofibration that is representably trivial is an
  `InfinityCosmos.TrivialFibration`. It consumes a `RepresentableTrivialFibration` hypothesis via
  the forward bridge `RepresentableTrivialFibration.equivalence`; because only that forward bridge
  exists, it does not by itself close the `InfinityCosmos.TrivialFibration` class. Upgrading it to
  genuine closure needs the converse bridge `SSet.TrivialFibration.of_isofibration_of_equiv` stated
  in the module docstring of `InfinityCosmos.ForMathlib.InfinityCosmos.TrivialFibrationLimits`.
-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos
open MonoidalCategory MonoidalClosed Functor SSet

variable {K : Type u} [Category.{v} K] [InfinityCosmos.{0} K]

/-- The top projection of the Leibniz cotensor pullback square composed with the Leibniz cotensor
map recovers the contravariant cotensor map. -/
lemma leibnizCotensorMap_fst {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    leibnizCotensorMap i f ≫ leibnizCotensor.fst i f = cotensorContraMap i A :=
  (leibnizCotensor.isPullback i f).lift_fst _ _ _

/-- The left projection of the Leibniz cotensor pullback square composed with the Leibniz cotensor
map recovers the covariant cotensor map. -/
lemma leibnizCotensorMap_snd {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    leibnizCotensorMap i f ≫ leibnizCotensor.snd i f = cotensorCovMap V f.1 :=
  (leibnizCotensor.isPullback i f).lift_snd _ _ _

/-- Applying the covariant representable `Fun(X, -)` to the Leibniz cotensor pullback square and
transporting along the cotensor isomorphisms `sHom X (W ⋔ C) ≅ (ihom W).obj (sHom X C)` yields the
internal-hom `PullbackObjObj` structure of `i` against `representableMap X f.1`. Its underlying
object is `sHom X (leibnizCotensorCod i f)`, so the comparison map `π` lands in the representable of
the Leibniz cotensor codomain. -/
@[simps pt fst snd]
noncomputable def representableLeibnizPullbackObjObj {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    {A B : K} (f : A ↠ B) (X : K) :
    MonoidalClosed.internalHom.PullbackObjObj i (representableMap X f.1) where
  pt := sHom X (leibnizCotensorCod i f)
  fst := representableMap X (leibnizCotensor.fst i f) ≫ (cotensor.iso U A X).hom
  snd := representableMap X (leibnizCotensor.snd i f) ≫ (cotensor.iso V B X).hom
  isPullback :=
    (leibnizCotensor.representableIsPullback i f X).of_iso
      (Iso.refl _) (cotensor.iso U A X) (cotensor.iso V B X) (cotensor.iso U B X)
      (by simp) (by simp)
      (cotensor_iso_hom_naturality_postcompose f.1 X)
      (cotensor_iso_hom_naturality_precompose i B X)

set_option backward.isDefEq.respectTransparency false in
/-- **Issue #115 (∞-cosmos, representable form).** The Leibniz cotensor of a monomorphism `i` with a
representably-trivial isofibration `f` is again representably trivial: each representable of
`leibnizCotensorMap i f` is, up to a cotensor isomorphism on its source, the comparison map of the
internal-hom pullback square of `i` against `representableMap X f.1`, a trivial fibration of
simplicial sets by `SSet.TrivialFibration.pullbackObjObjπ`. -/
theorem representableTrivialFibration_leibnizCotensorMap {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    {A B : K} (f : A ↠ B) (hf : RepresentableTrivialFibration f.1) :
    RepresentableTrivialFibration (leibnizCotensorMap i f) := by
  intro X
  -- The representable of the Leibniz cotensor map composed with each pullback projection.
  have hfst : representableMap X (leibnizCotensorMap i f) ≫
      (representableLeibnizPullbackObjObj i f X).fst =
        (cotensor.iso V A X).hom ≫ (MonoidalClosed.pre i).app (sHom X A) := by
    rw [representableLeibnizPullbackObjObj_fst, ← Category.assoc, ← representableMap_comp,
      leibnizCotensorMap_fst]
    exact cotensor_iso_hom_naturality_precompose i A X
  have hsnd : representableMap X (leibnizCotensorMap i f) ≫
      (representableLeibnizPullbackObjObj i f X).snd =
        (cotensor.iso V A X).hom ≫ (ihom V).map (representableMap X f.1) := by
    rw [representableLeibnizPullbackObjObj_snd, ← Category.assoc, ← representableMap_comp,
      leibnizCotensorMap_snd]
    exact cotensor_iso_hom_naturality_postcompose (U := V) f.1 X
  -- Hence the representable agrees with the pullback comparison `π` up to a cotensor isomorphism.
  have key : representableMap X (leibnizCotensorMap i f) =
      (cotensor.iso V A X).hom ≫ (representableLeibnizPullbackObjObj i f X).π := by
    refine (representableLeibnizPullbackObjObj i f X).isPullback.hom_ext ?_ ?_
    · rw [hfst, Category.assoc, (representableLeibnizPullbackObjObj i f X).π_fst]
      rfl
    · rw [hsnd, Category.assoc, (representableLeibnizPullbackObjObj i f X).π_snd]
      rfl
  have aiso : Arrow.mk (representableMap X (leibnizCotensorMap i f)) ≅
      Arrow.mk (representableLeibnizPullbackObjObj i f X).π :=
    Arrow.isoMk (cotensor.iso V A X) (Iso.refl _) (by
      simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
      exact key.symm)
  exact (SSet.TrivialFibration.arrow_iso_iff aiso).2
    ((hf X).pullbackObjObjπ (representableLeibnizPullbackObjObj i f X))

/-- **Leibniz cotensor of a representably-trivial isofibration (issue #115, corollary form).** If
`i : U ⟶ V` is a monomorphism of simplicial sets and `f : A ↠ B` is an isofibration that is
representably trivial, then the Leibniz cotensor `leibnizCotensorMap i f` is an
`InfinityCosmos.TrivialFibration`. It is an isofibration by the ∞-cosmos Leibniz cotensor axiom, and
an equivalence because it is representably trivial. This is a corollary of the class-level closure
`representableTrivialFibration_leibnizCotensorMap` via the forward bridge
`RepresentableTrivialFibration.equivalence`; it does not by itself close the
`InfinityCosmos.TrivialFibration` class. See the module docstring. -/
theorem trivialFibration_leibnizCotensorMap {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    {A B : K} (f : A ↠ B) (hf : RepresentableTrivialFibration f.1) :
    TrivialFibration (leibnizCotensorMap i f) :=
  ⟨(leibnizCotensorIsofibration i f).2,
    (representableTrivialFibration_leibnizCotensorMap i f hf).equivalence⟩

end InfinityCosmos
