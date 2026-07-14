/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Isofibrations

open scoped Simplicial

/-!
# Representables preserve the Leibniz cotensor pullback square

The Leibniz cotensor of a monomorphism `i : U ⟶ V` with an isofibration `f : A ↠ B` is defined
through a chosen pullback square (`leibnizCotensor.isPullback`). This file records that every
covariant representable `Fun(X, -) = eCoyoneda SSet X` preserves that square, since it preserves the
conical pullback supplied by the isofibration-pullback axiom.

This is the bridge used to transport the Leibniz cotensor pullback square through representables
when proving that the Leibniz cotensor of a representably-trivial isofibration is again
representably trivial.
-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos
open HasConicalTerminal
open MonoidalCategory BraidedCategory

variable {K : Type u} [Category.{v} K] [InfinityCosmos.{0} K]

/-- Covariant representables preserve the chosen Leibniz cotensor pullback square. -/
theorem leibnizCotensor.representableIsPullback {U V : SSet.{v}} (i : U ⟶ V)
    [Mono i] {A B : K} (f : A ↠ B) (X : K) :
    IsPullback (representableMap X (leibnizCotensor.fst i f))
      (representableMap X (leibnizCotensor.snd i f))
      (representableMap X (cotensorCovMap U f.1))
      (representableMap X (cotensorContraMap i B)) := by
  haveI : HasConicalPullback SSet (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
  change IsPullback ((eCoyoneda SSet X).map (leibnizCotensor.fst i f))
    ((eCoyoneda SSet X).map (leibnizCotensor.snd i f))
    ((eCoyoneda SSet X).map (cotensorCovMap U f.1))
    ((eCoyoneda SSet X).map (cotensorContraMap i B))
  exact (leibnizCotensor.isPullback i f).map (eCoyoneda SSet X)

end InfinityCosmos
