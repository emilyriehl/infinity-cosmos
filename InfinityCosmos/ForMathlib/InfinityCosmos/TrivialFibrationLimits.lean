/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.TrivialFibration
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Stability of trivial fibrations under conical limits in an ∞-cosmos

This file builds the ∞-cosmos half of the "stability of trivial fibrations under conical
cosmological limits" statement (infinity-cosmos issue #114). The argument follows the issue's
decomposition into two halves:

* **Representables preserve conical limits.** The covariant representable `Fun(X, -)` of a
  pre-∞-cosmos is, on hom-spaces, the enriched coyoneda functor `eCoyoneda SSet X`, which preserves
  every conical limit (`CategoryTheory.Enriched.HasConicalLimit.preservesLimit_eCoyoneda`). It is
  used here in the shapes that appear in the limit axioms of an ∞-cosmos: products and pullbacks.
* **Trivial fibrations of simplicial sets are stable under these limits.** This is the simplicial
  half, recorded in `InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.TrivialFibration`
  (`SSet.TrivialFibration.piMap` and `SSet.TrivialFibration.of_isPullback`).

The bridge between the two is `RepresentableTrivialFibration`: a map `f` in a pre-∞-cosmos for which
every representable `representableMap X f` is a trivial fibration of simplicial sets. A
representably-trivial fibration is an `InfinityCosmos.Equivalence` (its representables are trivial
fibrations between quasi-categories, hence equivalences of quasi-categories), so combined with the
isofibration axioms it is an `InfinityCosmos.TrivialFibration`.

## Main results

* `RepresentableTrivialFibration.equivalence` — a representably-trivial fibration is an equivalence.
* `representableTrivialFibration_piMap` / `representableTrivialFibration_of_isPullback` — the class
  `RepresentableTrivialFibration` is stable under products and under pullback.
* `trivialFibration_piMap` / `trivialFibration_snd_of_isPullback` — an isofibration that is
  representably trivial assembles, through products and pullbacks, into an
  `InfinityCosmos.TrivialFibration`.

## Scope

The product and pullback shapes are closed here. The countable-tower (inverse sequential limit)
shape is *not* closed: the simplicial half is missing, as
`InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.TrivialFibration` has no inverse-limit
stability lemma for `SSet.TrivialFibration`. See the module's note for the precise missing lemma.
-/

universe w v u

namespace CategoryTheory

open Category Limits MonoidalCategory SimplicialCategory EnrichedOrdinaryCategory Enriched SSet

namespace InfinityCosmos

variable {K : Type u} [Category.{v} K]

section PreInfinityCosmos

variable [PreInfinityCosmos.{v} K]

/-- The covariant representable `representableMap X` is the enriched coyoneda functor `eCoyoneda`
acting on a morphism. -/
lemma representableMap_eq_eCoyoneda_map (X : K) {A B : K} (f : A ⟶ B) :
    representableMap X f = (eCoyoneda SSet X).map f :=
  rfl

/-- A morphism in a pre-∞-cosmos is a **representable trivial fibration** if every covariant
representable `Fun(X, -)` sends it to a trivial fibration of simplicial sets. -/
def RepresentableTrivialFibration {A B : K} (f : A ⟶ B) : Prop :=
  ∀ X : K, SSet.TrivialFibration (representableMap X f)

/-- A representably-trivial fibration is an equivalence: each representable is a trivial fibration
between quasi-categories, hence an equivalence of quasi-categories. -/
lemma RepresentableTrivialFibration.equivalence {A B : K} {f : A ⟶ B}
    (hf : RepresentableTrivialFibration f) : Equivalence f := fun X =>
  SSet.TrivialFibration.toQCatEquiv_exists (p := toFunMap X f) (hf X)

end PreInfinityCosmos

section InfinityCosmos

variable [InfinityCosmos.{w, v} K]

/-- **Representables preserve products (issue #114, half (i)) at the level of trivial fibrations.**
A product of representably-trivial fibrations is a representably-trivial fibration: the
representable `eCoyoneda SSet X` carries the product map to the product of the representable maps
(up to the product comparison isomorphism), which is a trivial fibration of simplicial sets by
`SSet.TrivialFibration.piMap`. -/
theorem representableTrivialFibration_piMap {γ : Type w} {A B : γ → K} (φ : ∀ i, A i ⟶ B i)
    (hφ : ∀ i, RepresentableTrivialFibration (φ i)) :
    RepresentableTrivialFibration (Limits.Pi.map φ) := by
  intro X
  rw [representableMap_eq_eCoyoneda_map]
  -- The representables of the factor objects have products, since `eCoyoneda SSet X` preserves the
  -- conical products that exist in the ∞-cosmos.
  haveI hpA : HasProduct (fun i => (eCoyoneda SSet X).obj (A i)) :=
    HasLimit.mk ⟨_, isLimitOfHasProductOfPreservesLimit (eCoyoneda SSet X) (fun i => A i)⟩
  haveI hpB : HasProduct (fun i => (eCoyoneda SSet X).obj (B i)) :=
    HasLimit.mk ⟨_, isLimitOfHasProductOfPreservesLimit (eCoyoneda SSet X) (fun i => B i)⟩
  set eA := asIso (piComparison (eCoyoneda SSet X) (fun i => A i)) with heA
  set eB := asIso (piComparison (eCoyoneda SSet X) (fun i => B i)) with heB
  have hsq : (eCoyoneda SSet X).map (Limits.Pi.map φ) ≫ eB.hom =
      eA.hom ≫ Limits.Pi.map (fun i => (eCoyoneda SSet X).map (φ i)) := by
    apply Limits.Pi.hom_ext
    intro i
    have hL : ((eCoyoneda SSet X).map (Limits.Pi.map φ) ≫ eB.hom) ≫ Pi.π _ i =
        (eCoyoneda SSet X).map (Pi.π A i ≫ φ i) := by
      rw [heB]
      simp only [asIso_hom, Category.assoc, piComparison_comp_π, ← Functor.map_comp,
        Limits.Pi.map_π]
    have hR : (eA.hom ≫ Limits.Pi.map (fun i => (eCoyoneda SSet X).map (φ i))) ≫ Pi.π _ i =
        (eCoyoneda SSet X).map (Pi.π A i ≫ φ i) := by
      rw [heA, asIso_hom, Category.assoc, Limits.Pi.map_π, ← Category.assoc, piComparison_comp_π,
        ← Functor.map_comp]
    rw [hL, hR]
  -- Transport the trivial fibration along the product-comparison arrow isomorphism.
  have htf : SSet.TrivialFibration (Limits.Pi.map (fun i => (eCoyoneda SSet X).map (φ i))) :=
    SSet.TrivialFibration.piMap _ (fun i => hφ i X)
  have aiso : Arrow.mk ((eCoyoneda SSet X).map (Limits.Pi.map φ)) ≅
      Arrow.mk (Limits.Pi.map (fun i => (eCoyoneda SSet X).map (φ i))) :=
    Arrow.isoMk eA eB hsq.symm
  exact (SSet.TrivialFibration.arrow_iso_iff aiso).2 htf

/-- **Representables preserve pullbacks (issue #114, half (i)) at the level of trivial fibrations.**
The pullback of a representably-trivial fibration is a representably-trivial fibration: the
representable `eCoyoneda SSet X` preserves the conical pullback, so it carries the pullback square
to a pullback square of simplicial sets, where `SSet.TrivialFibration.of_isPullback` applies. -/
theorem representableTrivialFibration_of_isPullback {E B A P : K} {p : E ⟶ B} {f : A ⟶ B}
    {fst : P ⟶ E} {snd : P ⟶ A} (h : IsPullback fst snd p f) [HasConicalPullback SSet p f]
    (hp : RepresentableTrivialFibration p) : RepresentableTrivialFibration snd := by
  intro X
  rw [representableMap_eq_eCoyoneda_map]
  have hmap : IsPullback ((eCoyoneda SSet X).map fst) ((eCoyoneda SSet X).map snd)
      ((eCoyoneda SSet X).map p) ((eCoyoneda SSet X).map f) := h.map (eCoyoneda SSet X)
  refine SSet.TrivialFibration.of_isPullback hmap ?_
  rw [← representableMap_eq_eCoyoneda_map]
  exact hp X

/-- **Trivial fibrations in an ∞-cosmos are stable under products (issue #114).** A product of
isofibrations that are representably trivial is an `InfinityCosmos.TrivialFibration`: the product
map is an isofibration by the product axiom, and an equivalence since it is representably trivial.
-/
theorem trivialFibration_piMap {γ : Type w} {A B : γ → K} (f : ∀ i, A i ↠ B i)
    (hf : ∀ i, RepresentableTrivialFibration (f i).1) :
    TrivialFibration (Limits.Pi.map (fun i => (f i).1)) :=
  ⟨prod_map_fibrant f,
    (representableTrivialFibration_piMap (fun i => (f i).1) hf).equivalence⟩

/-- **Trivial fibrations in an ∞-cosmos are stable under pullback (issue #114).** The pullback of an
isofibration that is representably trivial along an arbitrary map is an
`InfinityCosmos.TrivialFibration`: the pulled-back leg is an isofibration by the pullback axiom and
an equivalence because it is representably trivial. -/
theorem trivialFibration_snd_of_isPullback {E B A P : K} (p : E ↠ B) (f : A ⟶ B)
    (fst : P ⟶ E) (snd : P ⟶ A) (h : IsPullback fst snd p.1 f)
    (hp : RepresentableTrivialFibration p.1) : TrivialFibration snd :=
  ⟨pullback_isIsofibration p f fst snd h,
    (representableTrivialFibration_of_isPullback h hp).equivalence⟩

end InfinityCosmos

end InfinityCosmos

end CategoryTheory
