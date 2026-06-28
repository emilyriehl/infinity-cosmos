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
# Stability of the representable trivial-fibration class under conical limits in an ∞-cosmos

This file builds the ∞-cosmos half of infinity-cosmos issue #114. The genuine closure statement
proved here is for the class `RepresentableTrivialFibration`: a map `f` in a pre-∞-cosmos for which
every covariant representable `Fun(X, -) = eCoyoneda SSet X` sends it to a trivial fibration of
simplicial sets. This class is closed under each limit shape of the ∞-cosmos completeness axiom,
with the same hypothesis and conclusion, so the results compose with one another.

The argument follows the issue's decomposition into two halves:

* **Representables preserve conical limits.** The covariant representable `Fun(X, -)` of a
  pre-∞-cosmos is, on hom-spaces, the enriched coyoneda functor `eCoyoneda SSet X`, which preserves
  every conical limit (`CategoryTheory.Enriched.HasConicalLimit.preservesLimit_eCoyoneda`). It is
  used here in the shapes that appear in the limit axioms of an ∞-cosmos: products and pullbacks.
* **Trivial fibrations of simplicial sets are stable under these limits.** This is the simplicial
  half, recorded in `InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.TrivialFibration`
  (`SSet.TrivialFibration.piMap` and `SSet.TrivialFibration.of_isPullback`).

## Main results (representable-class closure)

* `RepresentableTrivialFibration.equivalence`: a representably-trivial fibration is an equivalence.
* `representableTrivialFibration_piMap`, `representableTrivialFibration_of_isPullback`,
  `representableTrivialFibration_tower`: the class `RepresentableTrivialFibration` is closed under
  products, under pullback, and under limits of countable towers. Hypothesis and conclusion are
  both `RepresentableTrivialFibration`, so these are genuine closure statements: an output may be
  re-fed as an input, and they compose.

## Corollaries in the `InfinityCosmos.TrivialFibration` class

* `trivialFibration_piMap`, `trivialFibration_snd_of_isPullback`, `trivialFibration_tower`: an
  isofibration whose connecting maps are representably trivial assembles, through products,
  pullbacks, and towers, into an `InfinityCosmos.TrivialFibration` (`IsIsofibration ∧ Equivalence`).
  Each consumes a `RepresentableTrivialFibration` hypothesis and emits the weaker def-form class via
  the forward bridge `RepresentableTrivialFibration.equivalence`. Only that forward bridge is
  available, so these corollaries are *not* closure statements for `InfinityCosmos.TrivialFibration`
  itself: their `IsIsofibration ∧ Equivalence` output cannot be re-fed as the representable
  hypothesis. The genuine closure lives one level up, in the `representableTrivialFibration_*`
  family above.

## Converse bridge (the next step)

Upgrading the corollaries to genuine closure of `InfinityCosmos.TrivialFibration` requires the
converse of `SSet.TrivialFibration.toIsofibration` together with
`SSet.TrivialFibration.toQCatEquiv_exists`, namely the acyclic-fibration characterization in the
Joyal model structure: an isofibration of quasi-categories that is an equivalence is a trivial
fibration of simplicial sets. That model structure is present neither in mathlib nor in this tree,
so the bridge is recorded here as the open next lemma rather than proved:

```
theorem SSet.TrivialFibration.of_isofibration_of_equiv {A B : QCat} {p : A ⟶ B}
    (hfib : SSet.Isofibration p)
    (he : ∃ e : @QCat.Equiv A.obj B.obj A.property B.property, e.toFun = p.hom) :
    SSet.TrivialFibration p.hom
```

Granting it, the ∞-cosmos converse
`InfinityCosmos.TrivialFibration f → RepresentableTrivialFibration f` follows
representable-by-representable: the isofibration axiom `local_isoFibration` makes each
`toFunMap X f` a quasi-category isofibration and `Equivalence f` supplies the equivalence. That
yields
`RepresentableTrivialFibration f ↔ InfinityCosmos.TrivialFibration f` and turns the four corollaries
into def-in/def-out closure statements.

## Scope

All three limit shapes from the ∞-cosmos completeness axiom are covered: products, pullbacks of
isofibrations, and countable towers of isofibrations. For the tower shape the statement is the
inverse-limit analogue of closure under composition: the projection from the limit of a tower
*of trivial fibrations* is a trivial fibration. The naive levelwise statement for a *map* of towers
(every component a trivial fibration) is false, by a Mittag-Leffler-type obstruction; see the note
in `InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.TrivialFibration`.
-/

universe w v u

namespace CategoryTheory

open Category Limits MonoidalCategory SimplicialCategory EnrichedOrdinaryCategory Enriched SSet
open PreInfinityCosmos

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

/-- **Products of representably-trivial isofibrations (issue #114, corollary form).** A product of
isofibrations that are representably trivial is an `InfinityCosmos.TrivialFibration`: the product
map is an isofibration by the product axiom, and an equivalence since it is representably trivial.
This is a corollary of the class-level closure `representableTrivialFibration_piMap` via the forward
bridge `RepresentableTrivialFibration.equivalence`; because only that forward bridge exists, it does
not by itself close the `InfinityCosmos.TrivialFibration` class (its `IsIsofibration ∧ Equivalence`
output cannot be re-fed as the representable hypothesis). See the module docstring. -/
theorem trivialFibration_piMap {γ : Type w} {A B : γ → K} (f : ∀ i, A i ↠ B i)
    (hf : ∀ i, RepresentableTrivialFibration (f i).1) :
    TrivialFibration (Limits.Pi.map (fun i => (f i).1)) :=
  ⟨prod_map_fibrant f,
    (representableTrivialFibration_piMap (fun i => (f i).1) hf).equivalence⟩

/-- **Pullback of a representably-trivial isofibration (issue #114, corollary form).** The pullback
of an isofibration that is representably trivial along an arbitrary map is an
`InfinityCosmos.TrivialFibration`: the pulled-back leg is an isofibration by the pullback axiom and
an equivalence because it is representably trivial. This is a corollary of the class-level closure
`representableTrivialFibration_of_isPullback` via the forward bridge
`RepresentableTrivialFibration.equivalence`; it does not by itself close the
`InfinityCosmos.TrivialFibration` class. See the module docstring. -/
theorem trivialFibration_snd_of_isPullback {E B A P : K} (p : E ↠ B) (f : A ⟶ B)
    (fst : P ⟶ E) (snd : P ⟶ A) (h : IsPullback fst snd p.1 f)
    (hp : RepresentableTrivialFibration p.1) : TrivialFibration snd :=
  ⟨pullback_isIsofibration p f fst snd h,
    (representableTrivialFibration_of_isPullback h hp).equivalence⟩

/-- **Representables preserve tower limits (issue #114, half (i)) at the level of trivial
fibrations.** Let `F : ℕᵒᵖ ⥤ K` be a tower of isofibrations whose connecting maps are all
representably trivial. The conical limit of `F` exists by the tower-limit axiom, and each
representable `eCoyoneda SSet X` preserves it. The image tower `F ⋙ eCoyoneda SSet X` is therefore
a tower of trivial fibrations of simplicial sets, so its limit projection — the representable of
`limit.π F (.op 0)` — is a trivial fibration by `SSet.TrivialFibration.of_isLimit_tower`. -/
theorem representableTrivialFibration_tower (F : ℕᵒᵖ ⥤ K)
    (hfib : ∀ n : ℕ, IsIsofibration (F.map (homOfLE (Nat.le_succ n)).op))
    (htriv : ∀ n : ℕ, RepresentableTrivialFibration (F.map (homOfLE (Nat.le_succ n)).op)) :
    haveI := has_limits_of_towers F hfib
    RepresentableTrivialFibration (limit.π F (.op 0)) := by
  haveI := has_limits_of_towers F hfib
  intro X
  rw [representableMap_eq_eCoyoneda_map]
  have hc : IsLimit ((eCoyoneda SSet X).mapCone (limit.cone F)) :=
    isLimitOfPreserves (eCoyoneda SSet X) (limit.isLimit F)
  have hf : ∀ n : ℕ,
      SSet.TrivialFibration ((F ⋙ eCoyoneda SSet X).map (homOfLE (Nat.le_succ n)).op) := by
    intro n
    have h := htriv n X
    rw [representableMap_eq_eCoyoneda_map] at h
    exact h
  exact SSet.TrivialFibration.of_isLimit_tower _ hc hf

/-- **Limit of a tower of representably-trivial isofibrations (issue #114, corollary form).** Given
a tower `F : ℕᵒᵖ ⥤ K` of isofibrations that are representably trivial, the projection
`limit.π F (.op 0)` from its conical limit is an `InfinityCosmos.TrivialFibration`: it is an
isofibration by the tower-limit axiom, and an equivalence because it is representably trivial. This
is a corollary of the class-level closure `representableTrivialFibration_tower` via the forward
bridge `RepresentableTrivialFibration.equivalence`; it does not by itself close the
`InfinityCosmos.TrivialFibration` class. See the module docstring.

This is the inverse-limit analogue of closure under composition. Note that the levelwise statement
for a *map* of towers is false; see the note in
`InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.TrivialFibration`. -/
theorem trivialFibration_tower (F : ℕᵒᵖ ⥤ K)
    (hfib : ∀ n : ℕ, IsIsofibration (F.map (homOfLE (Nat.le_succ n)).op))
    (htriv : ∀ n : ℕ, RepresentableTrivialFibration (F.map (homOfLE (Nat.le_succ n)).op)) :
    haveI := has_limits_of_towers F hfib
    TrivialFibration (limit.π F (.op 0)) :=
  haveI := has_limits_of_towers F hfib
  ⟨has_limits_of_towers_isIsofibration F hfib,
    (representableTrivialFibration_tower F hfib htriv).equivalence⟩

end InfinityCosmos

end InfinityCosmos

end CategoryTheory
