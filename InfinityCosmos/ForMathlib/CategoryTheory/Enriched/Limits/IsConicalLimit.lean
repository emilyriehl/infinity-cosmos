/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Dagur Asgeirsson, Emily Riehl
-/
-- import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
-- import Mathlib.CategoryTheory.Limits.Preserves.Limits
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

/-!
# Conical limits in enriched ordinary categories

A limit cone in the underlying category of an enriched ordinary category is a *conical limit* if
it is a limit cone in the underlying ordinary category and moreover this limit cone is preserved
by covariant enriched representable functors. These conditions are encoded in the structure
`IsConicalLimit`.

The universal property of a conical limit is enriched as follows: the canonical comparison map
defines an isomorphism in the enriching category:

`limitComparisonIso (h : IsConicalLimit V c) : (X ⟶[V] c.pt) ≅ (limit (F ⋙ eCoyoneda V X))`

Conversely, if the canonical maps define isomorphisms for all `X` then `c` is a conical limit cone:

`ofIsIsoLimitComparison [∀ X, IsIso (IsConicalLimit.limitComparison V c X)]`
`(hc : IsLimit c) : IsConicalLimit V c`

This file develops some general API for conical limits in enriched ordinary categories.

TODO: Dualize everything to define conical colimits.

-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

/--
A limit cone `c` in a `V`-enriched ordinary category `C` is a *`V`-enriched limit*
(or *conical limit*) if for every `X : C`, the cone obtained by applying the coyoneda
functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
-/
structure IsConicalLimit {J : Type u₁} [Category.{v₁} J]
    (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
    {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
    {F : J ⥤ C} (c : Cone F) where
  /-- A conical limit cone is a limit cone. -/
  isLimit : IsLimit c
  /--
  The cone obtained by applying the coyoneda functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
  -/
  isConicalLimit (X : C) : IsLimit <| (eCoyoneda V X).mapCone c

variable {J : Type u₁} [Category.{v₁} J]
variable {V : Type u'} [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable {F : J ⥤ C} {c d : Cone F}

namespace IsConicalLimit

open IsLimit in
lemma hasConicalLimit (hc : IsConicalLimit V c) : HasConicalLimit V F where
  exists_limit := ⟨c, hc.isLimit⟩
  preservesLimit_eCoyoneda X := {
    preserves {_d} hd :=
      let iso_cd := uniqueUpToIso hc.isLimit hd
      let isLimit_mapCone := hc.isConicalLimit X
      ⟨ofIsoLimit isLimit_mapCone ((Cones.functoriality F (eCoyoneda V X)).mapIso iso_cd)⟩}

/-- Transport evidence that a cone is a `V`-enriched limit cone across an isomorphism of cones. -/
noncomputable def of_iso (h : IsConicalLimit V c) (i : c ≅ d) :
    IsConicalLimit V d where
  isLimit := h.isLimit.ofIsoLimit i
  isConicalLimit X := h.isConicalLimit X |>.ofIsoLimit
    { hom := Functor.mapConeMorphism _ i.hom
      inv := Functor.mapConeMorphism _ i.inv
      hom_inv_id := by simp only [Functor.mapCone, Functor.mapConeMorphism, Iso.map_hom_inv_id]
      inv_hom_id := by simp only [Functor.mapCone, Functor.mapConeMorphism, Iso.map_inv_hom_id] }


/-!
## Characterization in terms of the comparison map.

There is a canonical comparison map with the limit in `V`, the following proves that a limit
cone in `C` is a `V`-enriched limit if and only if the comparison map is an isomorphism
for every `X : C`.
-/

-- Adjusting the size of `J` would also work, but this is more universe polymorphic.
variable [HasLimitsOfShape J V]

variable (V) (X : C)

variable (c) in

/-- The canonical comparison map with the limit in `V`. -/
noncomputable def limitComparison : (X ⟶[V] c.pt) ⟶ limit (F ⋙ eCoyoneda V X) :=
  limit.lift _ <| (eCoyoneda V X).mapCone c

variable {V} in

lemma limitComparison_eq_conePointUniqueUpToIso (h : IsConicalLimit V c)
    [HasLimit (F ⋙ eCoyoneda V X)] :
    limitComparison V c X =
    ((h.isConicalLimit X).conePointUniqueUpToIso (limit.isLimit _)).hom := by
  apply limit.hom_ext
  simp [limitComparison]

variable {V} in

/-- `IsConicalLimit.limitComparison` is an isomorphism. -/
lemma isIso_limitComparison (h : IsConicalLimit V c) : IsIso (limitComparison V c X) := by
  rw [limitComparison_eq_conePointUniqueUpToIso (h := h)]
  infer_instance

variable {V} in

/-- For all `X : C`, the canonical comparison map with the limit in `V` as isomorphism -/
noncomputable def limitComparisonIso (h : IsConicalLimit V c) :
    (X ⟶[V] c.pt) ≅ (limit (F ⋙ eCoyoneda V X)) := by
  have : IsIso (limitComparison V c X) := isIso_limitComparison X h
  exact (asIso (limitComparison V c X))


/-- Reverse direction: if the comparison map is an isomorphism, then `c` is a conical limit. -/
noncomputable def ofIsIsoLimitComparison
    [∀ X, IsIso (IsConicalLimit.limitComparison V c X)]
    (hc : IsLimit c) : IsConicalLimit V c where
  isLimit := hc
  isConicalLimit X := by
    suffices PreservesLimit F (eCoyoneda V X) from
      Classical.choice (this.preserves hc)
    have : HasLimit F := ⟨c, hc⟩
    apply (config := { allowSynthFailures := true }) preservesLimit_of_isIso_post
    have h : limit.post F (eCoyoneda V X) =
      ((eCoyoneda V X).map ((limit.isLimit F).conePointUniqueUpToIso hc).hom) ≫
        limitComparison V c X := by
      apply limit.hom_ext
      intro j
      simp [limitComparison, ← eHomWhiskerLeft_comp]
    rw [h]
    infer_instance

/--
A limit cone in `C` is a `V`-enriched limit if and only if the comparison map is an isomorphism
for every `X : C`.
Note: it's easier to use the two directions `limitComparisonIso` and
`ofIsIsoLimitComparison` directly.
-/
theorem nonempty_isConicalLimit_iff (hc : IsLimit c) : Nonempty (IsConicalLimit V c) ↔
    ∀ X, IsIso (limitComparison V c X) := by
  constructor
  · intro ⟨h⟩ X
    exact isIso_limitComparison X h
  · intro h
    exact ⟨ofIsIsoLimitComparison V hc⟩

end IsConicalLimit

namespace HasConicalLimit

variable (V) [HasConicalLimit V F]
namespace conicalLimit

variable (F)

/-- Evidence that the arbitrary choice of cone provided by `(conicalLimitCone V F).cone` is a
conical limit cone. -/
noncomputable def isConicalLimit : IsConicalLimit V (conicalLimitCone V F).limitCone.cone where
  isLimit := (getConicalLimitCone V F).limitCone.isLimit
  isConicalLimit X := (getConicalLimitCone V F).isConicalLimit X

variable (c) in
/-- The morphism from the cone point of any other cone to the limit object. -/
noncomputable def lift [HasConicalLimit V F] : c.pt ⟶ conicalLimit V F :=
  (conicalLimit.isConicalLimit V F).isLimit.lift c

@[reassoc (attr := simp)]
theorem lift_π (j : J) :
    conicalLimit.lift V F c ≫ conicalLimit.π V F j = c.π.app j :=
  IsLimit.fac _ c j

end HasConicalLimit.conicalLimit

end CategoryTheory.Enriched
