/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Ordinary
import Mathlib.CategoryTheory.Limits.Preserves.Limits

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

namespace CategoryTheory

open Limits Opposite

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable {F : J ⥤ C} (c : Cone F) (X : C)

-- TODO: move to Mathlib.CategoryTheory.Enriched.Basic
/-- enriched coyoneda functor `(X ⟶[V] _) : C ⥤ V`. -/
abbrev eCoyoneda := (eHomFunctor V C).obj (op X)

/--
A limit cone `c` in a `V`-enriched ordinary category `C` is a *`V`-enriched limit*
(or *conical limit*) if for every `X : C`, the cone obtained by applying the coyoneda
functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
-/
structure IsConicalLimit where
  /-- A conical limit cone is a limit cone. -/
  isLimit : IsLimit c
  /--
  The cone obtained by applying the coyoneda functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
  -/
  isConicalLimit (X : C) : IsLimit <| (eCoyoneda V X).mapCone c

namespace IsConicalLimit

variable {V}

/-- Transport evidence that a cone is a `V`-enriched limit cone across an isomorphism of cones. -/
noncomputable def ofIso {r₁ r₂ : Cone F} (h : IsConicalLimit V r₁)
    (i : r₁ ≅ r₂) : IsConicalLimit V r₂ where
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
variable (V) [HasLimitsOfShape J V]

/-- The canonical comparison map with the limit in `V`. -/
noncomputable def limitComparison : (X ⟶[V] c.pt) ⟶ limit (F ⋙ eCoyoneda V X) :=
  limit.lift _ <| (eCoyoneda V X).mapCone c

variable {V}

lemma limitComparison_eq_conePointUniqueUpToIso (h : IsConicalLimit V c)
    [HasLimit (F ⋙ eCoyoneda V X)] :
    limitComparison V c X =
    ((h.isConicalLimit X).conePointUniqueUpToIso (limit.isLimit _)).hom := by
  apply limit.hom_ext
  simp [limitComparison]

/-- `IsConicalLimit.limitComparison` is an isomorphism. -/
lemma isIso_limitComparison (h : IsConicalLimit V c) : IsIso (limitComparison V c X) := by
  rw [limitComparison_eq_conePointUniqueUpToIso (h := h)]
  infer_instance

/-- For all `X : C`, the canonical comparison map with the limit in `V` as isomorphism -/
noncomputable def limitComparisonIso (h : IsConicalLimit V c) :
    (X ⟶[V] c.pt) ≅ (limit (F ⋙ eCoyoneda V X)) := by
  have := isIso_limitComparison c X h
  exact (asIso (limitComparison V c X))

variable (V) in
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
Note: use the two directions `limitComparisonIso` and `ofIsIsoLimitComparison` directly.
-/
theorem nonempty_isConicalLimit_iff (hc : IsLimit c) : Nonempty (IsConicalLimit V c) ↔
    ∀ X, IsIso (IsConicalLimit.limitComparison V c X) := by
  constructor
  · intro ⟨h⟩ X
    exact isIso_limitComparison c X h
  · intro h
    exact ⟨ofIsIsoLimitComparison V c hc⟩

end IsConicalLimit

variable (F)

/-- `ConicalLimitCone V F` contains a cone over `F` together with the information that it is a
conical limit. -/
structure ConicalLimitCone where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isConicalLimit : IsConicalLimit V cone

/-- `HasConicalLimit F` represents the mere existence of a limit for `F`. -/
class HasConicalLimit : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_conicalLimitCone : Nonempty (ConicalLimitCone V F)

variable {F} in

theorem HasConicalLimit.mk (d : ConicalLimitCone V F) : HasConicalLimit V F := ⟨⟨d⟩⟩

variable [HasConicalLimit V F]

/-- Use the axiom of choice to extract explicit `ConicalLimitCone F` from `HasConicalLimit F`. -/
noncomputable def getConicalLimitCone : ConicalLimitCone V F :=
  Classical.choice <| HasConicalLimit.exists_conicalLimitCone

/-! Interface to the `HasConicalLimit` class. -/

/-- An arbitrary choice of conical limit cone for a functor. -/
noncomputable def conicalLimitCone : ConicalLimitCone V F :=
  (getConicalLimitCone V F)

/-- An arbitrary choice of conical limit object of a functor. -/
noncomputable def conicalLimit := (conicalLimitCone V F).cone.pt

instance HasConicalLimit.hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := (conicalLimitCone V F).cone,
    isLimit := (getConicalLimitCone V F).isConicalLimit.isLimit }

namespace conicalLimit

/-- The projection from the conical limit object to a value of the functor. -/
protected noncomputable def π (j : J) : conicalLimit V F ⟶ F.obj j :=
  (conicalLimitCone V F).cone.π.app j

@[reassoc (attr := simp)]
protected theorem w {j j' : J} (f : j ⟶ j') :
    conicalLimit.π V F j ≫ F.map f = conicalLimit.π V F j' := (conicalLimitCone V F).cone.w f

/-- Evidence that the arbitrary choice of cone provided by `(conicalLimitCone V F).cone` is a
conical limit cone. -/
noncomputable def isConicalLimit : IsConicalLimit V (conicalLimitCone V F).cone :=
  (getConicalLimitCone V F).isConicalLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
noncomputable def lift :
    c.pt ⟶ conicalLimit V F := (conicalLimit.isConicalLimit V F).isLimit.lift c

@[reassoc (attr := simp)]
theorem lift_π (j : J) :
    conicalLimit.lift V F c ≫ conicalLimit.π V F j = c.π.app j :=
  IsLimit.fac _ c j

end conicalLimit

variable (J C)

/-- `C` has conical limits of shape `J` if there exists a conical limit for every functor
`F : J ⥤ C`. -/
class HasConicalLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits. -/
  hasConicalLimit : ∀ F : J ⥤ C, HasConicalLimit V F := by infer_instance

namespace HasConicalLimitsOfShape

variable [HasConicalLimitsOfShape J V C]

-- see Note [lower instance priority]
instance (priority := 100) : HasConicalLimit V F :=
  HasConicalLimitsOfShape.hasConicalLimit F

instance : HasLimitsOfShape J C where
  has_limit _ := inferInstance

end HasConicalLimitsOfShape

section Equivalence

variable {J} {C}

variable {F} in

/-- If a functor `F` has a conical limit, so does any naturally isomorphic functor. -/
theorem HasConicalLimit.ofIso {G : J ⥤ C} (α : F ≅ G) : HasConicalLimit V G :=
  HasConicalLimit.mk V
    { cone := (Cones.postcompose α.hom).obj (conicalLimitCone V F).cone
      isConicalLimit := {
        isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (conicalLimit.isConicalLimit V F).isLimit
        isConicalLimit := fun X ↦ by
          let iso := Functor.mapConePostcompose (eCoyoneda V X) (α := α.hom)
            (c := (conicalLimitCone V F).cone)
          have :=
            (IsLimit.postcomposeHomEquiv (isoWhiskerRight α (eCoyoneda V X)) _).symm
              ((conicalLimit.isConicalLimit V F).isConicalLimit X)
          exact this.ofIsoLimit (id iso.symm)
      }
    }

instance hasConicalLimitEquivalenceComp (e : K ≌ J) :
    HasConicalLimit V (e.functor ⋙ F) :=
  HasConicalLimit.mk V
    { cone := Cone.whisker e.functor (conicalLimitCone V F).cone
      isConicalLimit := {
        isLimit := IsLimit.whiskerEquivalence (conicalLimit.isConicalLimit V F).isLimit e
        isConicalLimit := fun X ↦
          IsLimit.whiskerEquivalence ((conicalLimit.isConicalLimit V F).isConicalLimit X) e
        }
    }

omit [HasConicalLimit V F] in

/-- If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`. -/
theorem hasConicalLimitOfEquivalenceComp (e : K ≌ J)
    [HasConicalLimit V (e.functor ⋙ F)] : HasConicalLimit V F := by
  have : HasConicalLimit V (e.inverse ⋙ e.functor ⋙ F) :=
    hasConicalLimitEquivalenceComp V _ e.symm
  apply HasConicalLimit.ofIso V (e.invFunIdAssoc F)

/-- We can transport conical limits of shape `J` along an equivalence `J ≌ K`. -/
theorem hasConicalLimitsOfShape_of_equivalence (e : J ≌ K) [HasConicalLimitsOfShape J V C] :
    HasConicalLimitsOfShape K V C := by
  constructor
  intro F
  apply hasConicalLimitOfEquivalenceComp V _ e

end Equivalence

/--
`C` has all conical limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has conical limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
@[pp_with_univ]
class HasConicalLimitsOfSize : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have conical limits -/
  hasConicalLimitsOfShape : ∀ (J : Type u₁) [Category.{v₁} J], HasConicalLimitsOfShape J V C := by
    infer_instance

namespace HasConicalLimitsOfSize

variable {J}

-- see Note [lower instance priority]
instance (priority := 100)
    [HasConicalLimitsOfSize.{v₁, u₁} V C] : HasConicalLimitsOfShape J V C :=
  HasConicalLimitsOfSize.hasConicalLimitsOfShape J

instance hasLimitsOfSize [h : HasConicalLimitsOfSize.{v₁, u₁} V C] :
    HasLimitsOfSize.{v₁, u₁} C where
  has_limits_of_shape := fun J ↦
    have := h.hasConicalLimitsOfShape J
    inferInstance

/-- A category that has larger conical limits also has smaller conical limits. -/
theorem hasConicalLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [h : HasConicalLimitsOfSize.{v₁, u₁} V C] : HasConicalLimitsOfSize.{v₂, u₂} V C where
  hasConicalLimitsOfShape J {_} :=
    have := h.hasConicalLimitsOfShape (Shrink.{u₁, u₂} (ShrinkHoms.{u₂} J))
    hasConicalLimitsOfShape_of_equivalence V
      ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm

/-- `HasConicalLimitsOfSize.shrink.{v u} C` tries to obtain `HasConicalLimitsOfSize.{v u} C`
from some other `HasConicalLimitsOfSize C`.
-/
theorem shrink [HasConicalLimitsOfSize.{max v₁ v₂, max u₁ u₂} V C] :
    HasConicalLimitsOfSize.{v₁, u₁} V C :=
  hasConicalLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} V C

end HasConicalLimitsOfSize

/-- `C` has all (small) conical limits if it has limits of every shape that is as big as its
hom-sets.-/
abbrev HasConicalLimits (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop :=
  HasConicalLimitsOfSize.{v, v} V C

namespace HasConicalLimits

instance (priority := 100) hasSmallestConicalLimitsOfHasConicalLimits [HasConicalLimits V C] :
    HasConicalLimitsOfSize.{0, 0} V C := HasConicalLimitsOfSize.shrink.{0, 0} V C

instance [HasConicalLimits V C] : HasLimits C := inferInstance

instance {C : Type u} [Category.{v} C]
    [EnrichedOrdinaryCategory V C] [HasConicalLimits V C] (J : Type v)
    [Category.{v} J] : HasConicalLimitsOfShape J V C :=
  HasConicalLimitsOfSize.hasConicalLimitsOfShape J

end HasConicalLimits

/-! ## Conical Terminal -/

section ConicalTerminal

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

instance HasConicalTerminal_hasTerminal [hyp : HasConicalTerminal V C] : HasTerminal C :=
  inferInstance

end ConicalTerminal

/-! ## Conical Products -/

variable {C}

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalProduct {I : Type w} (f : I → C) := HasConicalLimit V (Discrete.functor f)

instance HasConicalProduct_hasProduct {I : Type w} (f : I → C) [HasConicalProduct V f] :
    HasProduct f := inferInstance

variable (C)

/-- Has conical products if all discrete diagrams of bounded size have conical products. -/
class HasConicalProducts : Prop where
  /-- All discrete diagrams of bounded size have conical products. -/
  hasConicalLimitsOfShape : ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) V C := by
    infer_instance

namespace HasConicalProducts

instance hasProducts [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasProducts.{w, v, u} C := by
  intro I
  constructor
  intro f
  have := hyp.hasConicalLimitsOfShape I
  have : HasConicalLimit V f := inferInstance
  infer_instance

instance hasConicalTerminal [hyp : HasConicalProducts.{0, v', v, u} V C] :
    HasConicalTerminal V C := hyp.hasConicalLimitsOfShape PEmpty.{1}

instance hasConicalTerminal' [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasConicalTerminal V C := by
  have inst := hyp.hasConicalLimitsOfShape PEmpty
  exact hasConicalLimitsOfShape_of_equivalence V (J := Discrete PEmpty.{w + 1}) emptyEquivalence

end HasConicalProducts

/-! ## Conical Pullbacks -/
section ConicalPullbacks

variable {C}

/-- `HasPullback f g` represents a particular choice of conical limit cone for the pair
of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` -/
abbrev HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasConicalLimit V (cospan f g)

instance HasConicalPullback_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasConicalPullback V f g] : HasPullback f g :=
  inferInstance

variable (C)

/-- `HasConicalPullbacks` represents a choice of conical pullback for every pair of morphisms -/
abbrev HasConicalPullbacks : Prop := HasConicalLimitsOfShape WalkingCospan V C

instance HasConicalPullbacks_hasPullbacks [hyp : HasConicalPullbacks V C] : HasPullbacks C :=
  inferInstance

end ConicalPullbacks

-- TODO: Add something for conical inverse limits of towers?

end CategoryTheory
