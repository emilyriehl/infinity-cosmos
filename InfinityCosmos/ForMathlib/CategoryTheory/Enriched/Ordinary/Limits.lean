/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dagur Asgeirsson, Jon Eugster
-/
import Mathlib.CategoryTheory.Enriched.Ordinary
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Conical limits / enriched limits


-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory

open Limits EnrichedOrdinaryCategory Opposite

variable {J : Type u₁} [Category.{v₁} J]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

section

variable {F : J ⥤ C} (c : Cone F)

/--
A limit cone `c` in a `V`-enriched ordinary category `C` is a *`V`-enriched limit* if for every
`X : C`, the cone obtained by applying the coyoneda functor `(X ⟶[V] -)` to `c` is a
limit cone in `V`.
-/
structure IsConicalLimit where
  isLimit : IsLimit c
  isConicalLimit (X : C) : IsLimit <| ((eHomFunctor V C).obj (op X)).mapCone c

/-- Conical simplicial limits are also limits in the unenriched sense. -/
def IsConicalLimit_islimit (slim : IsConicalLimit V c) : IsLimit c := slim.isLimit

/-- Transport evidence that a cone is a `V`-enriched limit cone across
an isomorphism of cones. -/
noncomputable def IsConicalLimit.ofIsoConicalLimit {r t : Cone F} (h : IsConicalLimit V r)
    (i : r ≅ t) : IsConicalLimit V t where
  isLimit := h.isLimit.ofIsoLimit i
  isConicalLimit X := h.isConicalLimit X |>.ofIsoLimit
    { hom := Functor.mapConeMorphism _ i.hom
      inv := Functor.mapConeMorphism _ i.inv
      hom_inv_id := by
        simp only [Functor.mapCone, Functor.mapConeMorphism, Iso.map_hom_inv_id]
      inv_hom_id := by
        simp only [Functor.mapCone, Functor.mapConeMorphism, Iso.map_inv_hom_id] }

namespace EnrichedOrdinaryCategory

/-!
# Characterization in terms of the comparison map.

There is a canonical comparison map with the limit in `V`, the following proves that a limit
cone in `C` is a simplicially enriched limit if and only if the comparison map is an isomorphism
for every `X : C`.
-/

-- Adjusting the size of `J` would also work, but this is more universe polymorphic.
variable [HasLimitsOfShape J V]

noncomputable def limitComparison (X : C)  :
    (X ⟶[V] c.pt) ⟶ limit (F ⋙ (eHomFunctor V C).obj (op X)) :=
  limit.lift _ (((eHomFunctor V C).obj (op X)).mapCone c)

lemma limitComparison_eq_conePointUniqueUpToIso (X : C) (h : IsConicalLimit V c)
    [HasLimit (F ⋙ (eHomFunctor V C).obj (op X))] :
    limitComparison V c X = ((h.isConicalLimit X).conePointUniqueUpToIso (limit.isLimit _)).hom := by
  apply limit.hom_ext
  simp [limitComparison]

lemma isIso_limitComparison (X : C) (h : IsConicalLimit V c) : IsIso (limitComparison V c X) := by
  rw [limitComparison_eq_conePointUniqueUpToIso (h := h)]
  infer_instance

noncomputable def limitComparisonIso (X : C) (h : IsConicalLimit V c) :
    (X ⟶[V] c.pt) ≅ (limit (F ⋙ (eHomFunctor V C).obj (op X))) := by
  have := isIso_limitComparison V c X h
  exact (asIso (EnrichedOrdinaryCategory.limitComparison V c X))

noncomputable def isConicalLimitOfIsIsoLimitComparison [∀ X, IsIso (limitComparison V c X)]
    (hc : IsLimit c) : IsConicalLimit V c where
  isLimit := hc
  isConicalLimit X := by
    suffices PreservesLimit F ((eHomFunctor V C).obj (op X)) from Classical.choice (this.preserves hc)
    have : HasLimit F := ⟨c, hc⟩
    apply (config := { allowSynthFailures := true } ) preservesLimit_of_isIso_post
    have : limit.post F ((eHomFunctor V C).obj (op X)) =
      (((eHomFunctor V C).obj (op X)).map ((limit.isLimit F).conePointUniqueUpToIso hc).hom) ≫
        limitComparison V c X := by
      apply limit.hom_ext
      intro j
      simp [eHomFunctor_obj_obj, Functor.comp_obj, limit.post_π, eHomFunctor_obj_map,
        limit.cone_x, Category.assoc, limitComparison, Category.assoc, limit.lift_π,
        Functor.mapCone_pt, Functor.mapCone_π_app,
        ← eHomWhiskerLeft_comp, IsLimit.conePointUniqueUpToIso_hom_comp,
        limit.cone_x, limit.cone_π]
    rw [this]
    infer_instance

end EnrichedOrdinaryCategory

end

section ConicalLimits

/-- `ConicalLimitCone V F` contains a cone over `F` together with the information that it is a conical
limit. -/
structure ConicalLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isConicalLimit : IsConicalLimit V cone

/-- A conical limit cone is a limit cone. -/
def ConicalLimitCone_isLimitCone {F : J ⥤ C} (cone : Cone F) (slim : IsConicalLimit V cone) :
    IsLimit cone := slim.isLimit

/-- `HasConicalLimit F` represents the mere existence of a limit for `F`. -/
class HasConicalLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_limit : Nonempty (ConicalLimitCone V F)

theorem HasConicalLimit.mk {F : J ⥤ C} (d : ConicalLimitCone V F) : HasConicalLimit V F :=
  ⟨Nonempty.intro d⟩

variable (F : J ⥤ C) [HasConicalLimit V F]

/-- Use the axiom of choice to extract explicit `ConicalLimitCone F` from `HasConicalLimit F`. -/
noncomputable def getConicalLimitCone : ConicalLimitCone V F :=
  Classical.choice <| HasConicalLimit.exists_limit

-- TODO: not an instance because `V` is explicit
def HasConicalLimit_hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := (getConicalLimitCone V F).cone,
    isLimit := ConicalLimitCone_isLimitCone V _ (getConicalLimitCone V F).isConicalLimit
    }

-- Interface to the `HasConicalLimit` class.
/-- An arbitrary choice of limit cone for a functor. -/
noncomputable def conicalLimit.cone (F : J ⥤ C) [HasConicalLimit V F] : Cone F :=
  (getConicalLimitCone V F).cone

/-- An arbitrary choice of conical limit object of a functor. -/
noncomputable def conicalLimit (F : J ⥤ C) [HasConicalLimit V F] :=
  (conicalLimit.cone V F).pt

/-- The projection from the conical limit object to a value of the functor. -/
noncomputable def conicalLimit.π (F : J ⥤ C) [HasConicalLimit V F] (j : J) :
    conicalLimit V F ⟶ F.obj j := (conicalLimit.cone V F).π.app j


@[reassoc (attr := simp)]
theorem conicalLimit.w (F : J ⥤ C) [HasConicalLimit V F] {j j' : J} (f : j ⟶ j') :
    conicalLimit.π V F j ≫ F.map f = conicalLimit.π V F j' :=
  (conicalLimit.cone V F).w f

/-- Evidence that the arbitrary choice of cone provided by `conicalLimit.cone F` is a conical
limit cone. -/
noncomputable def conicalLimit.isConicalLimit (F : J ⥤ C) [HasConicalLimit V F] :
    IsConicalLimit V (conicalLimit.cone V F) := (getConicalLimitCone V F).isConicalLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
noncomputable def conicalLimit.lift (F : J ⥤ C) [HasConicalLimit V F] (c : Cone F) :
    c.pt ⟶ conicalLimit V F := (conicalLimit.isConicalLimit V F).isLimit.lift c

@[reassoc (attr := simp)]
theorem conicalLimit.lift_π {F : J ⥤ C} [HasConicalLimit V F] (c : Cone F) (j : J) :
    conicalLimit.lift V F c ≫ conicalLimit.π V F j = c.π.app j :=
  IsLimit.fac _ c j

variable (J C)

/-- `C` has conical limits of shape `J` if there exists a conical limit for every functor
`F : J ⥤ C`. -/
class HasConicalLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits -/
  has_conical_limit : ∀ F : J ⥤ C, HasConicalLimit V F := by infer_instance

-- see Note [lower instance priority]
instance (priority := 100) hasConicalLimitOfHasConicalLimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [EnrichedOrdinaryCategory V C] [HasConicalLimitsOfShape J V C] (F : J ⥤ C) : HasConicalLimit V F :=
  HasConicalLimitsOfShape.has_conical_limit F

-- TODO; not an instance anymore
def HasConicalLimitsOfShape_hasLimitsOfShape [h : HasConicalLimitsOfShape J V C] :
    HasLimitsOfShape J C where
  has_limit F :=
    have := h.has_conical_limit
    HasConicalLimit_hasLimit V F

section Equivalence

variable {K : Type u₂} [Category.{v₂} K]
variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- If a functor `F` has a conical limit, so does any naturally isomorphic functor.
-/
theorem hasConicalLimitOfIso {F G : J ⥤ C} [HasConicalLimit V F] (α : F ≅ G) : HasConicalLimit V G :=
  HasConicalLimit.mk V
    { cone := (Cones.postcompose α.hom).obj (conicalLimit.cone V F)
      isConicalLimit := {
        isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (conicalLimit.isConicalLimit V F).isLimit
        isConicalLimit := fun X ↦ by
          let iso := Functor.mapConePostcompose ((eHomFunctor V C).obj (op X)) (α := α.hom)
            (c := conicalLimit.cone V F)
          have :=
            (IsLimit.postcomposeHomEquiv (isoWhiskerRight α ((eHomFunctor V C).obj (op X))) _ ).symm
              ((conicalLimit.isConicalLimit V F).isConicalLimit X)
          exact this.ofIsoLimit (id iso.symm)
      }
    }

instance hasConicalLimitEquivalenceComp {F : J ⥤ C} (e : K ≌ J) [HasConicalLimit V F] :
    HasConicalLimit V (e.functor ⋙ F) :=
  HasConicalLimit.mk V
    { cone := Cone.whisker e.functor (conicalLimit.cone V F)
      isConicalLimit := {
        isLimit := IsLimit.whiskerEquivalence (conicalLimit.isConicalLimit V F).isLimit e
        isConicalLimit := fun X ↦
          IsLimit.whiskerEquivalence ((conicalLimit.isConicalLimit V F).isConicalLimit X) e
        }
    }

/-- If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/
theorem hasConicalLimitOfEquivalenceComp {F : J ⥤ C} (e : K ≌ J)
    [HasConicalLimit V (e.functor ⋙ F)] : HasConicalLimit V F := by
  haveI : HasConicalLimit V (e.inverse ⋙ e.functor ⋙ F) := hasConicalLimitEquivalenceComp V e.symm
  apply hasConicalLimitOfIso V (e.invFunIdAssoc F)

/-- We can transport conical limits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem hasConicalLimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasConicalLimitsOfShape J V C] : HasConicalLimitsOfShape J' V C := by
  constructor
  intro F
  apply hasConicalLimitOfEquivalenceComp V e

end Equivalence

/-- `C` has all conical limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has conical limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
@[pp_with_univ]
class HasConicalLimitsOfSize (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have conical limits -/
  has_conical_limits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasConicalLimitsOfShape J V C := by
    infer_instance

-- see Note [lower instance priority]
instance (priority := 100) hasConicalLimitsOfShapeOfHasLimits {J : Type u₁} [Category.{v₁} J]
    [EnrichedOrdinaryCategory V C] [HasConicalLimitsOfSize.{v₁, u₁} V C] : HasConicalLimitsOfShape J V C :=
  HasConicalLimitsOfSize.has_conical_limits_of_shape J

-- TODO: instance
def HasConicalLimitsOfSize_hasLimitsOfSize [h : HasConicalLimitsOfSize.{v₂, u₂} V C] :
    HasLimitsOfSize.{v₂, u₂} C where
  has_limits_of_shape := fun J ↦
    have := h.has_conical_limits_of_shape J
    HasConicalLimitsOfShape_hasLimitsOfShape J V C

/-- A category that has larger conical limits also has smaller conical limits. -/
theorem hasConicalLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [h : HasConicalLimitsOfSize.{v₁, u₁} V C] : HasConicalLimitsOfSize.{v₂, u₂} V C where
  has_conical_limits_of_shape J {_} :=
    have := h.has_conical_limits_of_shape (Shrink.{u₁, u₂} (ShrinkHoms.{u₂} J))
    hasConicalLimitsOfShape_of_equivalence V
      ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm

/-- `hasConicalLimitsOfSizeShrink.{v u} C` tries to obtain `HasLimitsOfSize.{v u} C`
from some other `HasLimitsOfSize C`.
-/
theorem hasConicalLimitsOfSizeShrink [HasConicalLimitsOfSize.{max v₁ v₂, max u₁ u₂} V C] :
    HasConicalLimitsOfSize.{v₁, u₁} V C := hasConicalLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} V C

/-- `C` has all (small) conical limits if it has limits of every shape that is as big as its
hom-sets.-/
abbrev HasConicalLimits (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]  : Prop :=
  HasConicalLimitsOfSize.{v, v} V C

instance (priority := 100) hasSmallestConicalLimitsOfHasConicalLimits [HasConicalLimits V C] :
    HasConicalLimitsOfSize.{0, 0} V C := hasConicalLimitsOfSizeShrink.{0, 0} V C

-- TODO: instance
def HasConicalLimits_hasLimits [HasConicalLimits V C] : HasLimits C :=
  HasConicalLimitsOfSize_hasLimitsOfSize V C

instance HasConicalLimits.has_conical_limits_of_shape {C : Type u} [Category.{v} C]
    [EnrichedOrdinaryCategory V C] [HasConicalLimits V C] (J : Type v)
    [Category.{v} J] : HasConicalLimitsOfShape J V C :=
  HasConicalLimitsOfSize.has_conical_limits_of_shape J

end ConicalLimits

section ConicalTerminal

variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

-- TODO: instance
def HasConicalTerminal_hasTerminal [hyp : HasConicalTerminal V C] : HasTerminal C := by
  apply HasConicalLimitsOfShape_hasLimitsOfShape at hyp
  infer_instance

end ConicalTerminal
section ConicalProducts

variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- An abbreviation for `HasConicalLimit (Discrete.functor f)`. -/
abbrev HasConicalProduct { I : Type w} (f : I → C) := HasConicalLimit V (Discrete.functor f)

-- TODO: instance
def HasConicalProduct_hasProduct {I : Type w} (f : I → C) [HasConicalProduct V f] :
    HasProduct f := HasConicalLimit_hasLimit V (Discrete.functor f)

variable (C) in
class HasConicalProducts : Prop where
  /-- All discrete diagrams of bounded size have conical products.  -/
  has_conical_limits_of_shape : ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) V C :=
    by infer_instance
--  has_limits_of_shape : ∀ { I : Type w} (f : I → C), HasConicalProduct f := by
--    infer_instance

-- TODO: instance
def HasConicalProducts_hasProducts [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasProducts.{w, v, u} C := by
  intro I
  constructor
  intro f
  have := hyp.has_conical_limits_of_shape I
  have : HasConicalLimit V f := by infer_instance
  exact HasConicalLimit_hasLimit V f

instance HasConicalProducts_hasConicalTerminal [hyp : HasConicalProducts.{0, v', v, u} V C] :
    HasConicalTerminal V C := hyp.has_conical_limits_of_shape PEmpty.{1}

instance HasConicalProducts_hasConicalTerminal' [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasConicalTerminal V C := by
  have inst := hyp.has_conical_limits_of_shape PEmpty
  exact hasConicalLimitsOfShape_of_equivalence V (J := Discrete PEmpty.{w+1}) emptyEquivalence

end ConicalProducts

section ConicalPullbacks

variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

abbrev HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) := HasConicalLimit V (cospan f g)

-- TODO: instance
def HasConicalPullback_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasConicalPullback V f g] : HasPullback f g := HasConicalLimit_hasLimit V (cospan f g)

variable (C) in
abbrev HasConicalPullbacks : Prop := HasConicalLimitsOfShape WalkingCospan V C

-- TODO: instance
def HasConicalPullbacks_hasPullbacks [hyp : HasConicalPullbacks V C] : HasPullbacks C := by
  apply HasConicalLimitsOfShape_hasLimitsOfShape at hyp
  infer_instance

end ConicalPullbacks

-- TODO: Add something for conical inverse limits of towers?

end CategoryTheory
