/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Ordinary.Limits.IsConicalLimit

/-!
TODO: module docstring
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C) (c : Cone F)

/-- `ConicalLimitCone V F` contains a cone over `F` together with the information that it is a
conical limit. -/
structure ConicalLimitCone where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isConicalLimit : IsConicalLimit V cone

-- The class needs `V` as `outParam`.
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V] in
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C] (F : J ⥤ C) in

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

-- The class needs `V` as `outParam`.
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V] in
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] (F : J ⥤ C) in

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

-- The class needs `V` as `outParam`.
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V] in
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] (F : J ⥤ C) in

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

end CategoryTheory.Enriched
