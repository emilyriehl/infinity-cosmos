import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe v₁ u₁ v₂ u₂ w v u

namespace CategoryTheory

open Limits SimplicialCategory Opposite


section

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

variable {F : J ⥤ C} (c : Cone F)

/--
A limit cone `c` in a simplicial category `A` is a *simplicially enriched limit* if for every
`X : C`, the cone obtained by applying the simplicial coyoneda functor `(X ⟶[A] -)` to `c` is a
limit cone in `SSet`.
-/
structure IsSLimit where
  isLimit : IsLimit c
  isSLimit (X : C) : IsLimit <| ((sHomFunctor C).obj (op X)).mapCone c

/-- Conical simplicial limits are also limits in the unenriched sense.-/
def IsSLimit_islimit (slim : IsSLimit c) : IsLimit c := slim.isLimit

namespace SimplicialCategory

/-!
# Characterization in terms of the comparison map.

There is a canonical comparison map with the limit in `SSet`, the following proves that a limit
cone in `A` is a simplicially enriched limit if and only if the comparison map is an isomorphism
for every `X : A`.
-/

-- Adjusting the size of `J` would also work, but this is more universe polymorphic.
variable [HasLimitsOfShape J SSet]

noncomputable def limitComparison (X : C)  :
    sHom X c.pt ⟶ limit (F ⋙ (sHomFunctor C).obj (op X)) :=
  limit.lift _ (((sHomFunctor C).obj (op X)).mapCone c)

lemma limitComparison_eq_conePointUniqueUpToIso (X : C) (h : IsSLimit c)
    [HasLimit (F ⋙ (sHomFunctor C).obj (op X))] :
    limitComparison c X = ((h.isSLimit X).conePointUniqueUpToIso (limit.isLimit _)).hom := by
  apply limit.hom_ext
  simp [limitComparison]

lemma isIso_limitComparison (X : C) (h : IsSLimit c) : IsIso (limitComparison c X) := by
  rw [limitComparison_eq_conePointUniqueUpToIso (h := h)]
  infer_instance

noncomputable def limitComparisonIso (X : C) (h : IsSLimit c) :
    sHom X c.pt ≅ (limit (F ⋙ (sHomFunctor C).obj (op X))) := by
  have := isIso_limitComparison c X h
  exact (asIso (SimplicialCategory.limitComparison c X))

noncomputable def isSLimitOfIsIsoLimitComparison [∀ X, IsIso (limitComparison c X)]
    (hc : IsLimit c) : IsSLimit c where
  isLimit := hc
  isSLimit X := by
    suffices PreservesLimit F ((sHomFunctor C).obj (op X)) from this.preserves hc
    have : HasLimit F := ⟨c, hc⟩
    apply (config := { allowSynthFailures := true } ) preservesLimitOfIsIsoPost
    have : limit.post F ((sHomFunctor C).obj (op X)) =
      (((sHomFunctor C).obj (op X)).map ((limit.isLimit F).conePointUniqueUpToIso hc).hom) ≫
        limitComparison c X := by
      apply limit.hom_ext
      intro j
      simp only [eHomFunctor_obj_obj, Functor.comp_obj, limit.post_π, eHomFunctor_obj_map,
        limit.cone_x, Category.assoc, limitComparison, Category.assoc, limit.lift_π,
        Functor.mapCone_pt, Functor.mapCone_π_app,
        ← sHomWhiskerLeft_comp, IsLimit.conePointUniqueUpToIso_hom_comp,
        limit.cone_x, limit.cone_π]
    rw [this]
    infer_instance


end SimplicialCategory

end

section ConicalLimits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- `ConicalLimitCone F` contains a cone over `F` together with the information that it is a conical
limit. -/
structure ConicalLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isSLimit : IsSLimit cone

/-- A conical limit cone is a limit cone. -/
def ConicalLimitCone_isLimitCone {F : J ⥤ C} (cone : Cone F) (slim : IsSLimit cone) :
    IsLimit cone := slim.isLimit

/-- `HasConicalLimit F` represents the mere existence of a limit for `F`. -/
class HasConicalLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_limit : Nonempty (ConicalLimitCone F)

theorem HasConicalLimit.mk {F : J ⥤ C} (d : ConicalLimitCone F) : HasConicalLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `ConicalLimitCone F` from `HasConicalLimit F`. -/
noncomputable def getConicalLimitCone (F : J ⥤ C) [HasConicalLimit F] : ConicalLimitCone F :=
  Classical.choice <| HasConicalLimit.exists_limit

instance HasConicalLimit_hasLimit (F : J ⥤ C) [HasConicalLimit F] : HasLimit F := HasLimit.mk
  { cone := (getConicalLimitCone F).cone,
    isLimit := ConicalLimitCone_isLimitCone _ (getConicalLimitCone F).isSLimit }

variable (J C)

/-- `C` has conical limits of shape `J` if there exists a conical limit for every functor
`F : J ⥤ C`. -/
class HasConicalLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits -/
  has_conical_limit : ∀ F : J ⥤ C, HasConicalLimit F := by infer_instance

-- see Note [lower instance priority]
instance (priority := 100) hasConicalLimitOfHasConicalLimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [SimplicialCategory C] [HasConicalLimitsOfShape J C] (F : J ⥤ C) : HasConicalLimit F :=
  HasConicalLimitsOfShape.has_conical_limit F

instance HasConicalLimitsOfShape_hasLimitsOfShape [HasConicalLimitsOfShape J C] :
    HasLimitsOfShape J C where
  has_limit _ := inferInstance

/-- `C` has all conical limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has conical limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
@[pp_with_univ]
class HasConicalLimitsOfSize (C : Type u) [Category.{v} C] [SimplicialCategory C] : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have conical limits -/
  has_conical_limits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasConicalLimitsOfShape J C := by
    infer_instance

-- see Note [lower instance priority]
instance (priority := 100) hasConicalLimitsOfShapeOfHasLimits {J : Type u₁} [Category.{v₁} J]
    [SimplicialCategory C] [HasConicalLimitsOfSize.{v₁, u₁} C] : HasConicalLimitsOfShape J C :=
  HasConicalLimitsOfSize.has_conical_limits_of_shape J

instance HasConicalLimitsOfSize_hasLimitsOfSize [HasConicalLimitsOfSize.{v₂, u₂, v, u} C] :
    HasLimitsOfSize.{v₂, u₂, v, u} C where
  has_limits_of_shape := inferInstance

/-- `C` has all (small) conical limits if it has limits of every shape that is as big as its
hom-sets.-/
abbrev HasConicalLimits (C : Type u) [Category.{v} C] [SimplicialCategory C]  : Prop :=
  HasConicalLimitsOfSize.{v, v} C

instance HasConicalLimits_hasLimits [HasConicalLimits C] : HasLimits C :=
  HasConicalLimitsOfSize_hasLimitsOfSize C

instance HasConicalLimits.has_conical_limits_of_shape {C : Type u} [Category.{v} C]
    [SimplicialCategory C] [HasConicalLimits C] (J : Type v)
    [Category.{v} J] : HasConicalLimitsOfShape J C :=
  HasConicalLimitsOfSize.has_conical_limits_of_shape J

variable {J C}

end ConicalLimits

section ConicalProducts
variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- An abbreviation for `HasSLimit (Discrete.functor f)`. -/
abbrev HasConicalProduct { I : Type w} (f : I → C) := HasConicalLimit (Discrete.functor f)

instance HasConicalProduct_hasProduct {I : Type w} (f : I → C) [HasConicalProduct f] :
    HasProduct f := HasConicalLimit_hasLimit (Discrete.functor f)

variable (C) in
class HasConicalProducts : Prop where
  /-- All discrete diagrams of bounded size have conical products.  -/
  has_conical_limits_of_shape : ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) C :=
    by infer_instance
--  has_limits_of_shape : ∀ { I : Type w} (f : I → C), HasConicalProduct f := by
--    infer_instance

instance HasConicalProducts_hasProducts [hyp : HasConicalProducts.{w, v, u} C] :
     HasProducts.{w, v, u} C := by
  intro I
  constructor
  intro f
  have := hyp.has_conical_limits_of_shape I
  have : HasConicalLimit f := by infer_instance
  exact HasConicalLimit_hasLimit f

end ConicalProducts

end CategoryTheory
