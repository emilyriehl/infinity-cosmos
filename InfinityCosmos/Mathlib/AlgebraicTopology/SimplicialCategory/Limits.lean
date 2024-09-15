import InfinityCosmos.Mathlib.AlgebraicTopology.SimplicialCategory.Basic

namespace CategoryTheory

open Limits SimplicialCategory Opposite

variable {I A : Type*} [Category I] [Category A] [SimplicialCategory A] {K : I ⥤ A} (c : Cone K)

/--
A limit cone `c` in a simplicial category `A` is a *simplicially enriched limit* if for every
`X : A`, the cone obtained by applying the simplicial coyoneda functor `(X ⟶[A] -)` to `c` is a
limit cone in `SSet`.
-/
structure IsSLimit where
  isLimit : IsLimit c
  isSLimit (X : A) : IsLimit <| ((sHomFunctor A).obj (op X)).mapCone c

namespace SimplicialCategory

/-!
# Characterization in terms of the comparison map.

There is a canonical comparison map with the limit in `SSet`, the following proves that a limit
cone in `A` is a simplicially enriched limit if and only if the comparison map is an isomorphism
for every `X : A`.
-/

noncomputable def limitComparison (X : A) :
    sHom X c.pt ⟶ limit (K ⋙ (sHomFunctor A).obj (op X)) :=
  limit.lift _ (((sHomFunctor A).obj (op X)).mapCone c)

lemma limitComparison_eq_conePointUniqueUpToIso (X : A) (h : IsSLimit c) :
    limitComparison c X = ((h.isSLimit X).conePointUniqueUpToIso (limit.isLimit _)).hom := by
  apply limit.hom_ext
  simp [limitComparison]

lemma isIso_limitComparison (X : A) (h : IsSLimit c) : IsIso (limitComparison c X) := by
  rw [limitComparison_eq_conePointUniqueUpToIso (h := h)]
  infer_instance

noncomputable def limitComparisonIso (X : A) (h : IsSLimit c) :
    sHom X c.pt ≅ (limit (K ⋙ (sHomFunctor A).obj (op X))) := by
  have := isIso_limitComparison c X h
  exact (asIso (SimplicialCategory.limitComparison c X))

noncomputable def isSLimitOfIsIsoLimitComparison [∀ X, IsIso (limitComparison c X)]
    (hc : IsLimit c) : IsSLimit c where
  isLimit := hc
  isSLimit X := by
    suffices PreservesLimit K ((sHomFunctor A).obj (op X)) from this.preserves hc
    have : HasLimit K := ⟨c, hc⟩
    apply (config := { allowSynthFailures := true } ) preservesLimitOfIsIsoPost
    have : limit.post K ((sHomFunctor A).obj (op X)) =
      (((sHomFunctor A).obj (op X)).map ((limit.isLimit K).conePointUniqueUpToIso hc).hom) ≫
        limitComparison c X := by
      apply limit.hom_ext
      intro j
      simp only [sHomFunctor_obj_obj, Functor.comp_obj, limit.post_π, sHomFunctor_obj_map,
        limit.cone_x, limitComparison, Category.assoc, limit.lift_π, Functor.mapCone_pt,
        Functor.mapCone_π_app, ← sHomWhiskerLeft_comp, IsLimit.conePointUniqueUpToIso_hom_comp,
        limit.cone_x, limit.cone_π]
    rw [this]
    infer_instance


end CategoryTheory.SimplicialCategory
