import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Coproducts

open CategoryTheory Simplicial Opposite Limits
open scoped Simplicial

universe u

namespace SSet

noncomputable section

#print axioms SSet.augmentedDayUnitTo
#print axioms SSet.augmentedDayUnitTo_naturality
#print axioms SSet.joinInr
#print axioms SSet.joinInr_naturality_left

theorem not_preservesColimitsOfShape_joinFunctor_flip_deltaZero :
    ¬ PreservesColimitsOfShape (Discrete PEmpty.{1})
        (joinFunctor.flip.obj (Δ[0] : SSet.{u})) := by
  intro h
  haveI : PreservesColimit (Functor.empty.{0} SSet.{u})
      (joinFunctor.flip.obj (Δ[0] : SSet.{u})) := by
    exact PreservesColimitsOfShape.preservesColimit
  let bad : Δ[0] ⟶ (⊥_ SSet.{u}) :=
    joinInr (⊥_ SSet.{u}) (Δ[0] : SSet.{u}) ≫
      (PreservesInitial.iso (joinFunctor.flip.obj (Δ[0] : SSet.{u}))).hom
  let x := (bad.app (op ⦋0⦌)) (yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  have hInitial : IsInitial ((⊥_ SSet.{u}) _⦋0⦌) := by
    haveI : PreservesColimit (Functor.empty.{0} SSet.{u})
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) :=
      inferInstance
    exact initialIsInitial.isInitialObj
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) (⊥_ SSet.{u})
  haveI : IsEmpty ((⊥_ SSet.{u}) _⦋0⦌) :=
    (Types.initial_iff_empty ((⊥_ SSet.{u}) _⦋0⦌)).mp ⟨hInitial⟩
  exact IsEmpty.false x

#print axioms SSet.not_preservesColimitsOfShape_joinFunctor_flip_deltaZero

end

end SSet
