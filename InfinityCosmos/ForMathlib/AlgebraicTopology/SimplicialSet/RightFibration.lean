import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Right fibrations of simplicial sets

This file mirrors the `LeftFibration` API for right horns.
-/

universe u

open CategoryTheory HomotopicalAlgebra Simplicial MorphismProperty Limits
open scoped SSet.modelCategoryQuillen

namespace SSet

/-- The family of right horn inclusions `Λ[n+1, i].ι : Λ[n+1, i] ⟶ Δ[n+1]`
for `0 < i`. -/
inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) :
    rightHornInclusions Λ[n + 1, i].ι

lemma horn_ι_mem_rightHornInclusions {n : ℕ} [NeZero n] {i : Fin (n + 1)}
    (h0 : 0 < i) : rightHornInclusions (horn.{u} n i).ι := by
  obtain _ | k := n
  · exact (NeZero.ne 0 rfl).elim
  · exact ⟨i, h0⟩

lemma innerHornInclusions_le_rightHornInclusions :
    innerHornInclusions.{u} ≤ rightHornInclusions := by
  rintro _ _ _ ⟨i, h0, _⟩
  exact ⟨i, h0⟩

lemma rightHornInclusions_le_J :
    rightHornInclusions.{u} ≤ modelCategoryQuillen.J := by
  rintro _ _ _ ⟨i, _⟩
  exact modelCategoryQuillen.horn_ι_mem_J _ i

lemma rightHornInclusions_le_monomorphisms :
    rightHornInclusions.{u} ≤ monomorphisms SSet :=
  rightHornInclusions_le_J.trans modelCategoryQuillen.J_le_monomorphisms

/-- Right fibrations are morphisms with the right lifting property against all
right horn inclusions. -/
def rightFibrations : MorphismProperty SSet.{u} := rightHornInclusions.rlp
  deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
    IsStableUnderRetracts

/-- A morphism `q` satisfies `[RightFibration q]` if it belongs to
`rightFibrations`. -/
@[mk_iff]
class RightFibration {X Y : SSet} (q : X ⟶ Y) : Prop where
  mem : rightFibrations q

lemma mem_rightFibrations {X Y : SSet} (q : X ⟶ Y) [RightFibration q] :
    rightFibrations q := RightFibration.mem

/-- Right-anodyne extensions are the morphisms with the left lifting property
against right fibrations. -/
def rightAnodyneExtensions : MorphismProperty SSet.{u} := rightFibrations.llp
  deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
    IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
    IsStableUnderCoproducts

lemma rightAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    rightAnodyneExtensions f :=
  MorphismProperty.of_isIso rightAnodyneExtensions f

lemma rightAnodyneExtensions_eq_llp_rlp :
    rightAnodyneExtensions.{u} = rightHornInclusions.rlp.llp := rfl

lemma rightAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 2)}
    (h0 : 0 < i) :
    rightAnodyneExtensions.{u} Λ[n + 1, i].ι := by
  rw [rightAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ ⟨i, h0⟩

/-- Right fibrations are inner fibrations. -/
lemma rightFibrations_le_innerFibrations :
    rightFibrations.{u} ≤ innerFibrations :=
  antitone_rlp innerHornInclusions_le_rightHornInclusions

instance {X Y : SSet} (q : X ⟶ Y) [RightFibration q] : InnerFibration q :=
  ⟨rightFibrations_le_innerFibrations _ (mem_rightFibrations q)⟩

/-- Inner-anodyne extensions are right-anodyne. -/
lemma innerAnodyneExtensions_le_rightAnodyneExtensions :
    innerAnodyneExtensions.{u} ≤ rightAnodyneExtensions :=
  antitone_llp rightFibrations_le_innerFibrations

/-- Kan fibrations are right fibrations. -/
lemma fibrations_le_rightFibrations :
    fibrations SSet.{u} ≤ rightFibrations := by
  rw [modelCategoryQuillen.fibrations_eq]
  exact antitone_rlp rightHornInclusions_le_J

/-- Right-anodyne extensions are anodyne extensions. -/
lemma rightAnodyneExtensions_le :
    rightAnodyneExtensions.{u} ≤ anodyneExtensions := by
  rw [anodyneExtensions_eq_llp_rlp, rightAnodyneExtensions_eq_llp_rlp,
    le_llp_iff_le_rlp, rlp_llp_rlp]
  exact antitone_rlp rightHornInclusions_le_J

end SSet
