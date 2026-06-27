import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Left fibrations of simplicial sets

This file mirrors the existing `innerFibrations` / `innerAnodyneExtensions`
API for the left horns.  The only deferred theorem is the right-most horn lift
over a terminal base, the Kerodon 019D input closed later by the join/slice
argument.
-/

universe u

open CategoryTheory HomotopicalAlgebra Simplicial MorphismProperty Limits
open scoped SSet.modelCategoryQuillen

namespace SSet

/-- The family of left horn inclusions `Λ[n+1, i].ι : Λ[n+1, i] ⟶ Δ[n+1]`
for `i < Fin.last (n+1)`. -/
inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
    leftHornInclusions Λ[n + 1, i].ι

lemma horn_ι_mem_leftHornInclusions {n : ℕ} [NeZero n] {i : Fin (n + 1)}
    (hn : i < Fin.last n) : leftHornInclusions (horn.{u} n i).ι := by
  obtain _ | k := n
  · exact (NeZero.ne 0 rfl).elim
  · exact ⟨i, hn⟩

lemma innerHornInclusions_le_leftHornInclusions :
    innerHornInclusions.{u} ≤ leftHornInclusions := by
  rintro _ _ _ ⟨i, _, hn⟩
  exact ⟨i, hn⟩

lemma leftHornInclusions_le_J :
    leftHornInclusions.{u} ≤ modelCategoryQuillen.J := by
  rintro _ _ _ ⟨i, _⟩
  exact modelCategoryQuillen.horn_ι_mem_J _ i

lemma leftHornInclusions_le_monomorphisms :
    leftHornInclusions.{u} ≤ monomorphisms SSet :=
  leftHornInclusions_le_J.trans modelCategoryQuillen.J_le_monomorphisms

/-- Left fibrations are morphisms with the right lifting property against all
left horn inclusions. -/
def leftFibrations : MorphismProperty SSet.{u} := leftHornInclusions.rlp
  deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
    IsStableUnderRetracts

/-- A morphism `q` satisfies `[LeftFibration q]` if it belongs to
`leftFibrations`. -/
@[mk_iff]
class LeftFibration {X Y : SSet} (q : X ⟶ Y) : Prop where
  mem : leftFibrations q

lemma mem_leftFibrations {X Y : SSet} (q : X ⟶ Y) [LeftFibration q] :
    leftFibrations q := LeftFibration.mem

/-- Left-anodyne extensions are the morphisms with the left lifting property
against left fibrations. -/
def leftAnodyneExtensions : MorphismProperty SSet.{u} := leftFibrations.llp
  deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
    IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
    IsStableUnderCoproducts

lemma leftAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    leftAnodyneExtensions f :=
  MorphismProperty.of_isIso leftAnodyneExtensions f

lemma leftAnodyneExtensions_eq_llp_rlp :
    leftAnodyneExtensions.{u} = leftHornInclusions.rlp.llp := rfl

lemma leftAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 2)}
    (hn : i < Fin.last (n + 1)) :
    leftAnodyneExtensions.{u} Λ[n + 1, i].ι := by
  rw [leftAnodyneExtensions_eq_llp_rlp]
  exact le_llp_rlp _ _ ⟨i, hn⟩

/-- Left fibrations are inner fibrations. -/
lemma leftFibrations_le_innerFibrations :
    leftFibrations.{u} ≤ innerFibrations :=
  antitone_rlp innerHornInclusions_le_leftHornInclusions

instance {X Y : SSet} (q : X ⟶ Y) [LeftFibration q] : InnerFibration q :=
  ⟨leftFibrations_le_innerFibrations _ (mem_leftFibrations q)⟩

/-- Inner-anodyne extensions are left-anodyne. -/
lemma innerAnodyneExtensions_le_leftAnodyneExtensions :
    innerAnodyneExtensions.{u} ≤ leftAnodyneExtensions :=
  antitone_llp leftFibrations_le_innerFibrations

/-- Kan fibrations are left fibrations. -/
lemma fibrations_le_leftFibrations :
    fibrations SSet.{u} ≤ leftFibrations := by
  rw [modelCategoryQuillen.fibrations_eq]
  exact antitone_rlp leftHornInclusions_le_J

/-- Left-anodyne extensions are anodyne extensions. -/
lemma leftAnodyneExtensions_le :
    leftAnodyneExtensions.{u} ≤ anodyneExtensions := by
  rw [anodyneExtensions_eq_llp_rlp, leftAnodyneExtensions_eq_llp_rlp,
    le_llp_iff_le_rlp, rlp_llp_rlp]
  exact antitone_rlp leftHornInclusions_le_J

/-- Kerodon 019D input, deferred to the join/slice Joyal chunk: a left fibration
over a terminal object lifts against the single right-most horn. -/
theorem leftFibration_rlp_rightHorn_of_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] {n : ℕ} :
    HasLiftingProperty (Λ[n + 1, Fin.last (n + 1)].ι) p := by
  sorry

/-- A left fibration whose target is terminal has a Kan-complex source. -/
theorem kanComplex_of_leftFibration_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] : KanComplex X := by
  show IsFibrant X
  rw [isFibrant_iff_of_isTerminal p hY, modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [modelCategoryQuillen.J, iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  rcases lt_or_eq_of_le (Fin.le_last i) with hlt | heq
  · exact mem_leftFibrations p _ ⟨i, hlt⟩
  · subst heq
    exact leftFibration_rlp_rightHorn_of_isTerminal p hY

/-- The fiber of a left fibration over a vertex is a Kan complex. -/
theorem kanComplex_fiber_of_leftFibration {X S : SSet.{u}} (p : X ⟶ S)
    [LeftFibration p] (s : Δ[0] ⟶ S) :
    KanComplex (Limits.pullback p s) := by
  have hsnd : leftFibrations (Limits.pullback.snd p s) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p s)
      (mem_leftFibrations p)
  have : LeftFibration (Limits.pullback.snd p s) := ⟨hsnd⟩
  exact kanComplex_of_leftFibration_isTerminal (Limits.pullback.snd p s)
    stdSimplex.isTerminalObj₀

end SSet
