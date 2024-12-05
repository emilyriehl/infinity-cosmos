/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

universe u v w

namespace SSet

open CategoryTheory Simplicial SimplicialCategory Limits

/-- An interval is a simplicial set equipped with two endpoints.-/
class Interval (I : SSet.{u}) : Type u where
  src : Δ[0] ⟶ I
  tgt : Δ[0] ⟶ I

/-- The interval relevant to the theory of Kan complexes.-/
instance arrowInterval : Interval Δ[1] where
  src := standardSimplex.map (SimplexCategory.δ (n := 0) (1))
  tgt := standardSimplex.map (SimplexCategory.δ (n := 0) (0))

/-- The interval relevant to the theory of quasi-categories. -/
instance isoInterval : Interval coherentIso where
  src :=   (yonedaEquiv coherentIso [0]).symm (WalkingIso.coev WalkingIso.zero)
  tgt :=   (yonedaEquiv coherentIso [0]).symm (WalkingIso.coev WalkingIso.one)


open MonoidalCategory
noncomputable def pointIsUnit : Δ[0] ≅ (𝟙_ SSet) :=
  IsTerminal.uniqueUpToIso isTerminalDeltaZero (IsTerminal.ofUnique (𝟙_ SSet))

noncomputable def expUnitNatIso : ihom (𝟙_ SSet) ≅ 𝟭 SSet :=
  (conjugateIsoEquiv (Adjunction.id (C := SSet)) (ihom.adjunction _)
    (leftUnitorNatIso _)).symm

noncomputable def expPointNatIso : ihom Δ[0] ≅ 𝟭 SSet := by
  refine ?_ ≪≫ expUnitNatIso
  exact {
    hom := MonoidalClosed.pre pointIsUnit.inv
    inv := MonoidalClosed.pre pointIsUnit.hom
    hom_inv_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.hom_inv_id]
      exact MonoidalClosed.pre_id _
    inv_hom_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.inv_hom_id]
      exact MonoidalClosed.pre_id _
  }

noncomputable def expPointIsoSelf (X : SSet) : sHom Δ[0] X ≅ X := expPointNatIso.app X
section

variable {I : SSet.{u}} [Interval I]

noncomputable def pathSpace {I : SSet.{u}} [Interval I] (X : SSet.{u}) : SSet.{u} := sHom I X

open MonoidalClosed

noncomputable def pathSpace.src (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.src).app X ≫ X.expPointIsoSelf.hom)

noncomputable def pathSpace.tgt (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.tgt).app X ≫ X.expPointIsoSelf.hom)


/-- TODO: Figure out how to allow `I` to be an a different universe from `A` and `B`?-/
structure Homotopy {A B : SSet.{u}} (f g : A ⟶ B) : Type u
    where
  homotopy : A ⟶ sHom I B
  source_eq : homotopy ≫ pathSpace.src B = f
  target_eq : homotopy ≫ pathSpace.tgt B = g

/-- For the correct interval, this defines a good notion of equivalences for both Kan complexes
and quasi-categories.-/
structure Equiv (A B : SSet.{u}) : Type u where
  toFun : A ⟶ B
  invFun : B ⟶ A
  left_inv : Homotopy (I := I) (toFun ≫ invFun) (𝟙 A)
  right_inv : Homotopy (I := I) (invFun ≫ toFun) (𝟙 B)

end

section

variable {A : SSet.{u}} (f g : A _[1])

structure HomotopyL where
  simplex : A _[2]
  δ₀ : A.δ 0 simplex = A.σ 0 (A.δ 0 f)
  δ₁ : A.δ 1 simplex = g
  δ₂ : A.δ 2 simplex = f

def HomotopicL : Prop := Nonempty (HomotopyL f g)

structure HomotopyR where
  simplex : A _[2]
  δ₀ : A.δ 0 simplex = f
  δ₁ : A.δ 1 simplex = g
  δ₂ : A.δ 2 simplex = A.σ 0 (A.δ 1 f)

def HomotopicR : Prop := Nonempty (HomotopyR f g)

def HomotopyL.refl : HomotopyL f f where
  simplex := A.σ 1 f
  δ₀ := by
    rw [← types_comp_apply (A.σ _) (A.δ _), ← types_comp_apply (A.δ _) (A.σ _)]
    rw [← Fin.succ_zero_eq_one, ← Fin.castSucc_zero]
    rw [SimplicialObject.δ_comp_σ_of_le A (by rfl)]
  δ₁ := by
    rw [← types_comp_apply (A.σ _) (A.δ _)]
    rw [SimplicialObject.δ_comp_σ_self' A (by rfl)]
    rfl
  δ₂ := by
    rw [← types_comp_apply (A.σ _) (A.δ _)]
    rw [← Fin.succ_one_eq_two]
    rw [SimplicialObject.δ_comp_σ_succ A]
    rfl

private lemma spine₂_arrow₀ (s : A _[2]) : (A.spine 2 s).arrow 0 = A.δ 2 s := by
  simp only [SimplicialObject.δ, spine_arrow]
  have : SimplexCategory.mkOfSucc 0 = SimplexCategory.δ 2 := by
    ext i
    fin_cases i <;> rfl
  rw [this]

private lemma spine₂_arrow₁ (s : A _[2]) : (A.spine 2 s).arrow 1 = A.δ 0 s := by
  simp only [SimplicialObject.δ, spine_arrow]
  have : SimplexCategory.mkOfSucc 1 = SimplexCategory.δ 0 := by
    ext i
    fin_cases i <;> rfl
  rw [this]

lemma StrictSegal.homotopic_iff_eq [StrictSegal A] : HomotopicL f g ↔ f = g := by
  have hrfl := HomotopyL.refl f
  apply Iff.intro <;> intro h
  · have h := Classical.choice h
    suffices A.spine 2 hrfl.simplex = A.spine 2 h.simplex by
      rw [← hrfl.δ₁, ← h.δ₁]
      rw [← spineToSimplex_spine hrfl.simplex, ← spineToSimplex_spine h.simplex]
      rw [this]
    ext i
    fin_cases i
    · simp only [spine₂_arrow₀, Fin.zero_eta]
      rw [h.δ₂]
      exact hrfl.δ₂
    · simp only [spine₂_arrow₁, Fin.mk_one]
      rw [h.δ₀]
      exact hrfl.δ₀
  · rw [← h]
    exact Nonempty.intro hrfl

end

end SSet
