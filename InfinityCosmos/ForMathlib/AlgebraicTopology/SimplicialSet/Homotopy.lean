/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso

universe u v w

namespace SSet

open CategoryTheory Simplicial SimplicialCategory

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
def pointIsUnit : Δ[0] ≅ (𝟙_ SSet) := by sorry

noncomputable def expUnitNatIso : ihom (𝟙_ SSet) ≅ 𝟭 SSet :=
  (conjugateIsoEquiv (Adjunction.id (C := SSet)) (ihom.adjunction _)
    (leftUnitorNatIso _)).symm

def expPointNatIso : ihom Δ[0] ≅ 𝟭 SSet := by sorry
--   refine ?_ ≪≫ expUnitNatIso
--   have := pointIsUnit.symm.op
--   sorry

/-- Once we've proven that `Δ[0]` is terminal, this will follow from something just PRed to mathlib.-/
def expPointIsoSelf (X : SSet) : sHom Δ[0] X ≅ X := sorry

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

open SimplexCategory

variable {A : SSet.{u}} (f g : Δ[1] ⟶ A)

structure HomotopyL where
  homotopy : Δ[2] ⟶ A
  face0 : standardSimplex.map (δ 0) ≫ homotopy =
    standardSimplex.map (σ 0) ≫ standardSimplex.map (δ 0) ≫ f
  face1 : standardSimplex.map (δ 1) ≫ homotopy = g
  face2 : standardSimplex.map (δ 2) ≫ homotopy = f

structure HomotopyR where
  homotopy : Δ[2] ⟶ A
  face0 : standardSimplex.map (δ 0) ≫ homotopy = f
  face1 : standardSimplex.map (δ 1) ≫ homotopy = g
  face2 : standardSimplex.map (δ 2) ≫ homotopy =
    standardSimplex.map (σ 0) ≫ standardSimplex.map (δ 1) ≫ f

def HomotopicL : Prop :=
    Nonempty (HomotopyL f g)

def HomotopicR : Prop :=
    Nonempty (HomotopyR f g)

def HomotopyR.refl : HomotopyR f f where
  homotopy := standardSimplex.map (σ 0) ≫ f
  face0 := by
    rw [← Category.assoc, ← Functor.map_comp, δ_comp_σ_self' (by simp)]
    simp
  face1 := by
    rw [← Category.assoc, ← Functor.map_comp, δ_comp_σ_succ' (by simp)]
    simp
  face2 := by
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
        ← δ_comp_σ_of_gt (by simp)]
    rfl

lemma HomotopyR.equiv : --[Quasicategory A] :
    Equivalence (fun f g : Δ[1] ⟶ A ↦ HomotopicR f g) where
  refl f := ⟨HomotopyR.refl f⟩
  symm := sorry
  trans := sorry

lemma homotopicL_iff_homotopicR : --[Quasicategory A]
    HomotopicL f g ↔ HomotopicR f g := sorry

lemma HomotopyL.equiv : --[Quasicategory A]
    Equivalence (fun f g : Δ[1] ⟶ A ↦ HomotopicL f g) := by
  simp [homotopicL_iff_homotopicR]
  exact HomotopyR.equiv

end

end SSet
