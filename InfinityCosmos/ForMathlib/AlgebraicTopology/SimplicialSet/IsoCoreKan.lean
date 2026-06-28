/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIsoLift
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.InnerFiller

open CategoryTheory Simplicial

universe u

namespace SSet

/-- The outer-horn filler input needed to turn `isoCore A` into a Kan complex. -/
def IsoCoreOuterHornFiller (A : SSet.{u}) : Prop :=
  ∀ {n : ℕ} {i : Fin (n + 2)}, i = 0 ∨ i = Fin.last (n + 1) →
    (τ : (Λ[n + 1, i] : SSet.{u}) ⟶ (isoCore A : SSet.{u})) →
      ∃ σ : Δ[n + 1] ⟶ (isoCore A : SSet.{u}), τ = Λ[n + 1, i].ι ≫ σ

private lemma horn_faces_of_filler {Z : SSet.{u}} {n : ℕ} {i : Fin (n + 2)}
    {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ Z}
    (hf : horn.IsCompatible f) {σ : Δ[n + 1] ⟶ Z}
    (hσ : hf.desc = Λ[n + 1, i].ι ≫ σ) :
    ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ σ = f j hj := by
  intro j hj
  calc
    stdSimplex.δ j ≫ σ = (horn.ι i j hj ≫ Λ[n + 1, i].ι) ≫ σ := by
      rw [horn.ι_ι]
    _ = horn.ι i j hj ≫ (Λ[n + 1, i].ι ≫ σ) := by
      rw [Category.assoc]
    _ = horn.ι i j hj ≫ hf.desc := by
      rw [← hσ]
    _ = f j hj := hf.ι_desc j hj

/-- Conditional assembly of the Kan-complex structure on `isoCore A` from inner fillers and
the two outer-horn fillers supplied by the Joyal cascade. -/
theorem kanComplex_isoCore {A : SSet.{u}} [Quasicategory A]
    (hOuter : IsoCoreOuterHornFiller A) : KanComplex (isoCore A : SSet.{u}) := by
  rw [KanComplex.iff]
  intro n i f hf
  by_cases hzero : i = 0
  · obtain ⟨σ, hσ⟩ := hOuter (Or.inl hzero) hf.desc
    exact ⟨σ, horn_faces_of_filler hf hσ⟩
  by_cases hlast : i = Fin.last (n + 1)
  · obtain ⟨σ, hσ⟩ := hOuter (Or.inr hlast) hf.desc
    exact ⟨σ, horn_faces_of_filler hf hσ⟩
  · have hpos : 0 < i := by
      rw [Fin.lt_def, Fin.val_zero]
      exact Nat.pos_of_ne_zero (fun h => hzero (Fin.ext h))
    have hlt : i < Fin.last (n + 1) := by
      rw [Fin.lt_def, Fin.val_last]
      exact lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) (fun h => hlast (Fin.ext h))
    obtain ⟨σ, hσ⟩ := isoCore_innerHornFiller (A := A) hpos hlt hf.desc
    exact ⟨σ, horn_faces_of_filler hf hσ⟩

namespace coherentIso

/-- Conditional coherent-iso lift: once the Joyal cascade supplies the outer horn fillers for
`isoCore A`, the committed Kan-core consumer gives the lift. -/
theorem lift_of_isoCore_outerHornFiller {A : SSet.{u}} [Quasicategory A]
    {a₀ a₁ : A _⦋0⦌} {e : Edge a₀ a₁}
    (he : e.IsIso) (hOuter : IsoCoreOuterHornFiller A) :
    ∃ F : coherentIso.{u} ⟶ A, (coherentIso.hom.map F).edge = e.edge :=
  lift_of_isoCore_kanComplex he (kanComplex_isoCore hOuter)

end coherentIso

end SSet
