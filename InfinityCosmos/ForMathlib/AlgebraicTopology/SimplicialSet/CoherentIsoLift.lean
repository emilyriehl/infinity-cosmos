/-
Copyright (c) 2026 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIsoAnodyne
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCore

open CategoryTheory Simplicial HomotopicalAlgebra MorphismProperty Limits
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet
namespace coherentIso

/-- Final assembly for the coherent-iso lift: if the iso-core of `A` is Kan, then every
invertible edge of `A` extends to a map out of `coherentIso`. -/
theorem lift_of_isoCore_kanComplex {A : SSet.{u}} {a₀ a₁ : A _⦋0⦌} {e : Edge a₀ a₁}
    (he : e.IsIso) (hcore : KanComplex (isoCore A : SSet.{u})) :
    ∃ F : coherentIso.{u} ⟶ A, (coherentIso.hom.map F).edge = e.edge := by
  rw [coherentIso.lift_iff_extension]
  set ehat := Subfunctor.lift (yonedaEquiv.symm e.edge) (range_edge_le_isoCore he) with hehat
  have hfib : fibrations SSet.{u} (terminal.from (isoCore A : SSet.{u})) := by
    have hF : Fibration (terminal.from (isoCore A : SSet.{u})) := hcore
    rwa [fibration_iff] at hF
  haveI hlp : HasLiftingProperty (homInclusion.{u}) (terminal.from (isoCore A : SSet.{u})) :=
    homInclusion_anodyneExtensions (terminal.from (isoCore A : SSet.{u})) hfib
  have sq : CommSq ehat (homInclusion.{u}) (terminal.from (isoCore A : SSet.{u}))
      (terminal.from coherentIso.{u}) := ⟨Subsingleton.elim _ _⟩
  refine ⟨sq.lift ≫ (isoCore A).ι, ?_⟩
  rw [← Category.assoc, sq.fac_left, hehat, Subfunctor.lift_ι]

end coherentIso
end SSet
