/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import Architect
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe u v

open CategoryTheory

namespace SSet

open Simplicial Edge

-- @[blueprint
--   "defn:coherent-isomorphism"
--   (statement := /--
--   The \textbf{homotopy coherent isomorphism} $\iso$, is the nerve of the free-living isomorphism. Its n-simplices are sequences of arrows in WalkingIso.
--   -/)]
-- def coherentIso : SSet := nerve WalkingIso

namespace coherentIso

/-- Since the morphisms in WalkingIso do not carry information, an n-simplex of coherentIso is equivalent to an (n + 1)-vector of the objects of WalkingIso. -/
def equivFun {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → WalkingIso) where
  toFun f := f.obj
  invFun f := .mk f (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Since Fin 2 has decidable equality, the simplices of coherentIso have decidable equality as well. -/
instance (n : ℕ) : DecidableEq (coherentIso _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso.equivFun)

/-- The inclusion of the source vertex of `CoherentIso`. -/
def src : Δ[0] ⟶ coherentIso := yonedaEquiv.symm (coherentIso.x₀)

/-- The inclusion of the target vertex of `CoherentIso`. -/
def tgt : Δ[0] ⟶ coherentIso := yonedaEquiv.symm (coherentIso.x₁)

end coherentIso

end SSet
