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

attribute [blueprint
  "defn:coherent-isomorphism"
  (statement := /--
  The \textbf{homotopy coherent isomorphism} $\iso$, is the nerve of the free-living isomorphism. Its n-simplices are sequences of arrows in WalkingIso.
  -/)]
  coherentIso

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

/-- The two endpoint subcomplexes of the coherent isomorphism. -/
noncomputable def boundary : coherentIso.Subcomplex :=
  Subcomplex.range coherentIso.src ⊔ Subcomplex.range coherentIso.tgt

/-- A simplex in the source endpoint subcomplex is constantly the source vertex. -/
lemma mem_range_src_const {n : SimplexCategoryᵒᵖ} {x : coherentIso.obj n}
    (hx : x ∈ (Subcomplex.range coherentIso.src).obj n) :
    coherentIso.equivFun x = fun _ => WalkingIso.zero := by
  rcases hx with ⟨y, rfl⟩
  ext i
  cases n using Opposite.rec
  rfl

/-- A simplex in the target endpoint subcomplex is constantly the target vertex. -/
lemma mem_range_tgt_const {n : SimplexCategoryᵒᵖ} {x : coherentIso.obj n}
    (hx : x ∈ (Subcomplex.range coherentIso.tgt).obj n) :
    coherentIso.equivFun x = fun _ => WalkingIso.one := by
  rcases hx with ⟨y, rfl⟩
  ext i
  cases n using Opposite.rec
  rfl

/-- The source and target endpoint subcomplexes of `coherentIso` are disjoint. -/
lemma not_mem_range_src_of_mem_range_tgt {n : SimplexCategoryᵒᵖ}
    {x : coherentIso.obj n} (hx : x ∈ (Subcomplex.range coherentIso.tgt).obj n) :
    x ∉ (Subcomplex.range coherentIso.src).obj n := by
  intro hsrc
  have h0 := coherentIso.mem_range_src_const hsrc
  have h1 := coherentIso.mem_range_tgt_const hx
  have h01 : WalkingIso.zero = WalkingIso.one := by
    simpa using congrFun (h0.symm.trans h1) 0
  exact Bool.false_ne_true (congrArg (fun w => w.as.down) h01)

/-- Membership in the boundary of `coherentIso` is membership in one of the two endpoint ranges. -/
lemma mem_boundary_iff {n : SimplexCategoryᵒᵖ} {x : coherentIso.obj n} :
    x ∈ coherentIso.boundary.obj n ↔
      x ∈ (Subcomplex.range coherentIso.src).obj n ∨
      x ∈ (Subcomplex.range coherentIso.tgt).obj n := by
  rfl

/-- On the boundary of `coherentIso`, being in the source endpoint is preserved and reflected by
simplicial operators. -/
lemma map_mem_range_src_iff_of_boundary {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    {x : coherentIso.obj n} (hx : x ∈ coherentIso.boundary.obj n) :
    coherentIso.map α x ∈ (Subcomplex.range coherentIso.src).obj m ↔
      x ∈ (Subcomplex.range coherentIso.src).obj n := by
  constructor
  · intro hmap
    rcases (coherentIso.mem_boundary_iff.mp hx) with hsrc | htgt
    · exact hsrc
    · exfalso
      have htgt_map : coherentIso.map α x ∈ (Subcomplex.range coherentIso.tgt).obj m :=
        (Subcomplex.range coherentIso.tgt).map α htgt
      exact coherentIso.not_mem_range_src_of_mem_range_tgt htgt_map hmap
  · intro hsrc
    exact (Subcomplex.range coherentIso.src).map α hsrc

end coherentIso

end SSet
