/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import Architect
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.EdgeInvStruct
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

/-- Since WalkingIso has decidable equality, the simplices of coherentIso have decidable equality as well. -/
instance (n : ℕ) : DecidableEq (coherentIso _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso.equivFun)

/-- The `Fin 2` presentation of simplices in `coherentIso` used by the special-outer-horn stack. -/
def equivFin {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → Fin 2) where
  toFun f := fun i => finTwoEquiv.symm (WalkingIso.equivBool (equivFun f i))
  invFun f := equivFun.symm (fun i => WalkingIso.equivBool.symm (finTwoEquiv (f i)))
  left_inv f := by
    apply equivFun.injective
    funext i
    simp
  right_inv f := by
    funext i
    simp

/-- The forwards edge of `coherentIso` is an isomorphism edge. -/
def isIsoHom : Edge.IsIso coherentIso.hom :=
  coherentIso.invStructHom

/-- The image of `hom` under an SSet morphism is an isomorphism edge. -/
def isIsoMapHom
  {X : SSet}
  (g : coherentIso ⟶ X)
  : IsIso (coherentIso.hom.map g)
  := isIsoHom.map g

/-- If an edge is equal to the image of `hom` under an SSet morphism, this edge is an isomorphism. -/
def isIsoOfEqMapHom
  {X : SSet}
  {x₀ x₁ : X _⦋0⦌}
  {f : Edge x₀ x₁}
  {g : coherentIso ⟶ X}
  (hfg : f.edge = g.app _ hom.edge)
  : f.IsIso
  := (isIsoMapHom g).ofEq hfg.symm

/-- Forward-edge inclusion `Δ[1] ⟶ coherentIso` classifying `coherentIso.hom`. -/
noncomputable def homInclusion : Δ[1] ⟶ coherentIso := yonedaEquiv.symm coherentIso.hom.edge

/-- The simplex-level target equation is equivalent to a categorical extension square. -/
theorem edge_map_eq_iff_comp {A : SSet} {a₀ a₁ : A _⦋0⦌} (e : Edge a₀ a₁)
    (F : coherentIso ⟶ A) :
    (coherentIso.hom.map F).edge = e.edge ↔
      homInclusion ≫ F = yonedaEquiv.symm e.edge := by
  rw [homInclusion, yonedaEquiv_symm_comp, Edge.map_edge,
    yonedaEquiv.symm.injective.eq_iff]

/-- Lifting an edge to a map out of `coherentIso` is equivalent to extending it along the
forward-edge inclusion. -/
theorem lift_iff_extension {A : SSet} {a₀ a₁ : A _⦋0⦌} (e : Edge a₀ a₁) :
    (∃ F : coherentIso ⟶ A, (coherentIso.hom.map F).edge = e.edge) ↔
      (∃ F : coherentIso ⟶ A, homInclusion ≫ F = yonedaEquiv.symm e.edge) :=
  exists_congr (fun F => edge_map_eq_iff_comp e F)

/-- Easy direction: a lift of an edge through `coherentIso` certifies that the edge is an
isomorphism. -/
def isIso_of_lift {A : SSet} {a₀ a₁ : A _⦋0⦌} {e : Edge a₀ a₁}
    (F : coherentIso ⟶ A) (hF : (coherentIso.hom.map F).edge = e.edge) : e.IsIso :=
  coherentIso.isIsoOfEqMapHom hF.symm

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
    coherentIso.equivFin x = fun _ => 0 := by
  rcases hx with ⟨y, rfl⟩
  ext i
  cases n using Opposite.rec
  rfl

/-- A simplex in the target endpoint subcomplex is constantly the target vertex. -/
lemma mem_range_tgt_const {n : SimplexCategoryᵒᵖ} {x : coherentIso.obj n}
    (hx : x ∈ (Subcomplex.range coherentIso.tgt).obj n) :
    coherentIso.equivFin x = fun _ => 1 := by
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
  have h01 : (0 : Fin 2) = 1 := by
    simpa using congrFun (h0.symm.trans h1) 0
  exact Fin.zero_ne_one h01

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
