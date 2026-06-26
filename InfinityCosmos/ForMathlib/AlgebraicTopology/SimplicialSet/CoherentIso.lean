/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import Architect
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe u v

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects called
`zero` and `one`. Perhaps these should have different names?-/
def WalkingIso : Type u := ULift (Fin 2)

@[match_pattern]
def WalkingIso.zero : WalkingIso := ULift.up (0 : Fin 2)

@[match_pattern]
def WalkingIso.one : WalkingIso := ULift.up (1 : Fin 2)

open WalkingIso

namespace WalkingIso

/-- The free isomorphism is the codiscrete category on two objects. Can we make this a special
case of the other definition?-/
instance : Category (WalkingIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u} [Category.{v} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category.-/
def toIso  (F : WalkingIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map PUnit.unit
  inv := F.map PUnit.unit
  hom_inv_id := by rw [← F.map_comp, ← F.map_id]; rfl
  inv_hom_id := by rw [← F.map_comp, ← F.map_id]; rfl

/-- From an isomorphism in a category, one can build a functor out of `WalkingIso` to
that category.-/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso ⥤ C where
  obj := fun
    | zero => X
    | one => Y
  map := @fun
    | zero, zero, _ => 𝟙 _
    | zero, one,  _ => e.hom
    | one, zero, _ => e.inv
    | one, one,  _ => 𝟙 _
  map_comp := by simp [WalkingIso, Quiver.Hom]

/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
def equiv : (WalkingIso ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · simp [WalkingIso]
      constructor <;> rfl
    · simp [WalkingIso]
      simp only [fromIso, toIso]
      constructor <;> constructor <;>
      ( intro ⟨⟩
        try rfl
        try (rw [← F.map_id]; rfl) )

end

def coev (i : WalkingIso) : Fin 1 ⥤ WalkingIso := ComposableArrows.mk₀ i

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial Edge
open CategoryTheory

@[blueprint
  "defn:coherent-isomorphism"
  (statement := /--
  The \textbf{homotopy coherent isomorphism} $\iso$, is the nerve of the free-living isomorphism. Its n-simplices are sequences of arrows in WalkingIso.
  -/)]
def coherentIso : SSet := nerve WalkingIso

namespace coherentIso

/-- Since the morphisms in WalkingIso do not carry information, an n-simplex of coherentIso is equivalent to an (n + 1)-vector of the objects of WalkingIso. -/
def equivFun {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → Fin 2) where
  toFun f := ULift.down ∘ f.obj
  invFun f := .mk (ULift.up ∘ f) (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Since Fin 2 has decidable equality, the simplices of coherentIso have decidable equality as well. -/
instance (n : ℕ) : DecidableEq (coherentIso _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso.equivFun)

/-- The source vertex of `coherentIso`. -/
def x₀ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero

/-- The target edge of `coherentIso`. -/
def x₁ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one

/-- The forwards edge of `coherentIso`. -/
def hom : Edge x₀ x₁ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The backwards edge of `coherentIso`. -/
def inv : Edge x₁ x₀ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The forwards and backwards edge of `coherentIso` compose to the identity. -/
def homInvId : Edge.CompStruct hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The backwards and forwards edge of `coherentIso` compose to the identity. -/
def invHomId : Edge.CompStruct inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` is an isomorphism. -/
def isIsoHom : Edge.IsIso coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/-- The image of `hom` under an SSet morphism is an isomorphism. -/
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

/- This is the single local proof hole isolated by the phase-3 scout: it is the special
outer-horn extension theorem for isomorphism edges in a quasi-category. -/
theorem lift {A : SSet} [Quasicategory A] {a₀ a₁ : A _⦋0⦌}
    {e : Edge a₀ a₁} (he : e.IsIso) :
    ∃ F : coherentIso ⟶ A, (coherentIso.hom.map F).edge = e.edge := by
  rw [coherentIso.lift_iff_extension]
  sorry

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
    coherentIso.equivFun x = fun _ => 0 := by
  rcases hx with ⟨y, rfl⟩
  ext i
  cases n using Opposite.rec
  rfl

/-- A simplex in the target endpoint subcomplex is constantly the target vertex. -/
lemma mem_range_tgt_const {n : SimplexCategoryᵒᵖ} {x : coherentIso.obj n}
    (hx : x ∈ (Subcomplex.range coherentIso.tgt).obj n) :
    coherentIso.equivFun x = fun _ => 1 := by
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
