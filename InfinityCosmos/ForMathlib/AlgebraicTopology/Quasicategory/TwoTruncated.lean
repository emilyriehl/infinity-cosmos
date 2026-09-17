module

/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy
-/

import Architect
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Category.ReflQuiv
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Category.Cat.Limit
public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

@[expose] public section


universe v u

open Simplicial SimplexCategory CategoryTheory SimplexCategory.Truncated
  SimplexCategory.Truncated.Hom SimplicialObject SimplicialObject.Truncated

-- The proofs below need these to unfold while `isDefEq` matches implicit arguments.
-- TODO: upstream. They belong in mathlib carrying `implicit_reducible` at their definition
-- sites; delete this block then.
attribute [local implicit_reducible] _root_.HomRel CategoryTheory.Cat.FreeRefl
  CategoryTheory.Paths SSet.OneTruncation₂

namespace SSet
namespace Truncated

namespace Edge

@[simp]
lemma comp_map {A B C : Truncated.{u} 2} {x₀ x₁ : A _⦋0⦌₂}
    (e : Edge x₀ x₁) (F : A ⟶ B) (G : B ⟶ C) :
    e.map (F ≫ G) = (e.map F).map G := by
  ext; rfl

@[simp]
lemma id_map {A : Truncated.{u} 2} {x y : A _⦋0⦌₂} (e : Edge x y) :
    e.map (𝟙 A) = e := by
  ext; rfl

abbrev edgeMap {S : SSet} {y₀ y₁ : ((truncation 2).obj S) _⦋0⦌₂} (e : Edge y₀ y₁) : Δ[1] ⟶ S :=
  yonedaEquiv.symm e.edge

end Edge

open Truncated.Edge
attribute [blueprint
  "defn:2-truncated-qcat"
  (statement := /--
  A 2-truncated simplicial set $A$ is a \textbf{2-truncated quasi-category} if it admits the
  following three operations:
  \begin{itemize}
  \item (2,1)-filling: any path $f_\bullet$ of length 2 in $A$ may be filled to a $2$-simplex whose
  spine equals the given path.
  \item (3,1)-filling: given any path $f_\bullet$ of length 3 in $A$, 2-simplices $\sigma_3$ and
  $\sigma_0$ filling the restricted paths $f_{012}$ and $f_{123}$ respectively, and 2-simplex
  $\sigma_2$ filling the path formed by $f_{01}$ and the diagonal of $\sigma_0$, there is a
  2-simplex $\sigma_1$ filling the path formed by the diagonal of $\sigma_3$ and $f_{23}$ and whose
  diagonal is the diagonal of $\sigma_2$.
  \item (3,2)-filling: given any path $f_\bullet$ of length 3 in $A$, 2-simplices $\sigma_3$ and
  $\sigma_0$ filling the restricted paths $f_{012}$ and $f_{123}$ respectively, and 2-simplex
  $\sigma_1$ filling the path formed by the diagonal of $\sigma_3$ and $f_{23}$, there is a
  2-simplex $\sigma_2$ filling the path formed by $f_{01}$ and the diagonal of $\sigma_0$ and whose
  diagonal is the diagonal of $\sigma_1$.
  \end{itemize}
  -/)]
Quasicategory₂

end Truncated

namespace horn₂₁
open Truncated (Edge Edge.edgeMap Edge.CompStruct truncEquiv trunc_map trunc_map')
open Truncated.Edge

/-- The inclusion `ι₁₂ : Δ[1] ⟶ Λ[2, 1]` restricts `Λ[2, 1].ι` to the face map `δ 0`. -/
lemma incl₀ : horn₂₁.ι₁₂ ≫ Λ[2, 1].ι = stdSimplex.δ 0 := horn.ι_ι _ _ _

/-- The inclusion `ι₀₁ : Δ[1] ⟶ Λ[2, 1]` restricts `Λ[2, 1].ι` to the face map `δ 2`. -/
lemma incl₂ : horn₂₁.ι₀₁ ≫ Λ[2, 1].ι = stdSimplex.δ 2 := horn.ι_ι _ _ _

variable {S : SSet} {x₀ x₁ x₂ : ((truncation 2).obj S) _⦋0⦌₂}
  (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)

lemma path_edges_comm :
    stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ edgeMap e₀₁ =
      stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ edgeMap e₁₂ := by
  show stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
      yonedaEquiv.symm e₀₁.edge =
    stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
      yonedaEquiv.symm e₁₂.edge
  rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
  congr 1
  apply Eq.trans
  . exact e₀₁.tgt_eq
  . symm; exact e₁₂.src_eq

/--
Given the data of two consecutive edges `e₀₁` and `e₁₂`, construct a map
`Λ[2, 1].toSSet ⟶ S` which restricts to maps `Δ[1] ⟶ S` corresponding
to the two edges (this is made precise in the lemmas `horn_from_edges_restr₀` and
`horn_from_edges_restr₁`).
-/
noncomputable def fromEdges : Λ[2, 1].toSSet ⟶ S :=
  horn₂₁.isPushout.desc (edgeMap e₀₁) (edgeMap e₁₂) (path_edges_comm e₀₁ e₁₂)

/-- See `horn_from_edges` for details. -/
lemma horn_from_edges_restr₀ : horn₂₁.ι₁₂ ≫ (fromEdges e₀₁ e₁₂) = yonedaEquiv.symm e₁₂.edge :=
  horn₂₁.isPushout.inr_desc (edgeMap e₀₁) (edgeMap e₁₂) (path_edges_comm e₀₁ e₁₂)

/-- See `horn_from_edges` for details. -/
lemma horn_from_edges_restr₁ : horn₂₁.ι₀₁ ≫ (fromEdges e₀₁ e₁₂) = yonedaEquiv.symm e₀₁.edge :=
  horn₂₁.isPushout.inl_desc (edgeMap e₀₁) (edgeMap e₁₂) (path_edges_comm e₀₁ e₁₂)

/--
Given a map `Δ[2] ⟶ S` extending the horn given by `horn_from_edges`, construct
and edge `e₀₂` such that `e₀₁`, `e₁₂`, `e₀₂` bound a 2-simplex of `S` (this is witnessed
by `CompStruct e₀₁ e₁₂ e₀₂`).
-/
def fromHornExtension
    (g : Δ[2] ⟶ S)
    (comm : fromEdges e₀₁ e₁₂ = Λ[2, 1].ι ≫ g) :
    Σ e₀₂ : Edge x₀ x₂, Edge.CompStruct e₀₁ e₁₂ e₀₂ := by
  constructor; swap
  exact {
    edge := (truncEquiv 2) <| yonedaEquiv <| stdSimplex.δ 1 ≫ g
    src_eq := by
      rw [← e₀₁.src_eq, trunc_map]
      dsimp [SimplicialObject.δ]
      have : yonedaEquiv.symm (e₀₁.edge) = stdSimplex.δ 2 ≫ g := by
        rw [← horn_from_edges_restr₁ e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      rw [push_yonedaEquiv this]
      have : δ 1 ≫ δ 2 = δ 1 ≫ @δ 1 1 :=
        SimplexCategory.δ_comp_δ (n := 0) (i := 1) (j := 1) (le_refl 1)
      rw [this]
      apply push_yonedaEquiv
      rw [Equiv.symm_apply_apply]; rfl
    tgt_eq := by
      rw [← e₁₂.tgt_eq, trunc_map]
      dsimp [SimplicialObject.δ]
      have : yonedaEquiv.symm (e₁₂.edge) = stdSimplex.δ 0 ≫ g := by
        rw [← horn_from_edges_restr₀ e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₀]
      rw [push_yonedaEquiv this]
      have : δ 0 ≫ δ 0 = δ 0 ≫ @δ 1 1 :=
        (SimplexCategory.δ_comp_δ (n := 0) (i := 0) (j := 0) (le_refl 0)).symm
      rw [this]
      apply push_yonedaEquiv
      rw [Equiv.symm_apply_apply]; rfl
  }
  exact {
    simplex := (truncEquiv 2) <| yonedaEquiv g
    d₂ := by
      rw [trunc_map]
      have : yonedaEquiv.symm (e₀₁.edge) = stdSimplex.δ 2 ≫ g := by
        rw [← horn_from_edges_restr₁ e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      rw [← push_yonedaEquiv' this]
      rfl
    d₀ := by
      rw [trunc_map]
      have : yonedaEquiv.symm (e₁₂.edge) = stdSimplex.δ 0 ≫ g := by
        rw [← horn_from_edges_restr₀ e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₀]
      rw [← push_yonedaEquiv' this]
      rfl
    d₁ := by
      rw [trunc_map]
      dsimp only [len_mk, id_eq, Nat.reduceAdd, Fin.isValue, eq_mpr_eq_cast, cast_eq, op_comp,
        Fin.succ_zero_eq_one, Fin.castSucc_zero]
      rw [← map_yonedaEquiv']
      rfl
  }

end horn₂₁

/-- If two `2`-simplices of `S` have equal `i`-th and `j`-th faces, then the corresponding face
restrictions `Δ[1] ⟶ S` of their classifying maps `Δ[2] ⟶ S` agree. -/
lemma δ_comp_yonedaEquiv_symm_eq {S : SSet} {i j : Fin 3} {σ τ : S _⦋2⦌}
    (h : S.map (SimplexCategory.δ i).op σ = S.map (SimplexCategory.δ j).op τ) :
    stdSimplex.map (SimplexCategory.δ i) ≫ yonedaEquiv.symm σ =
      stdSimplex.map (SimplexCategory.δ j) ≫ yonedaEquiv.symm τ := by
  rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm, h]

namespace horn₃₁
open Truncated (Edge Edge.edgeMap Edge.CompStruct truncEquiv trunc_map trunc_map')
open Truncated.Edge

variable {S : SSet}
variable
    {x₀ x₁ x₂ x₃ : ((truncation 2).obj S) _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
    (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
    (f₂ : CompStruct e₀₁ e₁₃ e₀₃)

/-- The face inclusions `ι₀/ι₂/ι₃ : Δ[2] ⟶ Λ[3, 1]` restrict `Λ[3, 1].ι` to `δ 0/2/3`. -/
lemma incl₀ : horn₃₁.ι₀ ≫ Λ[3, 1].ι = stdSimplex.δ 0 := horn.ι_ι _ _ _
lemma incl₂ : horn₃₁.ι₂ ≫ Λ[3, 1].ι = stdSimplex.δ 2 := horn.ι_ι _ _ _
lemma incl₃ : horn₃₁.ι₃ ≫ Λ[3, 1].ι = stdSimplex.δ 3 := horn.ι_ι _ _ _

include S x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃ f₃ f₀ f₂

/--
Glue the three faces `f₃`, `f₀`, `f₂` into a map `Λ[3, 1].toSSet ⟶ S` via the multicoequalizer
presentation of the horn (`horn₃₁.desc`). The three hypotheses are the compatibilities of the
faces along their shared edges `e₁₂`, `e₁₃`, `e₀₁`.
-/
noncomputable def fromFaces : Λ[3, 1].toSSet ⟶ S :=
  horn₃₁.desc (yonedaEquiv.symm f₀.simplex) (yonedaEquiv.symm f₂.simplex)
    (yonedaEquiv.symm f₃.simplex)
    (δ_comp_yonedaEquiv_symm_eq ((f₀.d₂).trans (f₃.d₀).symm))
    (δ_comp_yonedaEquiv_symm_eq ((f₀.d₁).trans (f₂.d₀).symm))
    (δ_comp_yonedaEquiv_symm_eq ((f₂.d₂).trans (f₃.d₂).symm))

/-
A group of lemmas stating that the faces of the simplex `Δ[3] ⟶ S` extending the horn
`fromFaces f₃ f₀ f₂ : Λ[3, 1] ⟶ S` are as expected.
-/
lemma horn_extension_face₀ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₀.simplex = stdSimplex.δ 0 ≫ g := by
  have : horn₃₁.ι₀ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₀.simplex :=
    horn₃₁.ι₀_desc _ _ _ _ _ _
  rw [← this, comm, ← Category.assoc, incl₀]

lemma horn_extension_face₂ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₂.simplex = stdSimplex.δ 2 ≫ g := by
  have : horn₃₁.ι₂ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₂.simplex :=
    horn₃₁.ι₂_desc _ _ _ _ _ _
  rw [← this, comm, ← Category.assoc, incl₂]

lemma horn_extension_face₃ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : horn₃₁.ι₃ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₃.simplex :=
    horn₃₁.ι₃_desc _ _ _ _ _ _
  rw [← this, comm, ← Category.assoc, incl₃]

/--
Given a map `Δ[3] ⟶ S` extending the horn given by `fromFaces`, obtain a
2-simplex bounded by edges `e₀₂`, `e₂₃` and `e₀₃`. See also `Quasicategory₂.fill31`.
-/
def fromHornExtension
    (g : Δ[3] ⟶ S)
    (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    (CompStruct e₀₂ e₂₃ e₀₃) where
  simplex := (truncEquiv 2) <| S.map (SimplexCategory.δ 1).op (yonedaEquiv g)
  d₂ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 2) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.reduceSucc, Fin.castSucc_one] at this
    rw [← f₃.d₁, trunc_map, trunc_map', ← Functor.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₃ f₃ f₀ f₂ comm), this]
  d₀ := by
    rw [← f₀.d₀, trunc_map, trunc_map', ← Functor.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₀ f₃ f₀ f₂ comm)]
    rfl
  d₁ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.reduceSucc, Fin.castSucc_one] at this
    rw [← f₂.d₁, trunc_map, trunc_map', ← Functor.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₂ f₃ f₀ f₂ comm), this]

end horn₃₁

namespace horn₃₂
open Truncated (Edge Edge.edgeMap Edge.CompStruct truncEquiv trunc_map trunc_map')
open Truncated.Edge

variable {S : SSet}
variable
    {x₀ x₁ x₂ x₃ : ((truncation 2).obj S) _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
    (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
    (f₁ : CompStruct e₀₂ e₂₃ e₀₃)

/-- The face inclusions `ι₀/ι₁/ι₃ : Δ[2] ⟶ Λ[3, 2]` restrict `Λ[3, 2].ι` to `δ 0/1/3`. -/
lemma incl₀ : horn₃₂.ι₀ ≫ Λ[3, 2].ι = stdSimplex.δ 0 := horn.ι_ι _ _ _
lemma incl₁ : horn₃₂.ι₁ ≫ Λ[3, 2].ι = stdSimplex.δ 1 := horn.ι_ι _ _ _
lemma incl₃ : horn₃₂.ι₃ ≫ Λ[3, 2].ι = stdSimplex.δ 3 := horn.ι_ι _ _ _

include S x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃ f₃ f₀ f₁

/--
Glue the three faces `f₃`, `f₀`, `f₁` into a map `Λ[3, 2].toSSet ⟶ S` via the multicoequalizer
presentation of the horn (`horn₃₂.desc`). The three hypotheses are the compatibilities of the
faces along their shared edges `e₀₂`, `e₁₂`, `e₂₃`.
-/
noncomputable def fromFaces : Λ[3, 2].toSSet ⟶ S :=
  horn₃₂.desc (yonedaEquiv.symm f₀.simplex) (yonedaEquiv.symm f₁.simplex)
    (yonedaEquiv.symm f₃.simplex)
    (δ_comp_yonedaEquiv_symm_eq ((f₁.d₂).trans (f₃.d₁).symm))
    (δ_comp_yonedaEquiv_symm_eq ((f₀.d₂).trans (f₃.d₀).symm))
    (δ_comp_yonedaEquiv_symm_eq ((f₀.d₀).trans (f₁.d₀).symm))

/-
A group of lemmas stating that the faces of the simplex `Δ[3] ⟶ S` extending the horn
`fromFaces f₃ f₀ f₁ : Λ[3, 2] ⟶ S` are as expected.
-/
lemma horn_extension_face₀ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₀.simplex = stdSimplex.δ 0 ≫ g := by
  have : horn₃₂.ι₀ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₀.simplex :=
    horn₃₂.ι₀_desc _ _ _ _ _ _
  rw [← this, comm, ← Category.assoc, incl₀]

lemma horn_extension_face₁ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₁.simplex = stdSimplex.δ 1 ≫ g := by
  have : horn₃₂.ι₁ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₁.simplex :=
    horn₃₂.ι₁_desc _ _ _ _ _ _
  rw [← this, comm, ← Category.assoc, incl₁]

lemma horn_extension_face₃ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : horn₃₂.ι₃ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₃.simplex :=
    horn₃₂.ι₃_desc _ _ _ _ _ _
  rw [← this, comm, ← Category.assoc, incl₃]

/--
Given a map `Δ[3] ⟶ S` extending the horn given by `fromFaces`, obtain a
2-simplex bounded by edges `e₀₁`, `e₁₃` and `e₀₃`. See also `Quasicategory₂.fill32`.
-/
def fromHornExtension
    (g : Δ[3] ⟶ S)
    (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    (CompStruct e₀₁ e₁₃ e₀₃) where
  simplex := (truncEquiv 2) <| S.map (SimplexCategory.δ 2).op (yonedaEquiv g)
  d₂ := by
    have := δ_comp_δ (n := 1) (i := 2) (j := 2) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.reduceSucc, Fin.reduceCastSucc] at this
    rw [← f₃.d₂, trunc_map, trunc_map', ← Functor.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₃ f₃ f₀ f₁ comm), this]
  d₀ := by
    have := δ_comp_δ (n := 1) (i := 0) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two, Fin.castSucc_zero] at this
    rw [← f₀.d₁, trunc_map, trunc_map', ← Functor.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₀ f₃ f₀ f₁ comm), this]
  d₁ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two, Fin.castSucc_one] at this
    rw [← f₁.d₁, trunc_map, trunc_map', ← Functor.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₁ f₃ f₀ f₁ comm), this]

end horn₃₂

namespace Truncated

/--
The 2-truncation of a quasi-category is a 2-truncated quasi-category.
-/
@[blueprint
  "lem:2-truncated-qcat"
  (statement := /-- The 2-truncation of a quasi-category is a 2-truncated quasi-category. -/)
  (proof := /-- Immediate from the definition by filling horns in dimensions 2 and 3. -/)
  (latexEnv := "lemma")]
instance two_truncatation_of_qc_is_2_trunc_qc {X : SSet} [Quasicategory X] :
    Quasicategory₂ ((truncation 2).obj X) where
  fill21 e₀₁ e₁₂ := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp)
      (horn₂₁.fromEdges e₀₁ e₁₂)
    apply Nonempty.intro
    exact (horn₂₁.fromHornExtension e₀₁ e₁₂ g h)
  fill31 f₃ f₀ f₂ := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp)
      (horn₃₁.fromFaces f₃ f₀ f₂)
    apply Nonempty.intro
    exact (horn₃₁.fromHornExtension f₃ f₀ f₂ g h)
  fill32 f₃ f₀ f₁ := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling (by simp) (by simp)
      (horn₃₂.fromFaces f₃ f₀ f₁)
    apply Nonempty.intro
    exact (horn₃₂.fromHornExtension f₃ f₀ f₁ g h)

namespace Edge

namespace CompStruct

variable {A : Truncated 2}

end CompStruct

end Edge

section homotopy_def

open Truncated.Edge

attribute [blueprint
  "defn:1-simplex-htpy"
  (title := "homotopy relation on 1-simplices")
  (statement := /--
   A parallel pair of 1-sim\-plices $f,g$ in a simplicial set $X$ are \textbf{homotopic} if there
   exists a 2-simplex whose boundary takes either of the following forms\footnote{The symbol ``$=$''
   is used in diagrams to denote a degenerate simplex or an identity arrow.}
   %\footnote{The symbol ``$\!\!\!\!\!\begin{tikzcd}[ampersand replacement=\&, sep=small] ~\arrow[r,
   % equals] \& ~ \end{tikzcd}\!\!\!\!\!$'' is used in diagrams to denote a degenerate simplex or an
   % identity arrow.}
   \begin{center}
   \begin{tikzcd}[row sep=small, column sep=small]
   & y \arrow[dr, equals] & && &  x \arrow[dr, "f"]  \\ x \arrow[ur, "f"] \arrow[rr, "g"'] & & y & &
   x \arrow[ur, equals] \arrow[rr, "g"'] & & y
   \end{tikzcd}
  \end{center}
   or if $f$ and $g$ are in the same equivalence class generated by this relation.
  -/)]
HomotopicL

attribute [blueprint "defn:1-simplex-htpy"]
HomotopicR

end homotopy_def

end Truncated

/-- The full subcategory of 2-truncated simplicial sets that are quasicategories. -/
abbrev QCat₂ := ObjectProperty.FullSubcategory Truncated.Quasicategory₂.{u}

instance QCat₂.quasicategory₂ {A : QCat₂} : Truncated.Quasicategory₂ A.obj := A.property

namespace Quasicategory₂
open Truncated Edge.CompStruct

section homotopy_relation
open Edge

variable {A : Truncated 2} [Quasicategory₂ A]

omit [Quasicategory₂ A] in
/--
Left homotopy relation is reflexive
-/
@[blueprint
  "lem:2-truncated-qcat-htpy"
  (statement := /--
  If $A$ is a 2-truncated quasi-category then:
  \begin{enumerate}
    \item The left and right homotopy relations are reflexive.
    \item The left and right homotopy relations are symmetric.
    \item The left and right homotopy relations are transitive.
    \item The left homotopy relation coincides with the right homotopy relation.
  \end{enumerate}
  -/)
  (proof := /--
  Each statement follows from a single 3-dimensional horn filling, typically involving degenerate
  simplices.
  -/)
  (latexEnv := "lemma")]
lemma HomotopicL.refl {x y : A _⦋0⦌₂} {f : Truncated.Edge x y} :
    HomotopicL f f := ⟨compId f⟩

/--
Left homotopy relation is symmetric
-/
@[blueprint "lem:2-truncated-qcat-htpy"]
lemma HomotopicL.symm {x y : A _⦋0⦌₂} {f g : Truncated.Edge x y} (hfg : HomotopicL f g) :
    HomotopicL g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idCompId y) (compId f)

/--
Left homotopy relation is transitive
-/
@[blueprint "lem:2-truncated-qcat-htpy"]
lemma HomotopicL.trans {x y : A _⦋0⦌₂} {f g h : Truncated.Edge x y} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) :
    HomotopicL f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idCompId y) hgh

omit [Quasicategory₂ A] in
/--
Right homotopy relation is reflexive
-/
@[blueprint "lem:2-truncated-qcat-htpy"]
lemma HomotopicR.refl  {x y : A _⦋0⦌₂} {f : Truncated.Edge x y} : HomotopicR f f := ⟨idComp f⟩

/--
Right homotopy relation is symmetric
-/
@[blueprint "lem:2-truncated-qcat-htpy"]
lemma HomotopicR.symm {x y : A _⦋0⦌₂} {f g : Truncated.Edge x y} (hfg : HomotopicR f g) :
    HomotopicR g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idCompId x) hfg (idComp f)

/--
Right homotopy relation is transitive
-/
@[blueprint "lem:2-truncated-qcat-htpy"]
lemma HomotopicR.trans {x y : A _⦋0⦌₂} {f g h : Truncated.Edge x y} (hfg : HomotopicR f g)
    (hgh : HomotopicR g h) :
    HomotopicR f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idCompId x) hfg hgh

/--
The right and left homotopy relations coincide
-/
@[blueprint "lem:2-truncated-qcat-htpy"]
theorem HomotopicL_iff_HomotopicR {x y : A _⦋0⦌₂} {f g : Truncated.Edge x y} :
    HomotopicL f g ↔ HomotopicR f g := by
  constructor
  . rintro ⟨lhfg⟩
    exact Quasicategory₂.fill32 (idComp f) (compId f) lhfg
  . rintro ⟨rhfg⟩
    exact Quasicategory₂.fill31 (idComp f) (compId f) rhfg

end homotopy_relation

section basic_homotopies
open Edge

variable {A : Truncated 2} [Quasicategory₂ A]
variable {x y z : A _⦋0⦌₂}

lemma comp_unique {f : Truncated.Edge x y} {g : Truncated.Edge y z} {h h' : Truncated.Edge x z}
    (s : CompStruct f g h) (s' : CompStruct f g h') : HomotopicL h h' :=
  HomotopicL_iff_HomotopicR.mpr (Quasicategory₂.fill32 (idComp f) s s')

lemma comp_unique' {f : Truncated.Edge x y} {g : Truncated.Edge y z} {h h' : Truncated.Edge x z}
    (s : Nonempty (CompStruct f g h)) (s' : Nonempty (CompStruct f g h')) : HomotopicL h h' := by
  apply Nonempty.elim s
  apply Nonempty.elim s'
  intro t' t; exact comp_unique t t'

@[blueprint
  "lem:2-truncated-qcat-htpy-comp"
  (statement := /--
   $\quad$
  \begin{enumerate}
    \item If $\sigma$ and $\tau$ are 2-simplices in a 2-truncated quasi-category filling the same
    path, their diagonal edges are homotopic.
    \item If $h$ is the diagonal edge of a 2-simplex filling the path formed by $f$ and $g$ and $g$
    is homotopic to $g'$, then $h$ is the diagonal edge of a 2-simplex filling the path formed by
    $f$ and $g'$.
    \item If $h$ is the diagonal edge of a 2-simplex filling the path formed by $f$ and $g$ and $f$
    is homotopic to $f'$, then $h$ is the diagonal edge of a 2-simplex filling the path formed by
    $f'$ and $g$.
  \end{enumerate}
  -/)
  (proof := /--
  For (i), fill the (3,2)-horn filling the path formed by a degenerate edge, followed by the given
  path edges, and using the given simplices as the 0th and 1st faces. The proofs of (ii) and (iii)
  are similar.
  -/)
  (latexEnv := "lemma")]
lemma transport_edge₀ {f : Truncated.Edge x y} {g g' : Truncated.Edge y z} {h : Truncated.Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL g g') : Nonempty (CompStruct f g' h) := by
  rcases htpy with ⟨htpy⟩
  exact Quasicategory₂.fill32 s htpy (compId h)

@[blueprint "lem:2-truncated-qcat-htpy-comp"]
lemma transport_edge₁ {f : Truncated.Edge x y} {g : Truncated.Edge y z} {h h' : Truncated.Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL h h') : Nonempty (CompStruct f g h') := by
  rcases (HomotopicL_iff_HomotopicR.mp htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 (idComp f) s htpy

@[blueprint "lem:2-truncated-qcat-htpy-comp"]
lemma transport_edge₂ {f f' : Truncated.Edge x y} {g : Truncated.Edge y z} {h : Truncated.Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL f f') : Nonempty (CompStruct f' g h) := by
  rcases (HomotopicL_iff_HomotopicR.mp htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 htpy s (idComp h)

@[blueprint
  "cor:2-truncated-qcat-htpy-comp"
  (statement := /--
  Suppose there is a 2-simplex in a 2-truncated quasi-category with spine formed by the paths $f$
  and $g$ and diagonal $h$. Then if $f \sim f'$, $g \sim g'$, and $h \sim h'$, there is a 2-simplex
  with spine formed by $f'$ and $g'$ and diagonal $h'$.
  -/)
  (proof := /--
  Apply the three conclusions of Lemma \ref{lem:2-truncated-qcat-htpy-comp} one at a time to
  transform the given 2-simplex.
  -/)
  (latexEnv := "corollary")]
lemma transport_all_edges {f f' : Truncated.Edge x y} {g g' : Truncated.Edge y z}
    {h h' : Truncated.Edge x z} (hf : HomotopicL f f') (hg : HomotopicL g g') (hh : HomotopicL h h')
    (s : CompStruct f g h) :
    Nonempty (CompStruct f' g' h') := by
  have a : Nonempty (CompStruct f' g h) := transport_edge₂ s hf
  have b : Nonempty (CompStruct f' g' h) := by
    rcases a with ⟨a⟩
    exact transport_edge₀ a hg
  rcases b with ⟨b⟩
  exact transport_edge₁ b hh

end basic_homotopies

section homotopy_category
open Edge

variable {A : Truncated 2} [Quasicategory₂ A]

attribute [blueprint
  "defn:2-truncated-qcat-htpy-cat"
  (title := "the homotopy category of a 2-truncated quasi-category")
  (statement := /--
  If $A$ is a 2-truncated quasi-category then its \textbf{homotopy category} $\ho{A}$ has
  \begin{itemize}
  \item the set of 0-simplices $A_0$ as its objects
  \item the set of homotopy classes of 1-simplices $A_1$ as its arrows
  \item the identity arrow at $a \in A_0$ represented by the degenerate 1-simplex $a \cdot \degen^0
  \in A_1$
  \item a composition relation $h = g \circ f$ in $\ho{A}$ between the homotopy classes of arrows
  represented by any given 1-simplices $f,g,h \in A_1$ if and only if there exists a 2-simplex with
  boundary
  \begin{center}
  \begin{tikzcd}[row sep=small, column sep=small]
  & a_1 \arrow[dr, "g"] \\ a_0 \arrow[ur, "f"] \arrow[rr, "h"'] & & a_2
  \end{tikzcd}
  \end{center}
  \end{itemize}
  -/)]
SSet.Truncated.instCategoryHomotopyCategory₂

end homotopy_category

section isomorphism_of_htpy_categories
open Cat (FreeRefl)
open Edge

variable {A : Truncated.{u} 2} [Quasicategory₂ A]

/--
  The reflexive prefunctor sending edges (in the 1-truncation) of `A` to their homotopy class.
-/
noncomputable
def quotientReflPrefunctor₂ : (OneTruncation₂.{u} A) ⥤rq (HomotopyCategory₂.{u} A) where
  obj X := ⟨X⟩
  map f := Quotient.mk' { edge := f.edge, src_eq := f.src_eq, tgt_eq := f.tgt_eq }

/--
  By the adjunction `ReflQuiv.adj`, we obtain a functor from the free category on the reflexive
  quiver underlying `A` to the homotopy category corresponding to `quotientReflPrefunctor₂`.
-/
noncomputable
def quotientFunctor₂ : FreeRefl (OneTruncation₂ A) ⥤ HomotopyCategory₂ A :=
  ((ReflQuiv.adj.homEquiv
    (V := (ReflQuiv.of (OneTruncation₂ A)))
    (C := (Cat.of (HomotopyCategory₂ A)))).invFun quotientReflPrefunctor₂)

/--
  The adjoint relation between `quotientReflPrefunctor₂` and `quotientFunctor₂` expressed
  on the level of functors.
-/
lemma unit_app_quotientFunctor : quotientReflPrefunctor₂ =
    (ReflQuiv.adj.unit.app (ReflQuiv.of (OneTruncation₂ A))) ⋙rq quotientFunctor₂.{u}.toReflPrefunctor := by
  let η := ReflQuiv.adj.unit.app (ReflQuiv.of (OneTruncation₂ A))
  let q : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ A)) ⟶ Cat.of (HomotopyCategory₂ A) :=
    quotientFunctor₂.{u}.toCatHom
  let r : ReflQuiv.of (OneTruncation₂ A) ⟶ ReflQuiv.of (HomotopyCategory₂ A) :=
    quotientReflPrefunctor₂
  show r = η ≫ ReflQuiv.forget.map q
  have : η ≫ ReflQuiv.forget.map q = ReflQuiv.adj.homEquiv q.toFunctor := rfl
  rw [this]
  dsimp [r, q, quotientFunctor₂]
  symm
  apply Equiv.apply_symm_apply

-- lemma quotientFunctor_obj (x : FreeRefl (OneTruncation₂ A)) : quotientFunctor₂.obj x = x.as := rfl

-- The `dsimp` chain below leaves a `Quot.liftOn` and a `Cat.of` bundling whose implicit
-- arguments agree only at `default` transparency.
set_option backward.isDefEq.respectTransparency false in
lemma qFunctor_map_toPath (x y : FreeRefl.{u} (OneTruncation₂ A))
    (f : Truncated.Edge x.as y.as) :
    quotientFunctor₂.map.{u}
      ((FreeRefl.quotientFunctor _).map (Quiver.Hom.toPath f)) =
      quotientReflPrefunctor₂.map f := by
  dsimp [quotientFunctor₂, Adjunction.homEquiv, FreeRefl.lift]
  dsimp [quotientReflPrefunctor₂, FreeRefl.homMk,
    FreeRefl.quotientFunctor, Quotient.functor, ReflQuiv.adj, ReflQuiv.adj.homEquiv,
    FreeRefl.lift, Paths.lift, CategoryTheory.Quotient.lift, Cat.Hom.equivFunctor]
  rw [Quot.liftOn_mk]
  change 𝟙 _ ≫ _ = _
  simp

/--
  The edge `composeEdges f g` is the unique edge up to homotopy such that there is
  a 2-simplex with spine given by `f` and `g`.
-/
lemma composeEdges_unique {x₀ x₁ x₂ : A _⦋0⦌₂} {f : Truncated.Edge x₀ x₁} {g : Truncated.Edge x₁ x₂}
    {h : Truncated.Edge x₀ x₂} (s : CompStruct f g h) : HomotopicL h (f.comp g) := by
  apply comp_unique' ⟨s⟩
  exact nonempty_iff.mpr rfl

/--
  `quotientFunctor₂` respects the hom relation `HoRel₂`.
-/
theorem qFunctor_respects_horel₂ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
    (f g : x ⟶ y) (r : OneTruncation₂.HoRel₂ _ f g) :
    quotientFunctor₂.map.{u} f = quotientFunctor₂.map.{u} g := by
  rcases r with @⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, hcs⟩
  simp only [Functor.map_comp, qFunctor_map_toPath]
  exact hcs.homotopyCategory₂_fac

/--
An edge from `x₀` to `x₁` in a 2-truncated simplicial set defines an arrow in the refl quiver
`OneTruncation₂.{u} A)` from `x₀` to `x₁`.
-/
def edgeToHom {x₀ x₁ : A _⦋0⦌₂} (f : Truncated.Edge x₀ x₁) :
    @Quiver.Hom (OneTruncation₂.{u} A) _ x₀ x₁ where
  edge := f.edge
  src_eq := f.src_eq
  tgt_eq := f.tgt_eq

/--
An edge from `x₀` to `x₁` in a 2-truncated simplicial set defines an arrow in the free category
generated from the refl quiver `OneTruncation₂.{u} A)` from `x₀` to `x₁`.
-/
def edgeToFreeHom {x₀ x₁ : A _⦋0⦌₂} (f : Truncated.Edge x₀ x₁) :
    @Quiver.Hom (FreeRefl.{u} (OneTruncation₂.{u} A)) _ ⟨x₀⟩ ⟨x₁⟩ :=
  Quot.mk _ (edgeToHom f).toPath

omit [Quasicategory₂ A] in
lemma compose_id_path {x₀ x₁ : A _⦋0⦌₂} (f : Truncated.Edge x₀ x₁) :
    edgeToFreeHom f = Quot.mk _
      ((edgeToHom f).toPath.comp (edgeToHom (Truncated.Edge.id x₁)).toPath) := by
  rw [show edgeToFreeHom f = FreeRefl.homMk (edgeToHom f) from rfl]
  rw [← Category.comp_id (FreeRefl.homMk (edgeToHom f)),
      ← FreeRefl.homMk_id (V := OneTruncation₂ A) x₁]
  rw [Quiver.Path.comp_toPath_eq_cons]
  rfl

omit [Quasicategory₂ A] in
/--
  Two (left) homotopic edges `f`, `g` are equivalent under the hom-relation `HoRel₂`
  generated by 2-simplices.
-/
lemma homotopic_edges_are_equiv {x₀ x₁ : A _⦋0⦌₂} (f g : Truncated.Edge.{u} x₀ x₁) (htpy : HomotopicL f g) :
    OneTruncation₂.HoRel₂ _ (edgeToFreeHom f) (edgeToFreeHom g) := by
  rw [compose_id_path f]
  rcases htpy with ⟨htpy⟩
  exact OneTruncation₂.HoRel₂.of_compStruct htpy

/--
  If a reflexive prefunctor `F : FreeRefl (OneTruncation₂ A) ⥤rq C` respects
  the hom-relation `HoRel₂`, then it can be lifted to  `HomotopyCategory₂ A`.
-/
noncomputable
def liftRq₂ {C : Type*} [ReflQuiver C] (F : FreeRefl.{u} (OneTruncation₂.{u} A) ⥤rq C)
    (h : ∀ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : x ⟶ y),
      (r : OneTruncation₂.HoRel₂ _ f g) → F.map f = F.map g) :
    HomotopyCategory₂.{u} A ⥤rq C where
  obj x := F.obj ⟨x.1⟩
  map f := Quotient.liftOn f
    (fun e ↦ F.map (edgeToFreeHom e))
    (fun f g ↦ by
      intro htpy
      apply h
      exact homotopic_edges_are_equiv f g htpy)
  map_id := by
    intro x
    dsimp [CategoryStruct.id]
    have e : edgeToFreeHom (Truncated.Edge.id x.pt) = 𝟙 (⟨x.1⟩ : FreeRefl.{u} (OneTruncation₂.{u} A)) :=
      FreeRefl.homMk_id (V := OneTruncation₂ A) x.pt
    show F.map (edgeToFreeHom (Truncated.Edge.id x.pt)) = 𝟙rq (F.obj ⟨x.1⟩)
    rw [e]
    exact F.map_id _

theorem lift_unique_rq₂ {C} [ReflQuiver.{u, u} C] (F₁ F₂ : (HomotopyCategory₂.{u} A) ⥤rq C)
    (h : quotientReflPrefunctor₂ ⋙rq F₁ = quotientReflPrefunctor₂ ⋙rq F₂) : F₁ = F₂ := by
  refine ReflPrefunctor.ext (fun X => ?_) (fun X Y => Quotient.ind (fun f => ?_))
  · exact ReflPrefunctor.congr_obj h X.pt
  · -- `F₁.map`/`F₂.map` lie over defeq-but-distinct objects; compare via `≍`.
    symm
    apply eq_of_heq
    simp only [eqRec_heq_iff]
    exact (heq_of_eq (ReflPrefunctor.congr_hom h (edgeToHom f))).symm.trans
      (Quiver.homOfEq_heq _ _ _)

/--
  If a functor `F : FreeRefl (OneTruncation₂ A) ⥤ C` respects the hom-relation `HoRel₂`,
  then it can be lifted to  `HomotopyCategory₂ A` (see the weaker statement `liftRq₂`).
-/
noncomputable
def lift₂ {C : Type*} [Category* C] (F : FreeRefl.{u} (OneTruncation₂.{u} A) ⥤ C)
    (h : ∀ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : x ⟶ y),
      (r : OneTruncation₂.HoRel₂ _ f g) → F.map f = F.map g) :
    HomotopyCategory₂ A ⥤ C := by
  let G := liftRq₂ F.toReflPrefunctor h
  exact {
    obj := G.obj
    map := G.map
    map_id := G.map_id
    map_comp := by
      intro x₀ x₁ x₂
      apply Quotient.ind₂
      intro f g
      dsimp only [G, liftRq₂, Quotient.lift_mk, Functor.toReflPrefunctor]
      rw [← Functor.map_comp]
      let p := (Quasicategory₂.fill21 f g).some
      -- `⟦f⟧ ≫ ⟦g⟧` is defeq `⟦p.fst⟧`.
      show F.map (edgeToFreeHom p.fst) = F.map (edgeToFreeHom f ≫ edgeToFreeHom g)
      -- `.symm`: `of_compStruct` orients the relation as `composite`–`single`.
      exact (h _ _ _ _ (OneTruncation₂.HoRel₂.of_compStruct p.snd)).symm
  }

lemma is_lift₂ {C : Type*} [Category* C] (F : FreeRefl.{u} (OneTruncation₂.{u} A) ⥤ C)
    (h : ∀ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : x ⟶ y),
      (r : OneTruncation₂.HoRel₂ _ f g) → F.map f = F.map g) :
    quotientFunctor₂.{u} ⋙ lift₂ F h = F := by
  apply FreeRefl.lift_unique'
  refine Paths.ext_functor rfl ?_
  intro x y f
  simp only [lift₂, liftRq₂, Functor.comp_map]
  rw [qFunctor_map_toPath]
  -- the `eqToHom`s are between defeq objects; pass through `≍`.
  refine (conj_eqToHom_iff_heq' _ _ _ _).mpr ?_
  rfl

/--
  Lifts to the homotopy category are unique.
-/
theorem HomotopyCategory₂.lift_unique' {C : Type u} [Category.{u} C]
    (F₁ F₂ : HomotopyCategory₂.{u} A ⥤ C)
    (h : quotientFunctor₂.{u} ⋙ F₁ = quotientFunctor₂.{u} ⋙ F₂) : F₁ = F₂ := by
  have : F₁.toReflPrefunctor = F₂.toReflPrefunctor := by
    apply lift_unique_rq₂
    rw [unit_app_quotientFunctor.{u}]
    show _ ⋙rq (quotientFunctor₂.{u} ⋙ F₁).toReflPrefunctor =
      _ ⋙rq (quotientFunctor₂.{u} ⋙ F₂).toReflPrefunctor
    rw [h]
  cases F₁; cases F₂; cases this; rfl

/--
  Since both `HomotopyCategory A` and `HomotopyCategory₂ A` satisfy the same universal property,
  they are isomorphic.
-/
@[blueprint
  "lem:htpy-cat-of-qcat"
  (title := "the homotopy category of a quasi-category")
  (statement := /--
  If $A$ is a quasi-category then its \textbf{homotopy category} $\ho{A}$ is isomorphic to the
  homotopy category of its underlying 2-truncated quasi-category, as just described.
  -/)
  (proof := /--
  Given a 2-truncated quasi-category $A$, we can construct a natural isomorphism between its
  2-truncated homotopy category $\ho_2A$ in the sense of Definition \ref{defn:homotopy-cat} and its
  2-truncated homotopy category $\ho{A}$ in the sense of Definition
  \ref{defn:2-truncated-qcat-htpy-cat} by showing the latter satisfies the same universal property
  of the former, as a quotient of the free category $FA$ on the underlying reflexive quiver.

  By adjunction, to define a functor $q \colon FA \to \ho{A}$, it suffices to define a refl
  prefunctor $q \colon A \to \ho{A}$ from the one-truncation of $A$ to the underlying refl quiver of
  $\ho{A}$. The objects of these quivers coincide while the homs in the latter and quotients of the
  homs in the former, defining a canonical quotient map. By construction, the corresponding functor
  $q \colon FA \to \ho{A}$ respects the hom-relation that defines the homotopy category $\ho_2{A}$,
  so the universal property of the latter quotient induces a comparison functor $\ho_2{A} \to
  \ho{A}$ which factors $q$ through the analogously defined functor $q \colon FA \to \ho_2{A}$.

  To see this is an isomorphism, we show that $q \colon FA \to \ho{A}$ satisfies the same universal
  property. To that end, consider another functor $g \colon FA \to C$ respecting the hom-relation.
  In particular, $g$ respects the homotopy relation of Definition \ref{defn:1-simplex-htpy}, since
  this is a special case of the hom-relation. Thus, on underlying refl prefunctors, $g$ factors
  uniquely through $q$ along a map $h \colon \ho{A} \to C$. By Corollary
  \ref{cor:2-truncated-qcat-htpy-comp}, $h$ respects composition and thus lifts to define a functor.
  This gives the required factorization. Uniqueness follows because the the functor $U \colon \Cat
  \to \rQuiv$ is faithful.
  -/)
  (latexEnv := "lemma")]
noncomputable
def isoHomotopyCategories :
    (Cat.of (Truncated.HomotopyCategory.{u} A)) ≅ (Cat.of (HomotopyCategory₂.{u} A)) where
  hom := (CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂).toCatHom
  inv := lift₂ (Truncated.HomotopyCategory.quotientFunctor.{u} A) (fun _ _ _ _ h =>
    CategoryTheory.Quotient.sound _ h) |>.toCatHom
  hom_inv_id := Cat.Hom.ext <| by
    have hspec : Truncated.HomotopyCategory.quotientFunctor.{u} A ⋙
        CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂ = quotientFunctor₂ :=
      Quotient.lift_spec _ quotientFunctor₂ qFunctor_respects_horel₂
    apply Truncated.HomotopyCategory.lift_unique'
    show (Truncated.HomotopyCategory.quotientFunctor.{u} A ⋙
        CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂) ⋙
        lift₂ (Truncated.HomotopyCategory.quotientFunctor.{u} A)
          (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ h)
      = Truncated.HomotopyCategory.quotientFunctor.{u} A
    rw [hspec]
    exact is_lift₂ _ _
  inv_hom_id := Cat.Hom.ext <| by
    have hspec : Truncated.HomotopyCategory.quotientFunctor.{u} A ⋙
        CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂ = quotientFunctor₂ :=
      Quotient.lift_spec _ quotientFunctor₂ qFunctor_respects_horel₂
    apply HomotopyCategory₂.lift_unique'
    show (quotientFunctor₂ ⋙ lift₂ (Truncated.HomotopyCategory.quotientFunctor.{u} A)
          (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ h)) ⋙
        CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂
      = quotientFunctor₂
    have hlift : quotientFunctor₂ ⋙ lift₂ (Truncated.HomotopyCategory.quotientFunctor.{u} A)
        (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ h) =
        Truncated.HomotopyCategory.quotientFunctor.{u} A := is_lift₂ _ _
    rw [hlift]
    exact hspec

end isomorphism_of_htpy_categories

section Functoriality

open Truncated.Edge

variable {A B C : Truncated.{u} 2}

lemma homotopicL_map (F : A ⟶ B)
    {x y : A _⦋0⦌₂} {f f' : Truncated.Edge x y} (h : HomotopicL f f') :
    HomotopicL (f.map F) (f'.map F) := by
  rcases h with ⟨h⟩
  exact ⟨by simpa only [Truncated.Edge.map_id] using h.map F⟩

variable [A.Quasicategory₂] [B.Quasicategory₂] [C.Quasicategory₂]

lemma homotopicL_map_comp (F : A ⟶ B) {x y z : A _⦋0⦌₂}
    (f : Truncated.Edge x y) (g : Truncated.Edge y z) :
    HomotopicL ((f.comp g).map F) ((f.map F).comp (g.map F)) :=
  composeEdges_unique ((f.compStruct g).map F)

namespace mapHomotopyCategory₂

/-- The map on homotopy classes induced by a simplicial map. -/
def map (F : A ⟶ B) {X Y : HomotopyCategory₂ A} (f : X ⟶ Y) :
    HomotopyCategory₂.mk (F.app _ X.pt) ⟶ HomotopyCategory₂.mk (F.app _ Y.pt) :=
  Quotient.liftOn f (fun e ↦ HomotopyCategory₂.homMk (e.map F))
    (fun _ _ h ↦ Quotient.sound (homotopicL_map F h))

lemma map_homMk (F : A ⟶ B) {x y : A _⦋0⦌₂} (e : Truncated.Edge x y) :
    map F (HomotopyCategory₂.homMk e) = HomotopyCategory₂.homMk (e.map F) :=
  rfl

lemma id_map {X Y : HomotopyCategory₂ A} (f : X ⟶ Y) :
    map (𝟙 A) f = f := by
  obtain ⟨f, rfl⟩ := HomotopyCategory₂.homMk_surjective f
  simp only [map_homMk, Truncated.Edge.id_map]

lemma map_id (F : A ⟶ B) (X : HomotopyCategory₂ A) :
    map F (𝟙 X) = 𝟙 (HomotopyCategory₂.mk (F.app _ X.pt)) := by
  rw [← HomotopyCategory₂.homMk_id X, map_homMk, Truncated.Edge.map_id]
  rfl

lemma comp_map (F : A ⟶ B) (G : B ⟶ C)
    {X Y : HomotopyCategory₂ A} (f : X ⟶ Y) :
    map (F ≫ G) f = map G (map F f) := by
  obtain ⟨f, rfl⟩ := HomotopyCategory₂.homMk_surjective f
  simp only [map_homMk, Truncated.Edge.comp_map]

lemma map_comp (F : A ⟶ B)
    {X Y Z : HomotopyCategory₂ A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map F (f ≫ g) = map F f ≫ map F g :=
  Quotient.inductionOn₂ f g (fun f g ↦ Quotient.sound (homotopicL_map_comp F f g))

end mapHomotopyCategory₂

/-- The functor on homotopy categories induced by a map of 2-truncated quasicategories. -/
def mapHomotopyCategory₂ (F : A ⟶ B) :
    HomotopyCategory₂ A ⥤ HomotopyCategory₂ B where
  obj X := ⟨F.app _ X.pt⟩
  map := mapHomotopyCategory₂.map F
  map_id := mapHomotopyCategory₂.map_id F
  map_comp := mapHomotopyCategory₂.map_comp F

@[simp]
lemma mapHomotopyCategory₂_obj (F : A ⟶ B) (x : A _⦋0⦌₂) :
    (mapHomotopyCategory₂ F).obj (HomotopyCategory₂.mk x) = HomotopyCategory₂.mk (F.app _ x) :=
  rfl

@[simp]
lemma mapHomotopyCategory₂_homMk (F : A ⟶ B) {x y : A _⦋0⦌₂} (e : Truncated.Edge x y) :
    (mapHomotopyCategory₂ F).map (HomotopyCategory₂.homMk e) = HomotopyCategory₂.homMk (e.map F) :=
  rfl

variable (A) in
lemma mapHomotopyCategory₂_id :
    mapHomotopyCategory₂ (𝟙 A) = 𝟭 (HomotopyCategory₂ A) := by
  apply CategoryTheory.Functor.hext
  · intro _
    rfl
  · intro _ _ _
    exact heq_of_eq (mapHomotopyCategory₂.id_map _)

lemma mapHomotopyCategory₂_comp (F : A ⟶ B) (G : B ⟶ C) :
    mapHomotopyCategory₂ (F ≫ G) = mapHomotopyCategory₂ F ⋙ mapHomotopyCategory₂ G := by
  apply CategoryTheory.Functor.hext
  · intro _
    rfl
  · intro _ _ _
    exact heq_of_eq (mapHomotopyCategory₂.comp_map _ _ _)

/-- The homotopy category functor on 2-truncated quasicategories. -/
noncomputable def homotopyCategory₂Functor : QCat₂.{u} ⥤ Cat.{u, u} where
  obj A := Cat.of (HomotopyCategory₂ A.obj)
  map F := (mapHomotopyCategory₂ F.hom).toCatHom
  map_id A := Cat.Hom.ext (mapHomotopyCategory₂_id A.obj)
  map_comp F G := Cat.Hom.ext (mapHomotopyCategory₂_comp F.hom G.hom)

end Functoriality

section Comparison

variable {A B : Truncated.{u} 2} [A.Quasicategory₂] [B.Quasicategory₂]

@[simp]
lemma isoHomotopyCategories_hom_obj (x : A _⦋0⦌₂) :
    isoHomotopyCategories.hom.toFunctor.obj (Truncated.HomotopyCategory.mk x) =
      HomotopyCategory₂.mk x :=
  rfl

@[simp]
lemma isoHomotopyCategories_hom_map_homMk {x y : A _⦋0⦌₂} (e : Truncated.Edge x y) :
    isoHomotopyCategories.hom.toFunctor.map (Truncated.HomotopyCategory.homMk e) =
      HomotopyCategory₂.homMk e :=
  qFunctor_map_toPath _ _ _

/-- The comparison between the two homotopy category constructions is natural. -/
lemma isoHomotopyCategories_naturality (f : A ⟶ B) :
    (Truncated.mapHomotopyCategory f).toCatHom ≫ isoHomotopyCategories.hom =
      isoHomotopyCategories.hom ≫ (mapHomotopyCategory₂ f).toCatHom := by
  apply Cat.Hom.ext
  change Truncated.mapHomotopyCategory f ⋙ _ = _ ⋙ _
  refine Truncated.HomotopyCategory.functor_ext (fun _ ↦ rfl) ?_
  intro _ _ e
  apply (conj_eqToHom_iff_heq' _ _ _ _).mpr
  simp only [Functor.comp_map, Truncated.mapHomotopyCategory_homMk,
    isoHomotopyCategories_hom_map_homMk]
  exact (heq_of_eq (isoHomotopyCategories_hom_map_homMk (e.map f))).trans (by rfl)

/-- The homotopy category functor on 2-truncated quasicategories agrees naturally with
the restriction of the homotopy category functor on all 2-truncated simplicial sets. -/
@[blueprint "lem:htpy-cat-of-qcat" (hasProof := true) (latexEnv := "lemma")]
noncomputable def homotopyCategory₂FunctorIso :
    ObjectProperty.ι Quasicategory₂.{u} ⋙ Truncated.hoFunctor₂ ≅ homotopyCategory₂Functor :=
  NatIso.ofComponents (fun A ↦ isoHomotopyCategories (A := A.obj))
    (fun f ↦ isoHomotopyCategories_naturality f.hom)

end Comparison

end Quasicategory₂

end SSet

open CategoryTheory Limits SimplicialObject.Truncated

namespace SSet.Truncated

variable {J : Type u} {F : J → Truncated.{u} 2} {x y z : (∏ᶜ F) _⦋0⦌₂}

/-- Projecting a simplex assembled from a family recovers its component. -/
@[simp]
lemma pi_π_app_piObjIso_inv (n : (SimplexCategory.Truncated 2)ᵒᵖ)
    (s : ∀ j, (F j).obj n) (j : J) :
    (Pi.π F j).app n ((piObjIso F n).inv ((Types.productIso _).inv s)) = s j := by
  have hπ := ConcreteCategory.congr_hom (piObjIso_inv_comp_π F n j)
  dsimp only [types_comp_apply] at hπ
  rw [hπ, Types.productIso_inv_comp_π_apply]

namespace Edge

/-- Assemble edges with the specified coordinatewise endpoints. -/
noncomputable def pi (e : ∀ j, Edge ((Pi.π F j).app _ x) ((Pi.π F j).app _ y)) :
    Edge x y := by
  refine {
    edge := (piObjIso F _).inv ((Types.productIso _).inv (fun j ↦ (e j).edge))
    src_eq := ?_
    tgt_eq := ?_ }
  all_goals
    apply Concrete.Pi.map_ext F ((evaluation _ _).obj _)
    intro j
    rw [evaluation_obj_map, NatTrans.naturality_apply, pi_π_app_piObjIso_inv]
  · exact (e _).src_eq
  · exact (e _).tgt_eq

@[simp]
lemma pi_map_π (e : ∀ j, Edge ((Pi.π F j).app _ x) ((Pi.π F j).app _ y)) (j : J) :
    (pi e).map (Pi.π F j) = e j := by
  ext
  dsimp only [map, pi]
  rw [pi_π_app_piObjIso_inv]

@[simp]
lemma pi_eta (e : Edge x y) :
    pi (fun j ↦ e.map (Pi.π F j)) = e := by
  ext
  apply Concrete.Pi.map_ext F ((evaluation _ _).obj _)
  intro j
  dsimp only [evaluation_obj_map, map, pi]
  rw [pi_π_app_piObjIso_inv]

/-- Assemble composition triangles in a product. -/
noncomputable def CompStruct.pi {e₀₁ : Edge x y} {e₁₂ : Edge y z} {e₀₂ : Edge x z}
    (s : ∀ j, CompStruct (e₀₁.map (Pi.π F j)) (e₁₂.map (Pi.π F j))
      (e₀₂.map (Pi.π F j))) : CompStruct e₀₁ e₁₂ e₀₂ := by
  refine {
    simplex := (piObjIso F _).inv ((Types.productIso _).inv (fun j ↦ (s j).simplex))
    d₂ := ?_
    d₀ := ?_
    d₁ := ?_ }
  all_goals
    apply Concrete.Pi.map_ext F ((evaluation _ _).obj _)
    intro j
    rw [evaluation_obj_map, NatTrans.naturality_apply, pi_π_app_piObjIso_inv]
  · exact (s _).d₂
  · exact (s _).d₀
  · exact (s _).d₁

end Edge

/-- Products of 2-truncated quasicategories are 2-truncated quasicategories. -/
@[blueprint "lem:qcat-products"
  (title := "products of quasi-categories")
  (statement := /-- Quasi-categories are closed under small products, as are 2-truncated
    quasi-categories. -/)
  (proof := /-- A horn in the product can be filled by choosing a filler in each factor.
    The three filling conditions in Definition \ref{defn:2-truncated-qcat} are checked in
    the same way. -/)
  (latexEnv := "lemma")]
instance quasicategory₂_pi [∀ j, (F j).Quasicategory₂] : (∏ᶜ F).Quasicategory₂ where
  fill21 e₀₁ e₁₂ := by
    let s j := (Quasicategory₂.fill21 (e₀₁.map (Pi.π F j)) (e₁₂.map (Pi.π F j))).some
    refine ⟨⟨Edge.pi (fun j ↦ (s j).1), Edge.CompStruct.pi (fun j ↦ ?_)⟩⟩
    convert (s j).2
    exact Edge.pi_map_π (fun j ↦ (s j).1) j
  fill31 f₃ f₀ f₂ :=
    ⟨Edge.CompStruct.pi (fun j ↦ (Quasicategory₂.fill31 (f₃.map (Pi.π F j)) (f₀.map (Pi.π F j))
      (f₂.map (Pi.π F j))).some)⟩
  fill32 f₃ f₀ f₁ :=
    ⟨Edge.CompStruct.pi (fun j ↦ (Quasicategory₂.fill32 (f₃.map (Pi.π F j)) (f₀.map (Pi.π F j))
      (f₁.map (Pi.π F j))).some)⟩

/-- Homotopies in a product are exactly coordinatewise homotopies. -/
@[blueprint "lem:product-1-simplex-htpy"
  (title := "homotopies in products")
  (statement := /-- Two parallel 1-simplices in a small product of 2-truncated simplicial sets
    are left homotopic if and only if their projections to each factor are left homotopic. -/)
  (proof := /-- A 2-simplex in the product is a tuple of 2-simplices, and has the required
    boundary precisely when each component does. -/)
  (latexEnv := "lemma")]
lemma homotopicL_pi_iff (e f : Edge x y) :
    HomotopicL e f ↔ ∀ j, HomotopicL (e.map (Pi.π F j)) (f.map (Pi.π F j)) := by
  constructor
  · rintro ⟨s⟩ j
    exact ⟨by simpa only [Edge.map_id] using s.map (Pi.π F j)⟩
  · intro h
    exact ⟨Edge.CompStruct.pi (fun j ↦ by simpa only [Edge.map_id] using (h j).some)⟩

end SSet.Truncated

namespace SSet.QCat₂

open Truncated

section

variable {J : Type u} {F : J → QCat₂.{u}}

/-- The inclusion creates products of 2-truncated quasicategories. -/
noncomputable instance inclusionCreatesProduct :
    CreatesLimit (Discrete.functor F) (ObjectProperty.ι Truncated.Quasicategory₂) :=
  createsLimitFullSubcategoryInclusion' _
    ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete F _) _).symm (productIsProduct _))
      (quasicategory₂_pi (F := fun j ↦ (F j).obj))

instance hasProduct : HasProduct F :=
  hasLimit_of_created _ (ObjectProperty.ι Quasicategory₂)

end

variable {J : Type v} [Small.{u} J]

noncomputable instance inclusionCreatesProducts :
    CreatesLimitsOfShape (Discrete J) (ObjectProperty.ι Quasicategory₂.{u}) := by
  have : CreatesLimitsOfShape (Discrete (Shrink.{u} J)) (ObjectProperty.ι Quasicategory₂) :=
    ⟨createsLimitOfIsoDiagram _ Discrete.natIsoFunctor.symm⟩
  exact createsLimitsOfShapeOfEquiv (Discrete.equivalence (equivShrink.{u} J).symm) _

instance hasProductsOfShape : HasLimitsOfShape (Discrete J) QCat₂.{u} :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (ObjectProperty.ι Quasicategory₂)

instance hasFiniteProducts : HasFiniteProducts QCat₂.{u} :=
  hasFiniteProducts_of_hasProducts.{u} _

end SSet.QCat₂

namespace SSet.Quasicategory₂

open Truncated

section HomotopyCategoryProducts

variable {J : Type u} (F : J → Truncated.{u} 2) [∀ j, (F j).Quasicategory₂]

/-- The comparison with the category of families of objects and morphisms. -/
noncomputable def homotopyCategoryPi :
    HomotopyCategory₂ (∏ᶜ F) ⥤ ∀ j, HomotopyCategory₂ (F j) :=
  Functor.pi' (fun _ ↦ mapHomotopyCategory₂ (Pi.π F _))

variable {F} in
instance isIso_homotopyCategoryPi : (homotopyCategoryPi F).IsIso where
  faithful := by
    constructor
    intro _ _ f g h
    induction f, g using Quotient.inductionOn₂ with
    | h f g =>
      apply Quotient.sound
      apply (homotopicL_pi_iff _ _).mpr
      intro _
      exact Quotient.exact (congrFun h _)
  full := by
    constructor
    intro _ _ f
    refine ⟨HomotopyCategory₂.homMk (Edge.pi (fun j ↦ (f j).out)), ?_⟩
    funext j
    refine (mapHomotopyCategory₂_homMk (Pi.π F j) _).trans ?_
    rw [Edge.pi_map_π (fun j ↦ (f j).out) j]
    exact Quotient.out_eq (f j)
  bijective_obj := by
    constructor
    · rintro ⟨_⟩ ⟨_⟩ h
      congr 1
      apply Concrete.Pi.map_ext F ((evaluation _ _).obj _)
      intro _
      exact congrArg HomotopyCategory₂.pt (congrFun h _)
    · intro x
      refine ⟨⟨(piObjIso F _).inv ((Types.productIso _).inv (fun j ↦ (x j).pt))⟩, ?_⟩
      funext j
      apply congrArg HomotopyCategory₂.mk
      rw [pi_π_app_piObjIso_inv]

/-- The homotopy category of a product is the product category. -/
@[blueprint "lem:2-truncated-qcat-htpy-products"
  (title := "homotopy categories of products")
  (statement := /-- Let $(A_j)_{j\in J}$ be a small family of 2-truncated quasi-categories.
    The product projections induce an isomorphism
    \[
      \ho{\left(\prod_{j\in J} A_j\right)} \xrightarrow{\cong} \prod_{j\in J}\ho{A_j}.
    \] -/)
  (proof := /-- Vertices of a product are tuples of vertices, so the comparison is bijective
    on objects. It is full because a choice of representative 1-simplex in each factor gives
    a 1-simplex in the product, and faithful by Lemma \ref{lem:product-1-simplex-htpy}. -/)
  (latexEnv := "lemma")]
noncomputable def homotopyCategoryPiIso :
    Cat.of (HomotopyCategory₂ (∏ᶜ F)) ≅ Cat.of (∀ j, HomotopyCategory₂ (F j)) where
  hom := (homotopyCategoryPi _).toCatHom
  inv := (homotopyCategoryPi _).strictInv.toCatHom
  hom_inv_id := Cat.Hom.ext (homotopyCategoryPi _).asIsomorphism.unit_eq.symm
  inv_hom_id := Cat.Hom.ext (homotopyCategoryPi _).asIsomorphism.counit_eq

/-- The comparison to the categorical product of the homotopy categories. -/
noncomputable def homotopyCategoryProductComparison :
    Cat.of (HomotopyCategory₂ (∏ᶜ F)) ⟶ ∏ᶜ (fun j ↦ Cat.of (HomotopyCategory₂ (F j))) :=
  Pi.lift (fun _ ↦ (mapHomotopyCategory₂ (Pi.π _ _)).toCatHom)

variable {F} in
instance isIso_homotopyCategoryProductComparison :
    IsIso (homotopyCategoryProductComparison F) := by
  apply (Fan.nonempty_isLimit_iff_isIso_piLift
    (Fan.mk _ (fun j ↦ (mapHomotopyCategory₂ _).toCatHom))).mp
  let hc : IsLimit (Fan.mk (Cat.of (∀ j, HomotopyCategory₂ (F j)))
      (fun j ↦ (CategoryTheory.Pi.eval _ j).toCatHom)) := by
    refine Fan.IsLimit.mk _ ?_ ?_ ?_
    · intro s
      exact (Functor.pi' (fun j ↦ (s.proj j).toFunctor)).toCatHom
    · intro _ _
      rfl
    · intro _ _ h
      apply Cat.Hom.ext
      apply Functor.pi_ext
      intro _
      exact congrArg Cat.Hom.toFunctor (h _)
  exact hc.nonempty_isLimit_iff_isIso_lift.mpr (homotopyCategoryPiIso F).isIso_hom

end HomotopyCategoryProducts

section PreservesProducts

instance homotopyCategory₂Functor_preservesProduct {J : Type u}
    {F : J → QCat₂.{u}} :
    PreservesLimit (Discrete.functor F) homotopyCategory₂Functor := by
  let c : Fan F := Fan.mk ⟨∏ᶜ (fun j ↦ (F j).obj), inferInstance⟩
    (fun j ↦ ObjectProperty.homMk (Pi.π (fun j ↦ (F j).obj) j))
  have hc : IsLimit c := by
    apply isLimitOfReflects (ObjectProperty.ι Quasicategory₂)
    apply (isLimitMapConeFanMkEquiv _ _ _).symm _
    exact productIsProduct _
  apply preservesLimit_of_preserves_limit_cone hc
  apply (isLimitMapConeFanMkEquiv homotopyCategory₂Functor F _).symm _
  exact Fan.isLimitOfIsIsoPiLift _ (hc := isIso_homotopyCategoryProductComparison)

variable {J : Type v} [Small.{u} J]

instance homotopyCategory₂Functor_preservesProducts :
    PreservesLimitsOfShape (Discrete J) homotopyCategory₂Functor.{u} := by
  have : PreservesLimitsOfShape (Discrete (Shrink.{u} J)) homotopyCategory₂Functor.{u} :=
    ⟨preservesLimit_of_iso_diagram homotopyCategory₂Functor Discrete.natIsoFunctor.symm⟩
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink.{u} J).symm) _

instance homotopyCategory₂Functor_preservesFiniteProducts :
    PreservesFiniteProducts homotopyCategory₂Functor.{u} where
  preserves _ := inferInstance

end PreservesProducts

end SSet.Quasicategory₂

namespace SSet.Truncated

/-- The ordinary homotopy category functor preserves products of 2-truncated quasicategories. -/
instance hoFunctor₂_preservesProduct {J : Type v} [Small.{u} J] {F : J → Truncated.{u} 2}
    [∀ j, (F j).Quasicategory₂] : PreservesLimit (Discrete.functor F) hoFunctor₂ := by
  have : PreservesLimit (Discrete.functor (fun j ↦ ⟨F j, inferInstance⟩))
      (ObjectProperty.ι Quasicategory₂ ⋙ hoFunctor₂) :=
    preservesLimit_of_natIso _ SSet.Quasicategory₂.homotopyCategory₂FunctorIso.symm
  exact preservesLimit_of_iso_diagram hoFunctor₂
    (Discrete.compNatIsoDiscrete (fun j ↦ ⟨F j, inferInstance⟩) (ObjectProperty.ι Quasicategory₂))

end SSet.Truncated

namespace SSet

section PreservesProducts

variable {J : Type v} [Small.{u} J] {F : J → SSet.{u}} [∀ j, Quasicategory (F j)]

/-- The homotopy category functor preserves any small product of quasicategories. -/
@[blueprint "lem:ho-preserves-small-products"
  (title := "preservation of small products")
  (uses := ["defn:homotopy-cat"])
  (statement := /-- The functor $\ho \colon \qCat \to \Cat$ preserves small products. -/)
  (proof := /-- By Lemma \ref{lem:htpy-cat-of-qcat}, we may compute homotopy categories using
    the 2-truncations. Since truncation preserves products, the result follows from
    Lemma \ref{lem:2-truncated-qcat-htpy-products}. -/)
  (latexEnv := "lemma")]
instance hoFunctor_preservesProduct : PreservesLimit (Discrete.functor F) hoFunctor := by
  change PreservesLimit _ (truncation 2 ⋙ Truncated.hoFunctor₂)
  have : PreservesLimit (Discrete.functor F ⋙ truncation 2) Truncated.hoFunctor₂ :=
    (preservesLimit_iff_of_iso_diagram _ (Discrete.compNatIsoDiscrete _ _)).mpr
      (Truncated.hoFunctor₂_preservesProduct (F := fun j ↦ (truncation 2).obj (F j)))
  dsimp only [truncation, SimplicialObject.truncation] at this ⊢
  infer_instance

end PreservesProducts

/-- Products of quasicategories are quasicategories, by coordinatewise horn filling. -/
@[blueprint "lem:qcat-products" (hasProof := true) (latexEnv := "lemma")]
instance quasicategory_pi {J : Type v} {F : J → SSet.{u}} [HasProduct F]
    [∀ j, Quasicategory (F j)] : Quasicategory (∏ᶜ F) where
  hornFilling' _ _ f h₀ hₙ := by
    choose g hg using fun j ↦ Quasicategory.hornFilling h₀ hₙ (f ≫ Limits.Pi.π F j)
    refine ⟨Limits.Pi.lift g, ?_⟩
    apply Limits.Pi.hom_ext
    intro
    simpa only [Category.assoc, Pi.lift_π] using hg _

namespace QCat

variable {J : Type v} {F : J → QCat.{u}}

section

variable [HasProduct (fun j ↦ (F j).obj)]

/-- The inclusion creates products of quasicategories. -/
noncomputable instance inclusionCreatesProduct :
    CreatesLimit (Discrete.functor F) (ObjectProperty.ι Quasicategory) := by
  have : ∀ j, Quasicategory (F j).obj := fun j ↦ (F j).property
  exact createsLimitFullSubcategoryInclusion' _
    ((IsLimit.postcomposeInvEquiv
      (Discrete.compNatIsoDiscrete F (ObjectProperty.ι Quasicategory)) _).symm
        (productIsProduct (fun j ↦ (F j).obj))) (quasicategory_pi (F := fun j ↦ (F j).obj))

instance hasProduct : HasProduct F := by
  have : HasLimit (Discrete.functor F ⋙ ObjectProperty.ι Quasicategory) :=
    (hasLimit_iff_of_iso (Discrete.compNatIsoDiscrete F (ObjectProperty.ι Quasicategory))).mpr
      ‹HasProduct (fun j ↦ (F j).obj)›
  exact hasLimit_of_created (Discrete.functor F) (ObjectProperty.ι Quasicategory)

end

variable [Small.{u} J]

instance hasProductsOfShape : HasLimitsOfShape (Discrete J) QCat.{u} where
  has_limit D := hasLimit_of_iso (Discrete.natIsoFunctor (F := D)).symm

instance hasFiniteProducts : HasFiniteProducts QCat.{u} :=
  hasFiniteProducts_of_hasProducts.{u} _

instance inclusion_preservesProducts :
    PreservesLimitsOfShape (Discrete J) (ObjectProperty.ι Quasicategory.{u}) where
  preservesLimit := preservesLimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

instance hoFunctor_preservesProduct :
    PreservesLimit (Discrete.functor F) (ObjectProperty.ι Quasicategory ⋙ hoFunctor) := by
  have : ∀ j, Quasicategory (F j).obj := fun j ↦ (F j).property
  have : PreservesLimit (Discrete.functor F ⋙ ObjectProperty.ι Quasicategory) hoFunctor :=
    (preservesLimit_iff_of_iso_diagram _ (Discrete.compNatIsoDiscrete _ _)).mpr
      (SSet.hoFunctor_preservesProduct (F := fun j ↦ (F j).obj))
  infer_instance

/-- The homotopy category functor restricted to quasicategories preserves small products. -/
@[blueprint "lem:ho-preserves-small-products" (hasProof := true) (latexEnv := "lemma")]
instance hoFunctor_preservesProducts :
    PreservesLimitsOfShape (Discrete J) (ObjectProperty.ι Quasicategory.{u} ⋙ hoFunctor) where
  preservesLimit := preservesLimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

instance hoFunctor_preservesFiniteProducts :
    PreservesFiniteProducts (ObjectProperty.ι Quasicategory.{u} ⋙ hoFunctor) where
  preserves _ := inferInstance

end QCat

end SSet
