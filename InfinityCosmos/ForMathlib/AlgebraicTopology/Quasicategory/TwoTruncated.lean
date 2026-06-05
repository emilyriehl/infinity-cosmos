/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy
-/

import Architect
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.CategoryTheory.Category.ReflQuiv
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Basic


open Simplicial SimplexCategory CategoryTheory SimplexCategory.Truncated
  SimplexCategory.Truncated.Hom SimplicialObject SimplicialObject.Truncated

namespace SSet
namespace Truncated

namespace Edge

abbrev edgeMap {S : SSet} {y₀ y₁ : ((truncation 2).obj S) _⦋0⦌₂} (e : Edge y₀ y₁) : Δ[1] ⟶ S :=
  yonedaEquiv.symm e.edge

end Edge

open Edge
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
    rw [← f₃.d₁, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₃ f₃ f₀ f₂ comm), this]
  d₀ := by
    rw [← f₀.d₀, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₀ f₃ f₀ f₂ comm)]
    rfl
  d₁ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.reduceSucc, Fin.castSucc_one] at this
    rw [← f₂.d₁, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
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
    rw [← f₃.d₂, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₃ f₃ f₀ f₁ comm), this]
  d₀ := by
    have := δ_comp_δ (n := 1) (i := 0) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two, Fin.castSucc_zero] at this
    rw [← f₀.d₁, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₀ f₃ f₀ f₁ comm), this]
  d₁ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two, Fin.castSucc_one] at this
    rw [← f₁.d₁, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
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
open Edge

variable {A : Truncated 2}

end CompStruct

end Edge

section homotopy_def

open Edge

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

namespace Quasicategory₂
open Truncated Edge.CompStruct

section homotopy_relation
open Edge

variable {A : Truncated 2} [Quasicategory₂ A]

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
  (latexEnv := "lemma"), implicit_reducible]
def HomotopicL.refl {x y : A _⦋0⦌₂} {f : Truncated.Edge x y} :
    HomotopicL f f := ⟨compId f⟩

/--
Left homotopy relation is symmetric
-/
@[blueprint "lem:2-truncated-qcat-htpy", implicit_reducible]
def HomotopicL.symm {x y : A _⦋0⦌₂} {f g : Truncated.Edge x y} (hfg : HomotopicL f g) :
    HomotopicL g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idCompId y) (compId f)

/--
Left homotopy relation is transitive
-/
@[blueprint "lem:2-truncated-qcat-htpy", implicit_reducible]
def HomotopicL.trans {x y : A _⦋0⦌₂} {f g h : Truncated.Edge x y} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) :
    HomotopicL f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idCompId y) hgh

/--
Right homotopy relation is reflexive
-/
@[blueprint "lem:2-truncated-qcat-htpy", implicit_reducible]
def HomotopicR.refl  {x y : A _⦋0⦌₂} {f : Truncated.Edge x y} : HomotopicR f f := ⟨idComp f⟩

/--
Right homotopy relation is symmetric
-/
@[blueprint "lem:2-truncated-qcat-htpy", implicit_reducible]
def HomotopicR.symm {x y : A _⦋0⦌₂} {f g : Truncated.Edge x y} (hfg : HomotopicR f g) :
    HomotopicR g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idCompId x) hfg (idComp f)

/--
Right homotopy relation is transitive
-/
@[blueprint "lem:2-truncated-qcat-htpy", implicit_reducible]
def HomotopicR.trans {x y : A _⦋0⦌₂} {f g h : Truncated.Edge x y} (hfg : HomotopicR f g)
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

universe u
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

set_option backward.isDefEq.respectTransparency false in
lemma qFunctor_map_toPath (x y : FreeRefl.{u} (OneTruncation₂ A))
    (f : Truncated.Edge x.as y.as) :
    quotientFunctor₂.map.{u} (Quot.mk _ (Quiver.Hom.toPath f)) = quotientReflPrefunctor₂.map f := by
  dsimp [quotientFunctor₂, Adjunction.homEquiv, FreeRefl.lift]
  dsimp [quotientReflPrefunctor₂, FreeRefl.homMk,
    FreeRefl.quotientFunctor, Quotient.functor, ReflQuiv.adj, ReflQuiv.adj.homEquiv,
    FreeRefl.lift, Paths.lift, CategoryTheory.Quotient.lift, Cat.Hom.equivFunctor]
  rw [Quot.liftOn_mk]
  change 𝟙 _ ≫ _ = _
  simp

lemma qFunctor_map_path {x y : OneTruncation₂.{u} A} (p : Quiver.Path x y) :
    quotientFunctor₂.{u}.map (Quot.mk _ p) = (ReflQuiv.adj.counit.app (Cat.of (HomotopyCategory₂.{u} A))).toFunctor.map
      (Quot.mk _ (quotientReflPrefunctor₂.{u}.mapPath p)) :=
  sorry

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
  sorry

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
  have key : FreeRefl.homMk (edgeToHom f) ≫ FreeRefl.homMk (edgeToHom (Truncated.Edge.id x₁)) =
      Quot.mk _ ((edgeToHom f).toPath.comp (edgeToHom (Truncated.Edge.id x₁)).toPath) := by
    rw [Quiver.Path.comp_toPath_eq_cons]; rfl
  have e3 : FreeRefl.homMk (edgeToHom (Truncated.Edge.id x₁)) = 𝟙 _ :=
    FreeRefl.homMk_id (V := OneTruncation₂ A) x₁
  rw [show edgeToFreeHom f = FreeRefl.homMk (edgeToHom f) from rfl]
  conv_lhs => rw [← Category.comp_id (FreeRefl.homMk (edgeToHom f)), ← e3]
  exact key

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
    sorry
    -- show ⟦Edge.id x⟧.liftOn _ _ = 𝟙rq (F.obj { as := x})
    -- have : 𝟙rq (F.obj { as := x}) = F.map (𝟙 { as := x }) := (F.map_id { as := x }).symm
    -- rw [Quotient.liftOn_mk, this]
    -- congr 1
    -- dsimp [edgeToFreeHom, CategoryStruct.id]
    -- apply Quot.sound
    -- apply Quotient.CompClosure.of
    -- constructor

theorem lift_unique_rq₂ {C} [ReflQuiver.{u + 1, u} C] (F₁ F₂ : (HomotopyCategory₂.{u} A) ⥤rq C)
    (h : quotientReflPrefunctor₂ ⋙rq F₁ = quotientReflPrefunctor₂ ⋙rq F₂) : F₁ = F₂ := by
  sorry
  -- apply ReflPrefunctor.ext'
  -- . intro x₀ x₁
  --   apply Quotient.ind
  --   intro f
  --   have q_is_quotient : quotientReflPrefunctor₂.map (edgeToHom f) =
  --     Quotient.mk (instSetoidEdge x₀ x₁) f := rfl
  --   rw [← q_is_quotient, ← ReflPrefunctor.comp_map, ← ReflPrefunctor.comp_map,
  --     ReflPrefunctor.congr_hom h.symm]
  -- . intro x
  --   have : (quotientReflPrefunctor₂.{u} ⋙rq F₁).obj x = (quotientReflPrefunctor₂.{u} ⋙rq F₂).obj x :=
  --      congrFun (congrArg Prefunctor.obj (congrArg ReflPrefunctor.toPrefunctor h)) x
  --   rw [ReflPrefunctor.comp_obj, ReflPrefunctor.comp_obj] at this
  --   dsimp [quotientReflPrefunctor₂] at this
  --   exact this

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
      let h' : x₀ ⟶ x₂ := ⟦p.fst⟧
      sorry
      -- have : ⟦f⟧ ≫ ⟦g⟧ = h' := by
      --   dsimp only [CategoryStruct.comp, composeHEdges]
      --   rw [Quotient.lift₂_mk]
      --   rfl
      -- rw [this]
      -- dsimp only [h', Quotient.lift_mk]
      -- apply h
      -- apply HoRel₂.mk' (φ := p.snd.simplex) <;> symm
      -- . exact p.snd.d₂
      -- . exact p.snd.d₀
      -- . exact p.snd.d₁
  }

lemma is_lift₂ {C : Type*} [Category* C] (F : FreeRefl.{u} (OneTruncation₂.{u} A) ⥤ C)
    (h : ∀ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : x ⟶ y),
      (r : OneTruncation₂.HoRel₂ _ f g) → F.map f = F.map g) :
    quotientFunctor₂.{u} ⋙ lift₂ F h = F := by
  apply FreeRefl.lift_unique'
  apply Paths.ext_functor
  intro x y f
  all_goals sorry
  -- simp only [FreeRefl.quotientFunctor, Quotient.functor, lift₂, liftRq₂, Functor.comp_obj,
  --   Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
  -- . rw [qFunctor_map_toPath]; rfl
  -- . rfl

/--
  Lifts to the homotopy category are unique.
-/
theorem HomotopyCategory₂.lift_unique' {C : Type u} [Category.{u} C]
    (F₁ F₂ : HomotopyCategory₂.{u} A ⥤ C)
    (h : quotientFunctor₂.{u} ⋙ F₁ = quotientFunctor₂.{u} ⋙ F₂) : F₁ = F₂ := by
  have forget_faithful' {C D : Type u} [Category.{u} C] [Category.{u} D] (F G : C ⥤ D)
      (hyp : F.toReflPrefunctor = G.toReflPrefunctor) : F = G := by
    cases F; cases G; cases hyp; rfl
  apply forget_faithful'
  sorry
  -- apply lift_unique_rq₂
  -- let η := ReflQuiv.adj.unit.app (OneTruncation₂ A)
  -- rw [unit_app_quotientFunctor.{u}, ReflPrefunctor.comp_assoc,
  --   ← Functor.toReflPrefunctor.map_comp (C := FreeRefl (OneTruncation₂ A)), h]
  -- rfl

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
def isoHomotopyCategories : (Cat.of (HomotopyCategory.{u} A)) ≅ (Cat.of (HomotopyCategory₂.{u} A)) where
  hom := (CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂).toCatHom
  inv := lift₂ (HomotopyCategory.quotientFunctor.{u} A) (by
    intro _ _ _ _ h
    sorry
    -- simp only [Cat.of_α, HomotopyCategory.quotientFunctor, Quotient.functor]
    -- apply Quot.sound
    -- apply Quotient.CompClosure.of
    -- exact h
    ) |>.toCatHom
  hom_inv_id := by
    sorry
    -- apply HomotopyCategory.lift_unique'
    -- dsimp only [Cat.of_α, HomotopyCategory.quotientFunctor, CategoryStruct.comp]
    -- rw [← Functor.assoc, Quotient.lift_spec, is_lift₂]
    -- rfl
  inv_hom_id := by
    sorry
    -- apply HomotopyCategory₂.lift_unique'
    -- dsimp only [Cat.of_α, CategoryStruct.comp, HomotopyCategory.quotientFunctor]
    -- rw [← Functor.assoc, is_lift₂, Quotient.lift_spec]
    -- rfl

end isomorphism_of_htpy_categories

end Quasicategory₂

end SSet
