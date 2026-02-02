/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy
-/
import Architect
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Category.ReflQuiv

open Simplicial SimplexCategory CategoryTheory SimplexCategory.Truncated Truncated.Hom
  SimplicialObject SimplicialObject.Truncated

namespace SSet
namespace Truncated

section comp_struct

/--
`Edge x₀ x₁` is a wrapper around a 1-simplex in a 2-truncated simplicial set
with source `x₀` and target `x₁`.
-/
structure Edge {X : Truncated 2} (x₀ : X _⦋0⦌₂) (x₁ : X _⦋0⦌₂) where
  simplex : X _⦋1⦌₂
  h₀ : X.map (tr (δ 1)).op simplex = x₀
  h₁ : X.map (tr (δ 0)).op simplex = x₁

abbrev edgeMap {S : SSet} {y₀ y₁ : ((truncation 2).obj S) _⦋0⦌₂} (e : Edge y₀ y₁) : Δ[1] ⟶ S :=
  yonedaEquiv.symm e.simplex

/--
`CompStruct e₀₁ e₁₂ e₀₂` is a wrapper around a 2-simplex in a 2-truncated simplicial set
with edges `e₀₁`, `e₁₂`, `e₀₂` in the obvious configuration.
-/
structure CompStruct {X : Truncated 2} {x₀ x₁ x₂ : X _⦋0⦌₂}
    (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) where
  simplex : X _⦋2⦌₂
  h₀₁ : X.map (tr (δ 2)).op simplex = e₀₁.simplex
  h₁₂ : X.map (tr (δ 0)).op simplex = e₁₂.simplex
  h₀₂ : X.map (tr (δ 1)).op simplex = e₀₂.simplex
end comp_struct

/--
A 2-truncated quasicategory is a 2-truncated simplicial set with 3 properties:
  (2, 1)-filling: any path of length 2 in may be filled to a 2-simplex whose
    spine equals the given path.
  (3, 1)-filling: given any path f of length 3, 2-simplices σ₃ and σ₀ filling the restricted paths
    f₀₁₂ and f₁₂₃ respectively, and a 2-simplex σ₂ filling the path formed by f₀₁ and the diagonal
    of σ₀, there is a 2-simplex σ₁ filling the path formed by the diagonal of σ₃ and f₂₃ and whose
    diagonal is the diagonal of σ₂.
  (3, 2)-filling: given any path f of length 3, 2-simplices σ₃ and σ₀ filling the restricted paths
    f₀₁₂ and f₁₂₃ respectively, and a 2-simplex σ₁ filling the path formed by f₂₃ and the diagonal
    of σ₃, there is a 2-simplex σ₂ filling the path formed by f₀₁ and the diagonal of σ₀ and whose
    diagonal is the diagonal of σ₁.
-/
@[blueprint
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
class Quasicategory₂ (X : Truncated 2) where
  fill21 {x₀ x₁ x₂ : X _⦋0⦌₂}
      (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
      Nonempty (Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂)
  fill31 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₂ : CompStruct e₀₁ e₁₃ e₀₃) :
      Nonempty (CompStruct e₀₂ e₂₃ e₀₃)
  fill32 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₁ : CompStruct e₀₂ e₂₃ e₀₃) :
      Nonempty (CompStruct e₀₁ e₁₃ e₀₃)

end Truncated

namespace horn₂₁
open Truncated (Edge edgeMap CompStruct truncEquiv trunc_map trunc_map')

variable {S : SSet} {x₀ x₁ x₂ : ((truncation 2).obj S) _⦋0⦌₂}
  (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)

lemma path_edges_comm : pt₁ ≫ edgeMap e₁₂ = pt₀ ≫ edgeMap e₀₁ := by
  rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
  congr 1
  apply Eq.trans
  . exact e₁₂.h₀
  . symm; exact e₀₁.h₁

/--
Given the data of two consecutive edges `e₀₁` and `e₁₂`, construct a map
`Λ[2, 1].toSSet ⟶ S` which restricts to maps `Δ[1] ⟶ S` corresponding
to the two edges (this is made precise in the lemmas `horn_from_edges_restr₀` and
`horn_from_edges_restr₁`).
-/
def fromEdges : Λ[2, 1].toSSet ⟶ S :=
  Limits.PushoutCocone.IsColimit.desc pushoutIsPushout
    (edgeMap e₁₂) (edgeMap e₀₁) (path_edges_comm e₀₁ e₁₂)

/-- See `horn_from_edges` for details. -/
lemma horn_from_edges_restr₀ : ι₀ ≫ (fromEdges e₀₁ e₁₂) = yonedaEquiv.symm e₁₂.simplex :=
  Limits.PushoutCocone.IsColimit.inl_desc pushoutIsPushout
    (edgeMap e₁₂) (edgeMap e₀₁) (path_edges_comm e₀₁ e₁₂)

/-- See `horn_from_edges` for details. -/
lemma horn_from_edges_restr₁ : ι₂ ≫ (fromEdges e₀₁ e₁₂) = yonedaEquiv.symm e₀₁.simplex :=
  Limits.PushoutCocone.IsColimit.inr_desc pushoutIsPushout
    (edgeMap e₁₂) (edgeMap e₀₁) (path_edges_comm e₀₁ e₁₂)

/--
Given a map `Δ[2] ⟶ S` extending the horn given by `horn_from_edges`, construct
and edge `e₀₂` such that `e₀₁`, `e₁₂`, `e₀₂` bound a 2-simplex of `S` (this is witnessed
by `CompStruct e₀₁ e₁₂ e₀₂`).
-/
def fromHornExtension
    (g : Δ[2] ⟶ S)
    (comm : fromEdges e₀₁ e₁₂ = Λ[2, 1].ι ≫ g) :
    Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂ := by
  constructor; swap
  exact {
    simplex := (truncEquiv 2) <| yonedaEquiv <| stdSimplex.δ 1 ≫ g
    h₀ := by
      rw [← e₀₁.h₀, trunc_map, trunc_map']
      have : yonedaEquiv.symm (e₀₁.simplex) = stdSimplex.δ 2 ≫ g := by
        rw [← horn_from_edges_restr₁ e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      rw [push_yonedaEquiv this]
      have : δ 1 ≫ δ 2 = δ 1 ≫ @δ 1 1 :=
        SimplexCategory.δ_comp_δ (n := 0) (i := 1) (j := 1) (le_refl 1)
      rw [this]
      apply push_yonedaEquiv
      rw [Equiv.symm_apply_apply]; rfl
    h₁ := by
      rw [← e₁₂.h₁, trunc_map, trunc_map']
      have : yonedaEquiv.symm (e₁₂.simplex) = stdSimplex.δ 0 ≫ g := by
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
    h₀₁ := by
      rw [trunc_map]
      have : yonedaEquiv.symm (e₀₁.simplex) = stdSimplex.δ 2 ≫ g := by
        rw [← horn_from_edges_restr₁ e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      rw [← push_yonedaEquiv' this]
    h₁₂ := by
      rw [trunc_map]
      have : yonedaEquiv.symm (e₁₂.simplex) = stdSimplex.δ 0 ≫ g := by
        rw [← horn_from_edges_restr₀ e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₀]
      rw [← push_yonedaEquiv' this]
    h₀₂ := by
      rw [trunc_map]
      dsimp only [len_mk, id_eq, Nat.reduceAdd, Fin.isValue, eq_mpr_eq_cast, cast_eq, op_comp,
        Fin.succ_zero_eq_one, Fin.castSucc_zero]
      rw [← map_yonedaEquiv']; rfl
  }

end horn₂₁

namespace horn₃₁
open Truncated (CompStruct Edge truncEquiv trunc_map trunc_map')

variable {S : SSet}
variable
    {x₀ x₁ x₂ x₃ : ((truncation 2).obj S) _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
    (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
    (f₂ : CompStruct e₀₁ e₁₃ e₀₃)

include S x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃ f₃ f₀ f₂

/--
Choose the i-th face from the given faces, where i is represented by `a : horn₃₁.R`,
i.e. `a` is 0, 2 or 3
-/
def chooseFace (a : R) : (Δ[2] ⟶ S) := match a with
  | R.f₀ => yonedaEquiv.symm f₀.simplex
  | R.f₂ => yonedaEquiv.symm f₂.simplex
  | R.f₃ => yonedaEquiv.symm f₃.simplex

def chooseFace' (a : R) : S _⦋2⦌ := match a with
  | R.f₀ => f₀.simplex
  | R.f₂ => f₂.simplex
  | R.f₃ => f₃.simplex

-- The multicofork `⨿ Δ[1] ⇉ ⨿ Δ[2] ⟶ S` defined by sending `Δ[2]`s to
-- each of the three faces `f₃`, `f₀`, `f₂`.
def multicoforkFromFaces : Limits.Multicofork multispanIndex :=
  Limits.Multicofork.ofπ multispanIndex S
    (chooseFace f₃ f₀ f₂)
    (by
      rintro ⟨⟨⟨i, i_ne_1⟩, ⟨j, j_ne_1⟩⟩, i_lt_j⟩
      all_goals
        dsimp [J, multispanIndex, chooseFace, CosimplicialObject.δ]
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      -- rw doesn't work because the statement is about `SSet`, not `Truncated 2`
      . apply Eq.trans
        exact f₂.h₀₁
        symm; exact f₃.h₀₁
      . apply Eq.trans
        exact f₃.h₁₂
        symm; exact f₀.h₀₁
      . apply Eq.trans
        exact f₀.h₀₂
        symm; exact f₂.h₁₂)

/--
Use the fact that `Λ[3, 1]` is the coequalizer of `multicoforkFromFaces` allows the
construction of a map `Λ[3, 1].toSSet ⟶ S`.
-/
def fromFaces : Λ[3, 1].toSSet ⟶ S := Limits.IsColimit.desc horn₃₁.isMulticoeq
  (multicoforkFromFaces f₃ f₀ f₂)

/-
A group of lemmas stating that the faces of the simplex `Δ[3] ⟶ S` extending the horn
`fromFaces f₃ f₀ f₂ : Λ[3, 1] ⟶ S` are as expected.
-/
lemma horn_extension_face₀ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₀.simplex = stdSimplex.δ 0 ≫ g := by
  have : ι₀ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₀.simplex :=
    isMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₂) (.right R.f₀)
  rw [← this, comm, ← Category.assoc, incl₀]

lemma horn_extension_face₂ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₂.simplex = stdSimplex.δ 2 ≫ g := by
  have : ι₂ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₂.simplex :=
    isMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₂) (.right R.f₂)
  rw [← this, comm, ← Category.assoc, incl₂]

lemma horn_extension_face₃ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : ι₃ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₃.simplex :=
    isMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₂) (.right R.f₃)
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
  h₀₁ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 2) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.reduceSucc, Fin.castSucc_one] at this
    rw [← f₃.h₀₂, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₃ f₃ f₀ f₂ comm), this]
  h₁₂ := by
    rw [← f₀.h₁₂, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₀ f₃ f₀ f₂ comm)]
    rfl
  h₀₂ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.reduceSucc, Fin.castSucc_one] at this
    rw [← f₂.h₀₂, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₂ f₃ f₀ f₂ comm), this]

end horn₃₁

namespace horn₃₂
open Truncated (CompStruct Edge truncEquiv trunc_map trunc_map')

variable {S : SSet}
variable
    {x₀ x₁ x₂ x₃ : ((truncation 2).obj S) _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
    (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
    (f₁ : CompStruct e₀₂ e₂₃ e₀₃)

include S x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃ f₃ f₀ f₁

/--
Choose the i-th face from the given faces, where i is represented by `a : horn₃₂.R`,
i.e. `a` is 0, 1 or 3
-/
def chooseFace (a : R) : (Δ[2] ⟶ S) := match a with
  | R.f₀ => yonedaEquiv.symm f₀.simplex
  | R.f₁ => yonedaEquiv.symm f₁.simplex
  | R.f₃ => yonedaEquiv.symm f₃.simplex

def chooseFace' (a : R) : S _⦋2⦌ := match a with
  | R.f₀ => f₀.simplex
  | R.f₁ => f₁.simplex
  | R.f₃ => f₃.simplex

-- The multicofork `⨿ Δ[1] ⇉ ⨿ Δ[2] ⟶ S` defined by sending `Δ[2]`s to
-- each of the three faces `f₃`, `f₀`, `f₁`.
def multicoforkFromFaces : Limits.Multicofork multispanIndex :=
  Limits.Multicofork.ofπ multispanIndex S
    (chooseFace f₃ f₀ f₁)
    (by
      rintro ⟨⟨⟨i, i_ne_1⟩, ⟨j, j_ne_1⟩⟩, i_lt_j⟩
      all_goals
        dsimp [J, multispanIndex, chooseFace, CosimplicialObject.δ]
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      -- rw doesn't work because the statement is about `SSet`, not `Truncated 2`
      . apply Eq.trans
        exact f₁.h₀₁
        symm; exact f₃.h₀₂
      . apply Eq.trans
        exact f₃.h₁₂
        symm; exact f₀.h₀₁
      . apply Eq.trans
        exact f₀.h₁₂
        symm; exact f₁.h₁₂)

/--
Use the fact that `Λ[3, 2]` is the coequalizer of `multicoforkFromFaces` allows the
construction of a map `Λ[3, 2].toSSet ⟶ S`.
-/
def fromFaces : Λ[3, 2].toSSet ⟶ S := Limits.IsColimit.desc horn₃₂.multicoforkIsMulticoeq
  (multicoforkFromFaces f₃ f₀ f₁)

/-
A group of lemmas stating that the faces of the simplex `Δ[3] ⟶ S` extending the horn
`fromFaces f₃ f₀ f₁ : Λ[3, 2] ⟶ S` are as expected.
-/
lemma horn_extension_face₀ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₀.simplex = stdSimplex.δ 0 ≫ g := by
  have : ι₀ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₀.simplex :=
    multicoforkIsMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₁) (.right R.f₀)
  rw [← this, comm, ← Category.assoc, incl₀]

lemma horn_extension_face₁ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₁.simplex = stdSimplex.δ 1 ≫ g := by
  have : ι₁ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₁.simplex :=
    multicoforkIsMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₁) (.right R.f₁)
  rw [← this, comm, ← Category.assoc, incl₁]

lemma horn_extension_face₃ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : ι₃ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₃.simplex :=
    multicoforkIsMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₁) (.right R.f₃)
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
  h₀₁ := by
    have := δ_comp_δ (n := 1) (i := 2) (j := 2) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.reduceSucc, Fin.reduceCastSucc] at this
    rw [← f₃.h₀₁, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₃ f₃ f₀ f₁ comm), this]
  h₁₂ := by
    have := δ_comp_δ (n := 1) (i := 0) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two, Fin.castSucc_zero] at this
    rw [← f₀.h₀₂, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
      push_yonedaEquiv (horn_extension_face₀ f₃ f₀ f₁ comm), this]
  h₀₂ := by
    have := δ_comp_δ (n := 1) (i := 1) (j := 1) (by simp)
    dsimp only [Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two, Fin.castSucc_one] at this
    rw [← f₁.h₀₂, trunc_map, trunc_map', ← FunctorToTypes.map_comp_apply, ← op_comp,
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

def id {A : Truncated 2} (x : A _⦋0⦌₂) : Edge x x where
  simplex := A.map (tr (σ 0)).op x
  h₀ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp,
      δ₂_one_comp_σ₂_zero, op_id, FunctorToTypes.map_id_apply]
  h₁ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp,
      δ₂_zero_comp_σ₂_zero, op_id, FunctorToTypes.map_id_apply]
end Edge

namespace CompStruct
open Edge

variable {A : Truncated 2}

def compId {x y : A _⦋0⦌₂} (e : Edge x y) : CompStruct e (id y) e where
  simplex := A.map (tr (σ 1)).op e.simplex
  h₀₁ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_one, op_id,
      FunctorToTypes.map_id_apply]
  h₁₂ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one, op_comp,
      FunctorToTypes.map_comp_apply, e.h₁]
    rfl
  h₀₂ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← Hom.tr_comp]
    dsimp only [tr]
    rw [δ_comp_σ_self' (by rfl)]
    apply FunctorToTypes.map_id_apply

def idComp {x y : A _⦋0⦌₂} (e : Edge x y) : CompStruct (id x) e e where
  simplex := A.map (tr (σ 0)).op e.simplex
  h₀₁ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero,
      op_comp, FunctorToTypes.map_comp_apply, e.h₀]
    rfl
  h₁₂ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero, op_id,
      FunctorToTypes.map_id_apply]
  h₀₂ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero, op_id,
      FunctorToTypes.map_id_apply]

def idCompId (x : A _⦋0⦌₂) := compId (id x)

end CompStruct

section homotopy_def

open Edge (id)
/--
Two edges `f` and `g` are left homotopic if there is a 2-simplex with
(0, 1)-edge `f`, (0, 2)-edge `g` and (1, 2)-edge `id`. We use `Nonempty` to
have a `Prop` valued `HomotopicL`.
-/
@[blueprint
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
abbrev HomotopicL {A : Truncated 2} {x y : A _⦋0⦌₂} (f g : Edge x y) := Nonempty (CompStruct f (id y) g)

/--
See `HomotopicL`.
-/
@[blueprint
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
abbrev HomotopicR {A : Truncated 2} {x y : A _⦋0⦌₂} (f g : Edge x y) := Nonempty (CompStruct (id x) f g)

end homotopy_def

end Truncated

namespace Quasicategory₂
open Truncated CompStruct

section homotopy_relation
open Edge (id)

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
  (latexEnv := "lemma")]
def HomotopicL.refl {x y : A _⦋0⦌₂} {f : Edge x y} : HomotopicL f f := ⟨compId f⟩

/--
Left homotopy relation is symmetric
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
def HomotopicL.symm {x y : A _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicL f g) :
    HomotopicL g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idCompId y) (compId f)

/--
Left homotopy relation is transitive
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
def HomotopicL.trans {x y : A _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) :
    HomotopicL f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idCompId y) hgh

/--
Right homotopy relation is reflexive
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
def HomotopicR.refl  {x y : A _⦋0⦌₂} {f : Edge x y} : HomotopicR f f := ⟨idComp f⟩

/--
Right homotopy relation is symmetric
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
def HomotopicR.symm {x y : A _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicR f g) :
    HomotopicR g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idCompId x) hfg (idComp f)

/--
Right homotopy relation is transitive
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
def HomotopicR.trans {x y : A _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicR f g)
    (hgh : HomotopicR g h) :
    HomotopicR f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idCompId x) hfg hgh

/--
The right and left homotopy relations coincide
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
theorem HomotopicL_iff_HomotopicR {x y : A _⦋0⦌₂} {f g : Edge x y} :
    HomotopicL f g ↔ HomotopicR f g := by
  constructor
  . rintro ⟨lhfg⟩
    exact Quasicategory₂.fill32 (idComp f) (compId f) lhfg
  . rintro ⟨rhfg⟩
    exact Quasicategory₂.fill31 (idComp f) (compId f) rhfg

end homotopy_relation

section basic_homotopies

variable {A : Truncated 2} [Quasicategory₂ A]
variable {x y z : A _⦋0⦌₂}

lemma comp_unique {f : Edge x y} {g : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (s' : CompStruct f g h') : HomotopicL h h' :=
  HomotopicL_iff_HomotopicR.mpr (Quasicategory₂.fill32 (idComp f) s s')

lemma comp_unique' {f : Edge x y} {g : Edge y z} {h h' : Edge x z}
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
lemma transport_edge₀ {f : Edge x y} {g g' : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL g g') : Nonempty (CompStruct f g' h) := by
  rcases htpy with ⟨htpy⟩
  exact Quasicategory₂.fill32 s htpy (compId h)

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
lemma transport_edge₁ {f : Edge x y} {g : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL h h') : Nonempty (CompStruct f g h') := by
  rcases (HomotopicL_iff_HomotopicR.mp htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 (idComp f) s htpy

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
lemma transport_edge₂ {f f' : Edge x y} {g : Edge y z} {h : Edge x z}
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
lemma transport_all_edges {f f' : Edge x y} {g g' : Edge y z}
    {h h' : Edge x z} (hf : HomotopicL f f') (hg : HomotopicL g g') (hh : HomotopicL h h')
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

variable {A : Truncated 2} [Quasicategory₂ A]

/--
  The homotopy category of a 2-truncated quasicategory `A` has as objects the 0-simplices of `A`
-/
def HomotopyCategory₂ (A : Truncated 2) := A _⦋0⦌₂

instance instSetoidEdge (x₀ x₁ : A _⦋0⦌₂) : Setoid (Edge x₀ x₁) where
  r := HomotopicL
  iseqv := ⟨fun _ ↦ HomotopicL.refl, HomotopicL.symm, HomotopicL.trans⟩

/--
  The morphisms between two vertices `x₀`, `x₁` in `HomotopyCategory₂ A` are homotopy classes
  of 1-simplices between `x₀` and `x₁`.
-/
def HEdge (x₀ x₁ : A _⦋0⦌₂) := Quotient (instSetoidEdge x₀ x₁)

/--
  Given two consecutive edges `f`, `g`  in a 2-truncated quasicategory, nonconstructively choose
  an edge that is the diagonal of a 2-simplex with spine given by `f` and `g`.
-/
noncomputable
def composeEdges {x₀ x₁ x₂ : A _⦋0⦌₂} (f : Edge x₀ x₁) (g : Edge x₁ x₂) : Edge x₀ x₂ :=
  (Nonempty.some (Quasicategory₂.fill21 f g)).1

noncomputable
def composeEdgesIsComposition {x₀ x₁ x₂ : A _⦋0⦌₂} (f : Edge x₀ x₁) (g : Edge x₁ x₂) :
    CompStruct f g (composeEdges f g) :=
  (Nonempty.some (Quasicategory₂.fill21 f g)).2

/--
  The edge `composeEdges f g` is the unique edge up to homotopy such that there is
  a 2-simplex with spine given by `f` and `g`.
-/
lemma composeEdges_unique {x₀ x₁ x₂ : A _⦋0⦌₂} {f : Edge x₀ x₁} {g : Edge x₁ x₂}
    {h : Edge x₀ x₂} (s : CompStruct f g h) : HomotopicL h (composeEdges f g) := by
  apply comp_unique' ⟨s⟩
  exact ⟨composeEdgesIsComposition f g⟩

/--
  The compositions of homotopic edges are homotopic
-/
lemma composeEdges_homotopic {x₀ x₁ x₂ : A _⦋0⦌₂} {f f' : Edge x₀ x₁} {g g' : Edge x₁ x₂}
    (hf : HomotopicL f f') (hg : HomotopicL g g') :
    HomotopicL (composeEdges f g) (composeEdges f' g') := by
  apply comp_unique' ⟨composeEdgesIsComposition f g⟩
  exact transport_all_edges (HomotopicL.symm hf) (HomotopicL.symm hg) (HomotopicL.refl)
    (composeEdgesIsComposition f' g')

/--
  Composition of morphisms in `HomotopyCategory₂ A` is given by lifting `composeEdges`.
-/
noncomputable
def composeHEdges {x₀ x₁ x₂ : A _⦋0⦌₂} (f : HEdge x₀ x₁) (g : HEdge x₁ x₂) : HEdge x₀ x₂ :=
  Quotient.lift₂ (fun f g ↦ ⟦composeEdges f g⟧) (fun _ _ _ _ hf hg ↦
    Quotient.sound (composeEdges_homotopic hf hg)
  ) f g

noncomputable
instance : CategoryStruct (HomotopyCategory₂ A) where
  Hom x₀ x₁ := HEdge x₀ x₁
  id x₀ := Quotient.mk' (Edge.id x₀)
  comp := composeHEdges

@[blueprint
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
noncomputable
instance instCategoryHomotopyCategory₂ : Category (HomotopyCategory₂ A) where
  id_comp f := by
    rcases f with ⟨f⟩
    apply Quotient.sound
    exact symm (composeEdges_unique (CompStruct.idComp f))
  comp_id f := by
    rcases f with ⟨f⟩
    apply Quotient.sound
    exact symm (composeEdges_unique (CompStruct.compId f))
  assoc f g h := by
    rcases f, g, h with ⟨⟨f⟩, ⟨g⟩, ⟨h⟩⟩
    apply Quotient.sound
    apply composeEdges_unique
    let fg := composeEdges f g
    exact Nonempty.some (Quasicategory₂.fill32
      (composeEdgesIsComposition f g)
      (composeEdgesIsComposition g h)
      (composeEdgesIsComposition fg h))

end homotopy_category

section isomorphism_of_htpy_categories
open Cat (FreeRefl)

universe u
variable {A : Truncated 2} [Quasicategory₂ A]

/--
  The reflexive prefunctor sending edges (in the 1-truncation) of `A` to their homotopy class.
-/
noncomputable
def quotientReflPrefunctor₂ : (OneTruncation₂ A) ⥤rq (HomotopyCategory₂ A) where
  obj := id
  map f := Quotient.mk' { simplex := f.edge, h₀ := f.src_eq, h₁ := f.tgt_eq }

/--
  By the adjunction `ReflQuiv.adj`, we obtain a functor from the free category on the reflexive
  quiver underlying `A` to the homotopy category corresponding to `quotientReflPrefunctor₂`.
-/
noncomputable
def quotientFunctor₂ : FreeRefl (OneTruncation₂ A) ⥤ HomotopyCategory₂ A :=
  (ReflQuiv.adj.homEquiv
    (ReflQuiv.of (OneTruncation₂ A))
    (Cat.of (HomotopyCategory₂ A))).invFun quotientReflPrefunctor₂

/--
  The adjoint relation between `quotientReflPrefunctor₂` and `quotientFunctor₂` expressed
  on the level of functors.
-/
lemma unit_app_quotientFunctor : quotientReflPrefunctor₂ =
    ReflQuiv.adj.unit.app (OneTruncation₂ A) ⋙rq quotientFunctor₂.{u}.toReflPrefunctor := by
  let η := ReflQuiv.adj.unit.app (OneTruncation₂ A)
  let q : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ A)) ⟶ Cat.of (HomotopyCategory₂ A) :=
    quotientFunctor₂.{u}
  let r : ReflQuiv.of (OneTruncation₂ A) ⟶ ReflQuiv.of (HomotopyCategory₂ A) :=
    quotientReflPrefunctor₂
  show r = η ≫ ReflQuiv.forget.map q
  have : η ≫ ReflQuiv.forget.map q = (ReflQuiv.adj.homEquiv _ _).toFun q := rfl
  rw [this]
  dsimp [r, q, quotientFunctor₂]
  symm
  apply Equiv.apply_symm_apply

lemma quotientFunctor_obj (x : FreeRefl (OneTruncation₂ A)) : quotientFunctor₂.obj x = x.as := rfl

lemma qFunctor_map_toPath (x y : FreeRefl.{u} (OneTruncation₂ A))
    (f : OneTruncation₂.Hom x.as y.as) :
    quotientFunctor₂.map.{u} (Quot.mk _ (Quiver.Hom.toPath f)) = quotientReflPrefunctor₂.map f := by
  dsimp [quotientFunctor₂, Adjunction.homEquiv]
  rw [Quot.liftOn_mk]
  simp [FreeRefl.quotientFunctor, Quotient.functor, ReflQuiv.adj]

lemma qFunctor_map_path {x y : OneTruncation₂.{u} A} (p : Quiver.Path x y) :
    quotientFunctor₂.{u}.map (Quot.mk _ p) = (ReflQuiv.adj.counit.app (HomotopyCategory₂.{u} A)).map
      (Quot.mk _ (quotientReflPrefunctor₂.mapPath p)) := rfl

/--
  `quotientFunctor₂` respects the hom relation `HoRel₂`.
-/
theorem qFunctor_respects_horel₂ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
    (f g : Quiver.Hom.{u + 1, u} x y) (r : HoRel₂ x y f g) :
    quotientFunctor₂.map.{u} f = quotientFunctor₂.map.{u} g := by
  rcases r with ⟨r⟩
  rw [qFunctor_map_toPath, qFunctor_map_path, Prefunctor.mapPath_comp,
    Prefunctor.mapPath_toPath, Prefunctor.mapPath_toPath]
  simp only [Cat.freeRefl_obj_α, ReflQuiv.of_val, ReflQuiv.adj.counit.app_map, composePath_comp,
    composePath_toPath]
  apply Quotient.sound
  apply composeEdges_unique
  exact { simplex := r, h₀₁ := rfl, h₁₂ := rfl, h₀₂ := rfl }

/--
An edge from `x₀` to `x₁` in a 2-truncated simplicial set defines an arrow in the refl quiver
`OneTruncation₂.{u} A)` from `x₀` to `x₁`.
-/
def edgeToHom {x₀ x₁ : A _⦋0⦌₂} (f : Edge x₀ x₁) :
    @Quiver.Hom (OneTruncation₂.{u} A) _ x₀ x₁ where
  edge := f.simplex
  src_eq := f.h₀
  tgt_eq := f.h₁

/--
An edge from `x₀` to `x₁` in a 2-truncated simplicial set defines an arrow in the free category
generated from the refl quiver `OneTruncation₂.{u} A)` from `x₀` to `x₁`.
-/
def edgeToFreeHom {x₀ x₁ : A _⦋0⦌₂} (f : Edge x₀ x₁) :
    @Quiver.Hom (FreeRefl.{u} (OneTruncation₂.{u} A)) _ ⟨x₀⟩ ⟨x₁⟩ :=
  Quot.mk _ (edgeToHom f).toPath

omit [Quasicategory₂ A] in
lemma compose_id_path {x₀ x₁ : A _⦋0⦌₂} (f : Edge x₀ x₁) :
    edgeToFreeHom f = Quot.mk _
      ((edgeToHom f).toPath.comp (edgeToHom (Edge.id x₁)).toPath) := by
  symm
  dsimp [edgeToFreeHom]
  apply Quot.sound
  have : (edgeToHom f).toPath = (edgeToHom f).toPath.comp .nil := rfl
  nth_rw 2 [this]
  rw [← Quiver.Path.comp_toPath_eq_cons]
  apply Quotient.comp_left
  apply Quotient.CompClosure.of
  constructor

/--
  Two (left) homotopic edges `f`, `g` are equivalent under the hom-relation `HoRel₂`
  generated by 2-simplices.
-/
lemma homotopic_edges_are_equiv {x₀ x₁ : A _⦋0⦌₂} (f g : Edge.{u} x₀ x₁) (htpy : HomotopicL f g) :
    HoRel₂ ⟨x₀⟩ ⟨x₁⟩ (edgeToFreeHom f) (edgeToFreeHom g) := by
  rw [compose_id_path g]
  dsimp [edgeToFreeHom]
  rcases HomotopicL.symm htpy with ⟨htpy⟩
  rw [← Quiver.Path.comp_toPath_eq_cons]
  apply HoRel₂.mk' (φ := htpy.simplex) <;> (dsimp [edgeToHom]; symm)
  . exact htpy.h₀₁
  . exact htpy.h₁₂
  . exact htpy.h₀₂

/--
  If a reflexive prefunctor `F : FreeRefl (OneTruncation₂ A) ⥤rq C` respects
  the hom-relation `HoRel₂`, then it can be lifted to  `HomotopyCategory₂ A`.
-/
noncomputable
def liftRq₂ {C : Type} [ReflQuiver C] (F : FreeRefl.{u} (OneTruncation₂.{u} A) ⥤rq C)
    (h : ∀ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : Quiver.Hom.{u + 1, u} x y),
      (r : HoRel₂ x y f g) → F.map f = F.map g) :
    HomotopyCategory₂.{u} A ⥤rq C where
  obj x := F.obj ⟨x⟩
  map f := Quotient.liftOn f
    (fun e ↦ F.map (edgeToFreeHom e))
    (fun f g ↦ by
      intro htpy
      dsimp
      apply h
      exact homotopic_edges_are_equiv f g htpy)
  map_id := by
    intro x
    dsimp [CategoryStruct.id]
    show ⟦Edge.id x⟧.liftOn _ _ = 𝟙rq (F.obj { as := x})
    have : 𝟙rq (F.obj { as := x}) = F.map (𝟙 { as := x }) := (F.map_id { as := x }).symm
    rw [Quotient.liftOn_mk, this]
    congr 1
    dsimp [edgeToFreeHom, CategoryStruct.id]
    apply Quot.sound
    apply Quotient.CompClosure.of
    constructor

theorem lift_unique_rq₂ {C} [ReflQuiver.{u + 1, u} C] (F₁ F₂ : (HomotopyCategory₂.{u} A) ⥤rq C)
    (h : quotientReflPrefunctor₂ ⋙rq F₁ = quotientReflPrefunctor₂ ⋙rq F₂) : F₁ = F₂ := by
  apply ReflPrefunctor.ext'
  . intro x₀ x₁
    apply Quotient.ind
    intro f
    have q_is_quotient : quotientReflPrefunctor₂.map (edgeToHom f) =
      Quotient.mk (instSetoidEdge x₀ x₁) f := rfl
    rw [← q_is_quotient, ← ReflPrefunctor.comp_map, ← ReflPrefunctor.comp_map,
      ReflPrefunctor.congr_hom h.symm]
  . intro x
    have : (quotientReflPrefunctor₂.{u} ⋙rq F₁).obj x = (quotientReflPrefunctor₂.{u} ⋙rq F₂).obj x :=
       congrFun (congrArg Prefunctor.obj (congrArg ReflPrefunctor.toPrefunctor h)) x
    rw [ReflPrefunctor.comp_obj, ReflPrefunctor.comp_obj] at this
    dsimp [quotientReflPrefunctor₂] at this
    exact this

/--
  If a functor `F : FreeRefl (OneTruncation₂ A) ⥤ C` respects the hom-relation `HoRel₂`,
  then it can be lifted to  `HomotopyCategory₂ A` (see the weaker statement `liftRq₂`).
-/
noncomputable
def lift₂ {C : Type} [Category C] (F : FreeRefl.{u} (OneTruncation₂.{u} A) ⥤ C)
    (h : ∀ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : Quiver.Hom.{u + 1, u} x y),
      (r : HoRel₂ x y f g) → F.map f = F.map g) :
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
      have : ⟦f⟧ ≫ ⟦g⟧ = h' := by
        dsimp only [CategoryStruct.comp, composeHEdges]
        rw [Quotient.lift₂_mk]
        rfl
      rw [this]
      dsimp only [h', Quotient.lift_mk]
      apply h
      apply HoRel₂.mk' (φ := p.snd.simplex) <;> symm
      . exact p.snd.h₀₁
      . exact p.snd.h₁₂
      . exact p.snd.h₀₂
  }

lemma is_lift₂ {C : Type} [Category C] (F : FreeRefl.{u} (OneTruncation₂.{u} A) ⥤ C)
    (h : ∀ (x y : FreeRefl.{u} (OneTruncation₂.{u} A))
      (f g : Quiver.Hom.{u + 1, u} x y),
      (r : HoRel₂ x y f g) → F.map f = F.map g) :
    quotientFunctor₂.{u} ⋙ lift₂ F h = F := by
  apply FreeRefl.lift_unique'
  apply Paths.ext_functor
  intro x y f
  simp only [FreeRefl.quotientFunctor, Quotient.functor, lift₂, liftRq₂, Functor.comp_obj,
    Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
  . rw [qFunctor_map_toPath]; rfl
  . rfl

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
  apply lift_unique_rq₂
  let η := ReflQuiv.adj.unit.app (OneTruncation₂ A)
  rw [unit_app_quotientFunctor.{u}, ReflPrefunctor.comp_assoc,
    ← Functor.toReflPrefunctor.map_comp (C := FreeRefl (OneTruncation₂ A)), h]
  rfl

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
def isoHomotopyCategories : (Cat.of (HomotopyCategory A)) ≅ (Cat.of (HomotopyCategory₂ A)) where
  hom := CategoryTheory.Quotient.lift _ quotientFunctor₂ qFunctor_respects_horel₂
  inv := lift₂ (HomotopyCategory.quotientFunctor A) (by
    intro _ _ _ _ h
    simp only [Cat.of_α, HomotopyCategory.quotientFunctor, Quotient.functor]
    apply Quot.sound
    apply Quotient.CompClosure.of
    exact h)
  hom_inv_id := by
    apply HomotopyCategory.lift_unique'
    dsimp only [Cat.of_α, HomotopyCategory.quotientFunctor, CategoryStruct.comp]
    rw [← Functor.assoc, Quotient.lift_spec, is_lift₂]
    rfl
  inv_hom_id := by
    apply HomotopyCategory₂.lift_unique'
    dsimp only [Cat.of_α, CategoryStruct.comp, HomotopyCategory.quotientFunctor]
    rw [← Functor.assoc, is_lift₂, Quotient.lift_spec]
    rfl

end isomorphism_of_htpy_categories

end Quasicategory₂

end SSet
