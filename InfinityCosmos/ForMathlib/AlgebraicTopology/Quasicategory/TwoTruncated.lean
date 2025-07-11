/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Basic

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
  | ⟨0, _⟩ => yonedaEquiv.symm f₀.simplex
  | ⟨1, _⟩ => by contradiction
  | ⟨2, _⟩ => yonedaEquiv.symm f₂.simplex
  | ⟨3, _⟩ => yonedaEquiv.symm f₃.simplex

def chooseFace' (a : R) : S _⦋2⦌ := match a with
  | ⟨0, _⟩ => f₀.simplex
  | ⟨1, _⟩ => by contradiction
  | ⟨2, _⟩ => f₂.simplex
  | ⟨3, _⟩ => f₃.simplex

abbrev R₀ : R := ⟨0, by omega⟩
abbrev R₂ : R := ⟨2, by omega⟩
abbrev R₃ : R := ⟨3, by omega⟩

-- The multicofork `⨿ Δ[1] ⇉ ⨿ Δ[2] ⟶ S` defined by sending `Δ[2]`s to
-- each of the three faces `f₃`, `f₀`, `f₂`.
def multicoforkFromFaces : Limits.Multicofork multispanIndex :=
  Limits.Multicofork.ofπ multispanIndex S
    (chooseFace f₃ f₀ f₂)
    (by
      rintro ⟨⟨⟨i, i_ne_1⟩, ⟨j, j_ne_1⟩⟩, i_lt_j⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp [J, multispanIndex, chooseFace]
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      -- rw doesn't work because the statement is about `SSet`, not `Truncated 2`
      . apply Eq.trans
        exact f₀.h₀₂
        symm; exact f₂.h₁₂
      . apply Eq.trans
        exact f₀.h₀₁
        symm; exact f₃.h₁₂
      . apply Eq.trans
        exact f₂.h₀₁
        symm; exact f₃.h₀₁)

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
    isMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₂) (.right R₀)
  rw [← this, comm, ← Category.assoc, incl₀]

lemma horn_extension_face₂ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₂.simplex = stdSimplex.δ 2 ≫ g := by
  have : ι₂ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₂.simplex :=
    isMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₂) (.right R₂)
  rw [← this, comm, ← Category.assoc, incl₂]

lemma horn_extension_face₃ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : ι₃ ≫ (fromFaces f₃ f₀ f₂) = yonedaEquiv.symm f₃.simplex :=
    isMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₂) (.right R₃)
  rw [← this, comm, ← Category.assoc, incl₃]

/--
Given a map `Δ[3] ⟶ S` extending the horn given by `fromFaces`, obtain a
2-simplex bounded by edges `e₀₂`, `e₂₃` and `e₀₃`. See also `Quasicategory₂.fill31`.
-/
def fromHornExtension
    (g : Δ[3] ⟶ S)
    (comm : fromFaces f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    (CompStruct e₀₂ e₂₃ e₀₃) where
  simplex := (truncEquiv 2) <| S.map (δ 1).op (yonedaEquiv g)
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
  | ⟨0, _⟩ => yonedaEquiv.symm f₀.simplex
  | ⟨1, _⟩ => yonedaEquiv.symm f₁.simplex
  | ⟨2, _⟩ => by contradiction
  | ⟨3, _⟩ => yonedaEquiv.symm f₃.simplex

def chooseFace' (a : R) : S _⦋2⦌ := match a with
  | ⟨0, _⟩ => f₀.simplex
  | ⟨1, _⟩ => f₁.simplex
  | ⟨2, _⟩ => by contradiction
  | ⟨3, _⟩ => f₃.simplex

abbrev R₀ : R := ⟨0, by omega⟩
abbrev R₁ : R := ⟨1, by omega⟩
abbrev R₃ : R := ⟨3, by omega⟩

-- The multicofork `⨿ Δ[1] ⇉ ⨿ Δ[2] ⟶ S` defined by sending `Δ[2]`s to
-- each of the three faces `f₃`, `f₀`, `f₁`.
def multicoforkFromFaces : Limits.Multicofork multispanIndex :=
  Limits.Multicofork.ofπ multispanIndex S
    (chooseFace f₃ f₀ f₁)
    (by
      rintro ⟨⟨⟨i, i_ne_1⟩, ⟨j, j_ne_1⟩⟩, i_lt_j⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp [J, multispanIndex, chooseFace]
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      -- rw doesn't work because the statement is about `SSet`, not `Truncated 2`
      . apply Eq.trans
        exact f₀.h₁₂
        symm; exact f₁.h₁₂
      . apply Eq.trans
        exact f₀.h₀₁
        symm; exact f₃.h₁₂
      . apply Eq.trans
        exact f₁.h₀₁
        symm; exact f₃.h₀₂)

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
    multicoforkIsMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₁) (.right R₀)
  rw [← this, comm, ← Category.assoc, incl₀]

lemma horn_extension_face₁ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₁.simplex = stdSimplex.δ 1 ≫ g := by
  have : ι₁ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₁.simplex :=
    multicoforkIsMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₁) (.right R₁)
  rw [← this, comm, ← Category.assoc, incl₁]

lemma horn_extension_face₃ {g : Δ[3] ⟶ S} (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : ι₃ ≫ (fromFaces f₃ f₀ f₁) = yonedaEquiv.symm f₃.simplex :=
    multicoforkIsMulticoeq.fac (multicoforkFromFaces f₃ f₀ f₁) (.right R₃)
  rw [← this, comm, ← Category.assoc, incl₃]

/--
Given a map `Δ[3] ⟶ S` extending the horn given by `fromFaces`, obtain a
2-simplex bounded by edges `e₀₁`, `e₁₃` and `e₀₃`. See also `Quasicategory₂.fill32`.
-/
def fromHornExtension
    (g : Δ[3] ⟶ S)
    (comm : fromFaces f₃ f₀ f₁ = Λ[3, 2].ι ≫ g) :
    (CompStruct e₀₁ e₁₃ e₀₃) where
  simplex := (truncEquiv 2) <| S.map (δ 2).op (yonedaEquiv g)
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
abbrev HomotopicL {A : Truncated 2} {x y : A _⦋0⦌₂} (f g : Edge x y) := Nonempty (CompStruct f (id y) g)

/--
See `HomotopicL`.
-/
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
def HomotopicL.refl {x : A _⦋0⦌₂} : HomotopicL (id x) (id x) := ⟨idCompId x⟩

/--
Left homotopy relation is symmetric
-/
def HomotopicL.symm {x y : A _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicL f g) :
    HomotopicL g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idCompId y) (compId f)

/--
Left homotopy relation is transitive
-/
def HomotopicL.trans {x y : A _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) :
    HomotopicL f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idCompId y) hgh

/--
Right homotopy relation is reflexive
-/
def HomotopicR.refl {x : A _⦋0⦌₂} : HomotopicR (id x) (id x) := ⟨idCompId x⟩

/--
Right homotopy relation is symmetric
-/
def HomotopicR.symm {x y : A _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicR f g) :
    HomotopicR g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idCompId x) hfg (idComp f)

/--
Right homotopy relation is transitive
-/
def HomotopicR.trans {x y : A _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicR f g)
    (hgh : HomotopicR g h) :
    HomotopicR f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idCompId x) hfg hgh

/--
The right and left homotopy relations coincide
-/
theorem left_homotopic_iff_right_homotopic {x y : A _⦋0⦌₂} {f g : Edge x y} :
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
  left_homotopic_iff_right_homotopic.2 (Quasicategory₂.fill32 (idComp f) s s')

lemma transport_edge₀ {f : Edge x y} {g g' : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL g g') : Nonempty (CompStruct f g' h) := by
  rcases htpy with ⟨htpy⟩
  exact Quasicategory₂.fill32 s htpy (compId h)

lemma transport_edge₁ {f : Edge x y} {g : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL h h') : Nonempty (CompStruct f g h') := by
  rcases (left_homotopic_iff_right_homotopic.1 htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 (idComp f) s htpy

lemma transport_edge₂ {f f' : Edge x y} {g : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL f f') : Nonempty (CompStruct f' g h) := by
  rcases (left_homotopic_iff_right_homotopic.1 htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 htpy s (idComp h)

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

end Quasicategory₂

end SSet
