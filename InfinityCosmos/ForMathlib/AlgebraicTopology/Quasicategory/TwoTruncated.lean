/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex

open Simplicial SimplexCategory CategoryTheory SimplexCategory.Truncated Truncated.Hom
  SimplicialObject SimplicialObject.Truncated

namespace SSet
namespace Truncated

/-
The idea behind this trivial equivalence and the lemma
is to make explicit whether an object is in a truncated simplicial set;
this allows us to replace `dsimp`s in proofs by `rw`s.
-/
def truncEquiv {S : SSet} (m : ℕ) {a : SimplexCategory} (ha : a.len ≤ m := by trunc) :
    S.obj (Opposite.op a) ≃ ((truncation m).obj S).obj (Opposite.op ⟨a, ha⟩) where
  toFun := id
  invFun := id
  left_inv := congrFun rfl
  right_inv := congrFun rfl

lemma trunc_map {S : SSet} {m : ℕ} {a b : SimplexCategory}
    (ha : a.len ≤ m := by trunc) (hb : b.len ≤ m := by trunc)
    {f : a ⟶ b} {σ : S.obj (Opposite.op b)} :
    ((truncation m).obj S).map (tr f).op (truncEquiv m hb σ) = S.map f.op σ := rfl

lemma trunc_map' {S : SSet} {m : ℕ} {a b : SimplexCategory}
    (ha : a.len ≤ m := by trunc) (hb : b.len ≤ m := by trunc)
    {f : a ⟶ b} {σ : truncation m |>.obj S |>.obj (Opposite.op ⟨b, hb⟩)} :
    ((truncation m).obj S).map (tr f).op σ = S.map f.op σ := rfl

section comp_struct
/--
`Edge x₀ x₁` is a wrapper around a 1-simplex in a 2-truncated simplicial set
with source `x₀` and target `x₁`.
-/
structure Edge {X : Truncated 2} (x₀ : X _⦋0⦌₂) (x₁ : X _⦋0⦌₂) where
  simplex : X _⦋1⦌₂
  h₀ : X.map (tr (δ 1)).op simplex = x₀
  h₁ : X.map (tr (δ 0)).op simplex = x₁

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

end Truncated

section fill21
open Truncated (Edge CompStruct truncEquiv trunc_map trunc_map')
open horn₂₁

variable {S : SSet} {x₀ x₁ x₂ : ((truncation 2).obj S) _⦋0⦌₂}
  (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)

abbrev edge_map {y₀ y₁ : ((truncation 2).obj S) _⦋0⦌₂} (e : Edge y₀ y₁) : Δ[1] ⟶ S :=
  yonedaEquiv.symm e.simplex

def path_edges_comm : pt₁ ≫ edge_map e₁₂ = pt₀ ≫ edge_map e₀₁ := by
  rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
  congr 1
  apply Eq.trans
  . exact e₁₂.h₀
  . symm; exact e₀₁.h₁

-- TODO fix unintuitive order of edges
def horn_from_data21 : Λ[2, 1].toSSet ⟶ S :=
  Limits.PushoutCocone.IsColimit.desc horn_is_pushout
    (edge_map e₁₂) (edge_map e₀₁) (path_edges_comm e₀₁ e₁₂)

lemma aux0: ι₀ ≫ (horn_from_data21 e₀₁ e₁₂) = yonedaEquiv.symm e₁₂.simplex :=
  Limits.PushoutCocone.IsColimit.inl_desc horn_is_pushout
    (edge_map e₁₂) (edge_map e₀₁) (path_edges_comm e₀₁ e₁₂)

lemma aux1: ι₂ ≫ (horn_from_data21 e₀₁ e₁₂) = yonedaEquiv.symm e₀₁.simplex :=
  Limits.PushoutCocone.IsColimit.inr_desc horn_is_pushout
    (edge_map e₁₂) (edge_map e₀₁) (path_edges_comm e₀₁ e₁₂)

def fill21_from_horn_extension
    (g : Δ[2] ⟶ S)
    (comm : horn_from_data21 e₀₁ e₁₂ = Λ[2, 1].ι ≫ g) :
    Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂ := by
  constructor; swap
  exact {
    simplex := (truncEquiv 2) <| yonedaEquiv <| stdSimplex.δ 1 ≫ g
    h₀ := by
      rw [← e₀₁.h₀, trunc_map, trunc_map']
      have : yonedaEquiv.symm (e₀₁.simplex) = stdSimplex.δ 2 ≫ g := by
        rw [← aux1 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      rw [push_yonedaEquiv this]
      have : δ 1 ≫ δ 2 = δ 1 ≫ @δ 1 1 :=
        SimplexCategory.δ_comp_δ (n := 0) (i := 1) (j := 1) (le_refl 1)
      rw [this]
      apply push_yonedaEquiv
      rw [Equiv.symm_apply_apply]; rfl
    h₁ := by
      rw [← e₁₂.h₁, trunc_map, trunc_map']
      have : yonedaEquiv.symm (e₁₂.simplex) = stdSimplex.δ 0 ≫ g := by
        rw [← aux0 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₀]
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
        rw [← aux1 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      rw [← push_yonedaEquiv' this]
    h₁₂ := by
      rw [trunc_map]
      have : yonedaEquiv.symm (e₁₂.simplex) = stdSimplex.δ 0 ≫ g := by
        rw [← aux0 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₀]
      rw [← push_yonedaEquiv' this]
    h₀₂ := by
      rw [trunc_map]
      dsimp only [len_mk, id_eq, Nat.reduceAdd, Fin.isValue, eq_mpr_eq_cast, cast_eq, op_comp,
        Fin.succ_zero_eq_one, Fin.castSucc_zero]
      rw [← map_yonedaEquiv']; rfl
  }

end fill21

section fill31
open horn₃₁
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

def π' (a : R) : (Δ[2] ⟶ S) := match a with
  | ⟨0, _⟩ => yonedaEquiv.symm f₀.simplex
  | ⟨1, _⟩ => by contradiction
  | ⟨2, _⟩ => yonedaEquiv.symm f₂.simplex
  | ⟨3, _⟩ => yonedaEquiv.symm f₃.simplex

def face (a : R) : S _⦋2⦌ := match a with
  | ⟨0, _⟩ => f₀.simplex
  | ⟨1, _⟩ => by contradiction
  | ⟨2, _⟩ => f₂.simplex
  | ⟨3, _⟩ => f₃.simplex

abbrev R₀ : R := ⟨0, by omega⟩
abbrev R₂ : R := ⟨2, by omega⟩
abbrev R₃ : R := ⟨3, by omega⟩

lemma edge₀₂ : S.map (δ 1).op (face f₃ f₀ f₂ R₃) = e₀₂.simplex := by
  dsimp only [Nat.reduceAdd, Fin.isValue, face]
  exact f₃.h₀₂

-- The multicofork ⨿ Δ[1] ⇉ ⨿ Δ[2] → X defined by sending Δ[2]s to
-- each of the three simplices in the combinatorial `horn_data`
def multicofork_from_data : Limits.Multicofork multispan_index :=
  Limits.Multicofork.ofπ multispan_index S
    (π' f₃ f₀ f₂)
    (by
      rintro ⟨⟨⟨i, i_ne_1⟩, ⟨j, j_ne_1⟩⟩, i_lt_j⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp [J, multispan_index, π']
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

-- TODO proper documentation
-- using the fact that Λ[3, 1] is the coequalizer gives a map Λ[3, 1] → X
def horn_from_data : Λ[3, 1].toSSet ⟶ S := Limits.IsColimit.desc horn₃₁.isMulticoeq
  (multicofork_from_data f₃ f₀ f₂)

/-
  A group of lemmas stating that the faces of the simplex `Δ[3] ⟶ S` extending the horn
  `horn_from_data f₃ f₀ f₂ : Λ[3, 1] ⟶ S` are as expected
-/
lemma horn_extension_face₀ {g : Δ[3] ⟶ S} (comm : horn_from_data f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₀.simplex = stdSimplex.δ 0 ≫ g := by
  have : horn₃₁.ι₀ ≫ (horn_from_data f₃ f₀ f₂) = yonedaEquiv.symm f₀.simplex :=
    horn₃₁.isMulticoeq.fac (multicofork_from_data f₃ f₀ f₂) (.right R₀)
  rw [← this, comm, ← Category.assoc, horn₃₁.incl₀]

lemma horn_extension_face₂ {g : Δ[3] ⟶ S} (comm : horn_from_data f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₂.simplex = stdSimplex.δ 2 ≫ g := by
  have : horn₃₁.ι₂ ≫ (horn_from_data f₃ f₀ f₂) = yonedaEquiv.symm f₂.simplex :=
    horn₃₁.isMulticoeq.fac (multicofork_from_data f₃ f₀ f₂) (.right R₂)
  rw [← this, comm, ← Category.assoc, horn₃₁.incl₂]

lemma horn_extension_face₃ {g : Δ[3] ⟶ S} (comm : horn_from_data f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : horn₃₁.ι₃ ≫ (horn_from_data f₃ f₀ f₂) = yonedaEquiv.symm f₃.simplex :=
    horn₃₁.isMulticoeq.fac (multicofork_from_data f₃ f₀ f₂) (.right R₃)
  rw [← this, comm, ← Category.assoc, horn₃₁.incl₃]

def fill31_from_horn_extension
    (g : Δ[3] ⟶ S)
    (comm : horn_from_data f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
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

end fill31

-- TODO should this be SSet namespace or SSet.Truncated?
instance two_truncatation_of_qc_is_2_trunc_qc {X : SSet} [Quasicategory X] :
    Truncated.Quasicategory₂ ((truncation 2).obj X) where
  fill21 e₀₁ e₁₂ := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp) (horn_from_data21 e₀₁ e₁₂)
    apply Nonempty.intro
    exact (fill21_from_horn_extension e₀₁ e₁₂ g h)
  fill31 f₃ f₀ f₂ := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp) (horn_from_data f₃ f₀ f₂)
    apply Nonempty.intro
    exact (fill31_from_horn_extension f₃ f₀ f₂ g h)
