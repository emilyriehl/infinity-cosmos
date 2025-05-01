import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.Quasicategory.Basic

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn

import Mathlib.Topology.Spectral.Prespectral

open Simplicial SimplexCategory
open CategoryTheory SimplexCategory.Truncated Truncated.Hom SimplicialObject
open SimplicialObject.Truncated

#check PrespectralSpace.of_isTopologicalBasis'

-- TODO should these go into the SimplexCategory.Basics file?
namespace SimplexCategory

lemma mkOfSucc_2_0 : @mkOfSucc 2 0 = δ 2 := by ext i; fin_cases i <;> rfl
lemma mkOfSucc_2_1 : @mkOfSucc 2 1 = δ 0 := by ext i; fin_cases i <;> rfl

end SimplexCategory

namespace SSet
namespace Truncated

-- TODO place these somewhere nice + are they necessary?
/- The idea behind this trivial equivalence and the lemma
  is to make explicit whether an object is in a truncated simplicial set;
  this allows us to replace dsimps in proofs by a rw
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
variable {X : Truncated 2}
variable {x₀ x₁ x₂ : X _⦋0⦌₂}

structure Edge (x₀ : X _⦋0⦌₂) (x₁ : X _⦋0⦌₂) where
  simplex : X _⦋1⦌₂
  h₀ : X.map (tr (δ 1)).op simplex = x₀
  h₁ : X.map (tr (δ 0)).op simplex = x₁

structure CompStruct (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) where
  simplex : X _⦋2⦌₂
  h₀₁ : X.map (tr (δ 2)).op simplex = e₀₁.simplex
  h₁₂ : X.map (tr (δ 0)).op simplex = e₁₂.simplex
  h₀₂ : X.map (tr (δ 1)).op simplex = e₀₂.simplex
end comp_struct

/--
A 2-truncated quasicategory is a 2-truncated simplicial set with 3 properties:
  (2, 1)-filling
  (3, 1)-filling
  (3, 2)-filling
See `fill31.horn_data` and `fill31.filling_simplex` for the details of (3, 1)-filling,
and `fill32.horn_data` and `fill32.filling_simplex` for the details of (3, 2)-filling.
-/
structure Quasicategory₂ (X : Truncated 2) where
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

-- TODO: this section contains 3 lemmas moving application of yonedaEquiv around.
-- some of these might be already in the library under a different name,
-- and the proofs could probably be greatly simplified
section aux_lemmas

-- TODO name collision!
lemma map_yonedaEquiv {n m : ℕ} {X : SSet} (f : ⦋n⦌ ⟶ ⦋m⦌) (g : Δ[m] ⟶ X) :
    X.map f.op (yonedaEquiv g) = g.app (Opposite.op ⦋n⦌) (stdSimplex.objEquiv.symm f) := by
  change (g.app (Opposite.op ⦋m⦌) ≫ X.map f.op) (stdSimplex.objEquiv.symm (𝟙 _)) =
     g.app (Opposite.op ⦋n⦌) (stdSimplex.objEquiv.symm f)
  rw [← g.naturality]
  dsimp
  have : Δ[m].map f.op (stdSimplex.objEquiv.symm (𝟙 _)) = stdSimplex.objEquiv.symm f := by
    aesop_cat
  rw [this]
  rfl

-- TODO implicit arguments!
lemma push_yonedaEquiv {n m k : ℕ} {X : SSet} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : X.obj (Opposite.op ⦋n⦌)) {s : ⦋n⦌ ⟶ ⦋k⦌} {g : Δ[k] ⟶ X}
    (h : yonedaEquiv.symm σ = stdSimplex.map s ≫ g) :
    X.map f.op σ = X.map (f ≫ s).op (yonedaEquiv g) := by
  rw [← Equiv.apply_symm_apply yonedaEquiv σ, h]
  have : yonedaEquiv (stdSimplex.map s ≫ g) = X.map s.op (yonedaEquiv g) := by
    rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_map, ← map_yonedaEquiv]
  rw [this, ← FunctorToTypes.map_comp_apply, ← op_comp]

-- TODO rename
lemma map_yonedaEquiv' {n m : ℕ} {X : SSet} (f : ⦋m⦌ ⟶ ⦋n⦌) {g : Δ[n] ⟶ X} :
    yonedaEquiv (stdSimplex.map f ≫ g) = X.map f.op (yonedaEquiv g) := by
  rw [yonedaEquiv_comp, map_yonedaEquiv, ← stdSimplex.yonedaEquiv_map]

lemma push_yonedaEquiv' {n m : ℕ} {X : SSet} {f : ⦋m⦌ ⟶ ⦋n⦌}
    {σ : X.obj (Opposite.op ⦋m⦌)} {g : Δ[n] ⟶ X}
    (h : yonedaEquiv.symm σ = stdSimplex.map f ≫ g) :
    σ = X.map f.op (yonedaEquiv g) := by
  rw [← map_yonedaEquiv']
  apply (Equiv.symm_apply_eq yonedaEquiv).1
  exact h

lemma map_comp_yonedaEquiv_symm {n m : ℕ} {X : SSet} (f : .mk n ⟶ .mk m)
    (s : X.obj (.op (.mk m))) :
    stdSimplex.map f ≫ yonedaEquiv.symm s = yonedaEquiv.symm (X.map f.op s) := by
  apply yonedaEquiv.apply_eq_iff_eq_symm_apply.1
  let s' := yonedaEquiv.symm s
  have : s = yonedaEquiv s' := (Equiv.symm_apply_eq yonedaEquiv).mp rfl
  rw [this, map_yonedaEquiv, yonedaEquiv_comp, Equiv.apply_symm_apply yonedaEquiv _,
    stdSimplex.yonedaEquiv_map]

end aux_lemmas

section horn_from_horn_data21
open SimplexCategory
open horn₂₁
namespace horn₂₁

abbrev pathEdge₀ {X : SSet} (f : Path X 2) : Δ[1] ⟶ X := yonedaEquiv.symm (f.arrow 0)
abbrev pathEdge₁ {X : SSet} (f : Path X 2) : Δ[1] ⟶ X := yonedaEquiv.symm (f.arrow 1)

def path_edges_comm {X : SSet} {f : SSet.Path X 2} : pt₁ ≫ pathEdge₁ f = pt₀ ≫ pathEdge₀ f := by
  rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm, f.arrow_src 1, f.arrow_tgt 0]; rfl

/-- Given a path of length 2 in the 2-truncation of a simplicial set `X`, construct
the obvious map Λ[2, 1] → X using that Λ[2, 1] is a pushout
-/
def horn_from_path {X : SSet} (f : ((truncation 2).obj X).Path 2) : Λ[2, 1].toSSet ⟶ X :=
  Limits.PushoutCocone.IsColimit.desc horn_is_pushout (pathEdge₁ f) (pathEdge₀ f) path_edges_comm

-- the following lemmas stem from the universal property of the horn pushout
lemma pushout_up0 {X : SSet} (f : ((truncation 2).obj X).Path 2) :
    hornTwo_edge₀ ≫ horn_from_path f = yonedaEquiv.symm (f.arrow 1) :=
  Limits.PushoutCocone.IsColimit.inl_desc horn_is_pushout
    (pathEdge₁ f) (pathEdge₀ f) path_edges_comm

lemma pushout_up1 {X : SSet} (f : ((truncation 2).obj X).Path 2) :
    hornTwo_edge₂ ≫ horn_from_path f = yonedaEquiv.symm (f.arrow 0) :=
  Limits.PushoutCocone.IsColimit.inr_desc horn_is_pushout
    (pathEdge₁ f) (pathEdge₀ f) path_edges_comm

end horn₂₁

section horn21_comp_struct
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

lemma aux0: hornTwo_edge₀ ≫ (horn_from_data21 e₀₁ e₁₂) = yonedaEquiv.symm e₁₂.simplex :=
  Limits.PushoutCocone.IsColimit.inl_desc horn_is_pushout
    (edge_map e₁₂) (edge_map e₀₁) (path_edges_comm e₀₁ e₁₂)

lemma aux1: hornTwo_edge₂ ≫ (horn_from_data21 e₀₁ e₁₂) = yonedaEquiv.symm e₀₁.simplex :=
  Limits.PushoutCocone.IsColimit.inr_desc horn_is_pushout
    (edge_map e₁₂) (edge_map e₀₁) (path_edges_comm e₀₁ e₁₂)

def fill21'
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
      rw [push_yonedaEquiv _ _ this]
      have : δ 1 ≫ δ 2 = δ 1 ≫ @δ 1 1 :=
        SimplexCategory.δ_comp_δ (n := 0) (i := 1) (j := 1) (le_refl 1)
      rw [this]
      apply push_yonedaEquiv
      rw [Equiv.symm_apply_apply]; rfl
    h₁ := by
      rw [← e₁₂.h₁, trunc_map, trunc_map']
      have : yonedaEquiv.symm (e₁₂.simplex) = stdSimplex.δ 0 ≫ g := by
        rw [← aux0 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₀]
      rw [push_yonedaEquiv _ _ this]
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

end horn21_comp_struct

end horn_from_horn_data21

/- define the structures Edge and CompStruct for a 2-truncated simplicial set `X : Truncated 2`
  and vertices `x₀`, ..., `x₃`
-/

section fill31_comp_struct

open Truncated (CompStruct Edge)

variable {S : SSet}
variable
    {x₀ x₁ x₂ x₃ : ((truncation 2).obj S) _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
    (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
    (f₂ : CompStruct e₀₁ e₁₃ e₀₃)

include S x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃ f₃ f₀ f₂
open horn₃₁
#check horn₃₁.multispan_index


/- steps of constructing fill31' from (g : Δ[3] ⟶ X):
  . construct a multicofork from the given CompStructs
  . construct a map h : Λ[3, 1] ⟶ X such that h = Λ[3, 1].ι ≫ g
  . make a CompStruct with simplex given by g, prove equalities
-/
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

-- using the fact that Λ[3, 1] is the coequalizer gives a map Λ[3, 1] → X
def horn_from_data : Λ[3, 1].toSSet ⟶ S := Limits.IsColimit.desc horn₃₁.isMulticoeq
  (multicofork_from_data f₃ f₀ f₂)

-- TODO rename these to something more useful
lemma mcofork_up0 : horn₃₁.ι₀ ≫ (horn_from_data f₃ f₀ f₂) = yonedaEquiv.symm f₀.simplex :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data f₃ f₀ f₂) (.right R₀)

lemma mcofork_up2 : horn₃₁.ι₂ ≫ (horn_from_data f₃ f₀ f₂) = yonedaEquiv.symm f₂.simplex :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data f₃ f₀ f₂) (.right R₂)

lemma mcofork_up3 : horn₃₁.ι₃ ≫ (horn_from_data f₃ f₀ f₂) = yonedaEquiv.symm f₃.simplex :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data f₃ f₀ f₂) (.right R₃)

-- TODO add congruence lemma?
def fill31_from_horn_extension'
    (g : Δ[3] ⟶ S)
    (comm : horn_from_data f₃ f₀ f₂ = Λ[3, 1].ι ≫ g) :
    (CompStruct e₀₂ e₂₃ e₀₃) := by
  have y0 : yonedaEquiv.symm f₀.simplex = stdSimplex.δ 0 ≫ g := by
    rw [← mcofork_up0, comm, ← Category.assoc, horn₃₁.incl₀]
  have y2 : yonedaEquiv.symm f₂.simplex = stdSimplex.δ 2 ≫ g := by
    rw [← mcofork_up2, comm, ← Category.assoc, horn₃₁.incl₂]
  have y3 : yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
    rw [← mcofork_up3, comm, ← Category.assoc, horn₃₁.incl₃]
  exact {
    simplex := S.map (δ 1).op (yonedaEquiv g)
    h₀₁ := by
      rw [← f₃.h₀₂]
      have := δ_comp_δ (n := 1) (i := 1) (j := 2) (by simp)
      dsimp at this
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
        len_mk, id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj,
        Nat.reduceAdd, Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ _ y3, this]
    h₁₂ := by
      rw [← f₀.h₁₂]
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
        len_mk, id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj,
        Nat.reduceAdd, Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ _ y0]
      apply congr_fun
      apply Prefunctor.congr_map
      apply (Opposite.op_inj_iff _ _).2
      exact @δ_comp_δ _ 0 0 (le_refl 0)
    h₀₂ := by
      rw [← f₂.h₀₂]
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
        len_mk, id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj,
        Nat.reduceAdd, Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ _ y2]
      apply congr_fun
      apply Prefunctor.congr_map
      apply (Opposite.op_inj_iff _ _).2
      symm; exact @δ_comp_δ _ 1 1 (le_refl 1)}

end fill31_comp_struct

def two_truncatation_of_qc_is_2_trunc_qc {X : SSet} [Quasicategory X] :
    Truncated.Quasicategory₂ ((truncation 2).obj X) where
  fill21 e₀₁ e₁₂ := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp) (horn_from_data21 e₀₁ e₁₂)
    apply Nonempty.intro
    exact (fill21' e₀₁ e₁₂ g h)
  fill31 f₃ f₀ f₂ := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp) (horn_from_data f₃ f₀ f₂)
    apply Nonempty.intro
    exact (fill31_from_horn_extension' f₃ f₀ f₂ g h)
