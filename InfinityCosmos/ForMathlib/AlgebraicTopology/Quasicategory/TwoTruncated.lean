import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.Quasicategory.Basic

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn

open Simplicial SimplexCategory
open CategoryTheory SimplexCategory.Truncated Truncated.Hom SimplicialObject
open SimplicialObject.Truncated

-- TODO should these go into the SimplexCategory.Basics file?
namespace SimplexCategory

lemma mkOfSucc_2_0 : @mkOfSucc 2 0 = δ 2 := by ext i; fin_cases i <;> rfl
lemma mkOfSucc_2_1 : @mkOfSucc 2 1 = δ 0 := by ext i; fin_cases i <;> rfl

end SimplexCategory

namespace SSet
namespace Truncated

namespace fill31

/-- Given a path `f` of length 3 in a 2-truncated simplicial set `X`, this
is the combinatorial data of three 2-simplices of `X` from which one can define a horn
Λ[3, 1] → X such that the spine of this horn is `f`.
-/
structure horn_data {X : Truncated 2} (f : X.Path 3) where
  σ₃ : X _⦋2⦌₂
  σ₀ : X _⦋2⦌₂
  σ₂ : X _⦋2⦌₂
  h₃ : spine X 2 _ σ₃ = f.interval 0 2
  h₀ : spine X 2 _ σ₀ = f.interval 1 2
  h₂₂ : X.map (tr (δ 2)).op σ₂ = f.arrow 0
  h₂₀ : X.map (tr (δ 0)).op σ₂ = X.map (tr (δ 1)).op σ₀

/--
Given a path `f` of length 3 in a 2-truncated simplicial set `X` and
horn_data `a`, `filling_simplex a σ` is the proposition that `σ` is a 2-simplex
that "fills in" the missing face of the horn defined by `a`. This is the (3, 1)-filling property.
-/
structure filling_simplex {X : Truncated 2} {f : X.Path 3} (a : horn_data f) (σ : X _⦋2⦌₂) : Prop where
  edge₀ : X.map (tr (δ 0)).op σ = f.arrow 2
  edge₁ : X.map (tr (δ 1)).op σ = X.map (tr (δ 1)).op a.σ₂
  edge₂ : X.map (tr (δ 2)).op σ = X.map (tr (δ 1)).op a.σ₃

end fill31

namespace fill32

/-- Given a path `f` of length 3 in a 2-truncated simplicial set `X`, this
is the combinatorial data of three 2-simplices of `X` from which one can define a horn
Λ[3, 1] → X such that the spine of this horn is `f`.
-/
structure horn_data {X : Truncated 2} (f : X.Path 3) where
  σ₃ : X _⦋2⦌₂
  σ₀ : X _⦋2⦌₂
  σ₁ : X _⦋2⦌₂
  h₃ : spine X 2 _ σ₃ = f.interval 0 2
  h₀ : spine X 2 _ σ₀ = f.interval 1 2
  h₁₂ : X.map (tr (δ 2)).op σ₁ = X.map (tr (δ 1)).op σ₃
  h₁₀ : X.map (tr (δ 0)).op σ₁ = f.arrow 2

/--
Given a path `f` of length 3 in a 2-truncated simplicial set `X` and
horn_data `a`, `filling_simplex a σ` is the proposition that `σ` is a 2-simplex
that "fills in" the missing face of the horn defined by `a`. This is the (3, 1)-filling property.
-/
structure filling_simplex {X : Truncated 2} {f : X.Path 3} (a : horn_data f) (σ : X _⦋2⦌₂) : Prop where
  edge₀ : X.map (tr (δ 0)).op σ = X.map (tr (δ 1)).op a.σ₀
  edge₁ : X.map (tr (δ 1)).op σ = X.map (tr (δ 1)).op a.σ₁
  edge₂ : X.map (tr (δ 2)).op σ = f.arrow 0
end fill32

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
  fill21 (f : Path X 2) : ∃ (σ : X _⦋2⦌₂), spine X 2 _ σ = f
  fill31 {f : Path X 3} (a : fill31.horn_data f) : ∃ σ₁ : X _⦋2⦌₂, fill31.filling_simplex a σ₁
  fill32 {f : Path X 3} (a : fill32.horn_data f) : ∃ σ₁ : X _⦋2⦌₂, fill32.filling_simplex a σ₁

end Truncated

-- TODO: this section contains 3 lemmas moving application of yonedaEquiv around.
-- some of these might be already in the library under a different name,
-- and the proofs could probably be greatly simplified
section aux_lemmas

lemma map_yonedaEquiv {n m : ℕ} {X : SSet} (f : .mk n ⟶ .mk m) (g : Δ[m] ⟶ X) :
    X.map f.op (yonedaEquiv g) = g.app (Opposite.op (mk n)) (stdSimplex.objEquiv.symm f) := by
  have : yonedaEquiv g = g.app (Opposite.op (mk m)) (stdSimplex.objEquiv.symm (𝟙 _)) := rfl
  rw [this]
  have : X.map f.op (g.app (Opposite.op (mk m)) (stdSimplex.objEquiv.symm (𝟙 _))) =
    (g.app (Opposite.op (mk m)) ≫ X.map f.op) (stdSimplex.objEquiv.symm (𝟙 _)) := rfl
  rw [← g.naturality] at this
  rw [this]
  -- TODO stdSimplex.map_id is probably helpful here
  have : Δ[m].map f.op (stdSimplex.objEquiv.symm (𝟙 _)) = stdSimplex.objEquiv.symm f := by aesop_cat
  dsimp
  rw [this]
  rfl

lemma push_yonedaEquiv {n m k : ℕ} {X : SSet} (f : .mk n ⟶ .mk m)
    (σ : X.obj (Opposite.op (.mk m))) {s : .mk m ⟶ .mk k} {g : Δ[k] ⟶ X}
    (h : yonedaEquiv.symm σ = stdSimplex.map s ≫ g) :
    X.map f.op σ = X.map (f ≫ s).op (yonedaEquiv g) := by
  rw [← Equiv.apply_symm_apply yonedaEquiv σ, h]
  have : yonedaEquiv (stdSimplex.map s ≫ g) = X.map s.op (yonedaEquiv g) := by
    rw [yonedaEquiv_comp, map_yonedaEquiv, stdSimplex.yonedaEquiv_map]
  rw [this, ← FunctorToTypes.map_comp_apply, ← op_comp]

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
open Truncated (Edge CompStruct)
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
    simplex := yonedaEquiv (stdSimplex.δ 1 ≫ g)
    h₀ := by
      rw [← e₀₁.h₀]
      have : yonedaEquiv.symm (e₀₁.simplex) = stdSimplex.δ 2 ≫ g := by
        rw [← aux1 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      dsimp [truncation, SimplicialObject.truncation, inclusion, tr]
      rw [push_yonedaEquiv _ _ this]
      have : δ 1 ≫ δ 2 = δ 1 ≫ @δ 1 1 :=
        SimplexCategory.δ_comp_δ (n := 0) (i := 1) (j := 1) (le_refl 1)
      rw [this]
      apply push_yonedaEquiv
      rw [Equiv.symm_apply_apply]
      rfl
    h₁ := by
      rw [← e₁₂.h₁]
      have : yonedaEquiv.symm (e₁₂.simplex) = stdSimplex.δ 0 ≫ g := by
        rw [← aux0 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₀]
      dsimp [truncation, SimplicialObject.truncation, inclusion, tr]
      rw [push_yonedaEquiv _ _ this]
      have : δ 0 ≫ δ 0 = δ 0 ≫ @δ 1 1 :=
        (SimplexCategory.δ_comp_δ (n := 0) (i := 0) (j := 0) (le_refl 0)).symm
      rw [this]
      apply push_yonedaEquiv
      rw [Equiv.symm_apply_apply]
      rfl
  }
  exact {
    simplex := yonedaEquiv g
    h₀₁ := by
      have : yonedaEquiv.symm (e₀₁.simplex) = stdSimplex.δ 2 ≫ g := by
        rw [← aux1 e₀₁ e₁₂, comm, ← Category.assoc, horn₂₁.incl₂]
      have app_id : e₀₁.simplex = S.map (𝟙 _).op e₀₁.simplex :=
        Eq.symm (FunctorToTypes.map_id_apply S _)
      rw [app_id]
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
        len_mk, id_eq, Functor.comp_obj, fullSubcategoryInclusion.obj,
        Nat.reduceAdd, Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map] at *
      -- TODO write a push_yonedaEquiv equivalent that does the case where we
      -- would need id
      rw [push_yonedaEquiv _ _ this]
      rfl
    h₁₂ := by sorry
    h₀₂ := by sorry
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
    Nonempty (CompStruct e₀₂ e₂₃ e₀₃) := by
  have y0 : yonedaEquiv.symm f₀.simplex = stdSimplex.δ 0 ≫ g := by
    rw [← mcofork_up0, comm, ← Category.assoc, horn₃₁.incl₀]
  have y2 : yonedaEquiv.symm f₂.simplex = stdSimplex.δ 2 ≫ g := by
    rw [← mcofork_up2, comm, ← Category.assoc, horn₃₁.incl₂]
  have y3 : yonedaEquiv.symm f₃.simplex = stdSimplex.δ 3 ≫ g := by
    rw [← mcofork_up3, comm, ← Category.assoc, horn₃₁.incl₃]

  -- TODO state some nice general thm.
  have comp_edge {y₀ y₁ y₂ : ((truncation 2).obj S) _⦋0⦌₂}
      {e₀₁ : Edge y₀ y₁} {e₁₂ : Edge y₁ y₂} {e₀₂ : Edge y₀ y₂}
      (i j : ℕ)
      (Δ : CompStruct e₀₁ e₁₂ e₀₂)
      (y : yonedaEquiv.symm Δ.simplex = stdSimplex.δ 3 ≫ g):
      S.map (δ i).op (S.map (δ 1).op (yonedaEquiv g)) =
      S.map (δ j).op (Δ.simplex) := by
    sorry
  apply Nonempty.intro
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

section horn_from_horn_data32
open horn₃₂
namespace horn₃₂

variable {X : SSet} {f : ((truncation 2).obj X).Path 3}
variable (horn_data : Truncated.fill32.horn_data f)

def π (a : R) : (Δ[2] ⟶ X) := match a with
  | ⟨0, h⟩ => yonedaEquiv.symm horn_data.σ₀
  | ⟨1, h⟩ => yonedaEquiv.symm horn_data.σ₁
  | ⟨2, h⟩ => by contradiction
  | ⟨3, h⟩ => yonedaEquiv.symm horn_data.σ₃

-- The multicofork ⨿ Δ[1] ⇉ ⨿ Δ[2] → X defined by sending Δ[2]s to
-- each of the three simplices in the combinatorial `horn_data`
def multicofork_from_data : Limits.Multicofork multispan_index :=
  Limits.Multicofork.ofπ multispan_index X
    (π horn_data)
    (by
    rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals
      dsimp only [J, multispan_index, π, Fin.castSucc, Fin.pred,
        Fin.castAdd, Fin.subNat, Fin.castLE]
      rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
      congr 1
    . have : (f.interval 1 2).arrow 1 = f.arrow 2 := rfl
      rw [← horn_data.h₀, ← horn_data.h₁₀, Truncated.spine_arrow, mkOfSucc_2_1] at this
      exact this
    . have : (f.interval 1 2).arrow 0 = (f.interval 0 2).arrow 1 := rfl
      rw [← horn_data.h₃, ← horn_data.h₀, Truncated.spine_arrow,
        Truncated.spine_arrow, mkOfSucc_2_0, mkOfSucc_2_1] at this
      exact this
    . exact horn_data.h₁₂)

-- using the fact that Λ[3, 2] is the coequalizer gives a map Λ[3, 2] → X
def horn_from_data : Λ[3, 2].toSSet ⟶ X :=
  Limits.IsColimit.desc isMulticoeq (multicofork_from_data horn_data)

-- some commutations guaranteed by the multicofork diagram
abbrev R₀ : R := ⟨0, by omega⟩
abbrev R₁ : R := ⟨1, by omega⟩
abbrev R₃ : R := ⟨3, by omega⟩

lemma mcofork_up0 : ι₀ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₀ :=
  isMulticoeq.fac (multicofork_from_data horn_data) (.right R₀)

lemma mcofork_up1 : ι₁ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₁ :=
  isMulticoeq.fac (multicofork_from_data horn_data) (.right R₁)

lemma mcofork_up3 : ι₃ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₃ :=
  isMulticoeq.fac (multicofork_from_data horn_data) (.right R₃)

/-- Given a 3-simplex `g : Δ[3] → X` extending the map `horn_data : Λ[3, 2].toSSet → X` along
the inclusion Λ[3, 2] → Δ[3], there exists a 2-simplex satisfying the (3, 2)-filling property
(namely, `yonedaEquiv g`).
-/
def fill32_from_horn_extension (g : Δ[3] ⟶ X) (h : horn_from_data horn_data = Λ[3, 2].ι ≫ g) :
    ∃ σ : ((truncation 2).obj X) _⦋2⦌₂, Truncated.fill32.filling_simplex horn_data σ := by
  let σ := X.map (δ 2).op (yonedaEquiv g)
  use σ
  constructor
  <;> dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
      len_mk, id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
      Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
      fullSubcategoryInclusion.map]
  . have : yonedaEquiv.symm horn_data.σ₀ = stdSimplex.δ 0 ≫ g
        := by rw [← mcofork_up0 horn_data, h, ← Category.assoc, incl₀]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₀ this]
    apply congr_fun
    apply Prefunctor.congr_map
    apply (Opposite.op_inj_iff _ _).2
    exact @δ_comp_δ 1 0 1 (Fin.zero_le _)
  . have : yonedaEquiv.symm horn_data.σ₁ = stdSimplex.δ 1 ≫ g
        := by rw [← mcofork_up1 horn_data, h, ← Category.assoc, incl₁]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₁ this]
    apply congr_fun
    apply Prefunctor.congr_map
    apply (Opposite.op_inj_iff _ _).2
    exact @δ_comp_δ 1 1 1 (Fin.ge_of_eq rfl)
  . have : f.arrow 0 = (f.interval 0 2).arrow 0 := rfl
    rw [← horn_data.h₃, Truncated.spine_arrow, mkOfSucc_2_0] at this
    rw [this]
    dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
      len_mk, id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
      Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
      fullSubcategoryInclusion.map]
    have : yonedaEquiv.symm horn_data.σ₃ = stdSimplex.δ 3 ≫ g
        := by rw [← mcofork_up3 horn_data, h, ← Category.assoc, incl₃]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₃ this]
    apply congr_fun
    apply Prefunctor.congr_map
    apply (Opposite.op_inj_iff _ _).2
    symm; exact @δ_comp_δ 1 2 2 (Fin.ge_of_eq rfl)

end horn₃₂
end horn_from_horn_data32

def two_truncatation_of_qc_is_2_trunc_qc {X : SSet} [Quasicategory X] :
    Truncated.Quasicategory₂ ((truncation 2).obj X) where
  fill21 f := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp) (horn₂₁.horn_from_path f)
    let g' := yonedaEquiv g
    use g'
    ext i; fin_cases i
    all_goals
      dsimp only [Fin.isValue, Fin.zero_eta]
      rw [Truncated.spine_arrow]
      have f_id i : f.arrow i = X.map (𝟙 _).op (f.arrow i) := by aesop_cat
      rw [f_id]
      dsimp only [Nat.reduceAdd, truncation, SimplicialObject.truncation, inclusion,
        whiskeringLeft_obj_obj, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj,
        len_mk, id_eq, Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
    . have : yonedaEquiv.symm (f.arrow 0) = stdSimplex.δ 2 ≫ g := by
        rw [← horn₂₁.pushout_up1 f, h, ← Category.assoc, horn₂₁.incl₂]
      rw [mkOfSucc_2_0, push_yonedaEquiv _ (f.arrow 0) this, Category.id_comp]
    . dsimp only [Fin.mk_one, Fin.isValue]
      have : yonedaEquiv.symm (f.arrow 1) = stdSimplex.δ 0 ≫ g := by
        rw [← horn₂₁.pushout_up0 f, h, ← Category.assoc, horn₂₁.incl₀]
      rw [mkOfSucc_2_1, push_yonedaEquiv _ (f.arrow 1) this, Category.id_comp]
  fill31 horn_data := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one
      Fin.one_lt_last (horn₃₁.horn_from_data horn_data)
    exact horn₃₁.fill31_from_horn_extension horn_data g h
  fill32 horn_data := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling (by decide)
      (by decide) (horn₃₂.horn_from_data horn_data)
    exact horn₃₂.fill32_from_horn_extension horn_data g h
