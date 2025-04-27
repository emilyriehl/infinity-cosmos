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
end horn_from_horn_data21

section horn_from_horn_data31
open SSet.horn₃₁
namespace horn₃₁

variable {X : SSet} {f : ((truncation 2).obj X).Path 3}
variable (horn_data : Truncated.fill31.horn_data f)

def π2 (a : horn₃₁.R) : (Δ[2] ⟶ X) := match a with
  | ⟨0, h⟩ => yonedaEquiv.symm horn_data.σ₀
  | ⟨1, h⟩ => by contradiction
  | ⟨2, h⟩ => yonedaEquiv.symm horn_data.σ₂
  | ⟨3, h⟩ => yonedaEquiv.symm horn_data.σ₃

-- The multicofork ⨿ Δ[1] ⇉ ⨿ Δ[2] → X defined by sending Δ[2]s to
-- each of the three simplices in the combinatorial `horn_data`
def multicofork_from_data : Limits.Multicofork multispan_index
    := Limits.Multicofork.ofπ multispan_index X
      (π2 horn_data)
      (by
      rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp only [J, multispan_index, π2, Fin.castSucc, Fin.pred,
          Fin.castAdd, Fin.subNat, Fin.castLE]
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      . symm; exact horn_data.h₂₀
      . have : (f.interval 1 2).arrow 0 = (f.interval 0 2).arrow 1 := rfl
        rw [← horn_data.h₃, ← horn_data.h₀, Truncated.spine_arrow,
          Truncated.spine_arrow, mkOfSucc_2_0, mkOfSucc_2_1] at this
        exact this
      . have : f.arrow 0 = (f.interval 0 2).arrow 0 := rfl
        rw [← horn_data.h₃, ← horn_data.h₂₂, Truncated.spine_arrow, mkOfSucc_2_0] at this
        exact this
    )

-- using the fact that Λ[3, 1] is the coequalizer gives a map Λ[3, 1] → X
def horn_from_data : Λ[3, 1].toSSet ⟶ X := Limits.IsColimit.desc horn₃₁.isMulticoeq
  (multicofork_from_data horn_data)

-- some commutations guaranteed by the multicofork diagram
abbrev R₀ : horn₃₁.R := ⟨0, by omega⟩
abbrev R₂ : horn₃₁.R := ⟨2, by omega⟩
abbrev R₃ : horn₃₁.R := ⟨3, by omega⟩

lemma mcofork_up0 : horn₃₁.ι₀ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₀ :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data horn_data) (.right R₀)

lemma mcofork_up2 : horn₃₁.ι₂ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₂ :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data horn_data) (.right R₂)

lemma mcofork_up3 : horn₃₁.ι₃ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₃ :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data horn_data) (.right R₃)

/-- Given a 3-simplex `g : Δ[3] → X` extending the map `horn_data : Λ[3, 1].toSSet → X` along
the inclusion Λ[3, 1] → Δ[3], there exists a 2-simplex satisfying the (3, 1)-filling property
(namely, `yonedaEquiv g`).
-/
def fill31_from_horn_extension (g : Δ[3] ⟶ X) (h : horn_from_data horn_data = Λ[3, 1].ι ≫ g) :
  ∃ σ : ((truncation 2).obj X) _⦋2⦌₂, Truncated.fill31.filling_simplex horn_data σ := by
  let σ := X.map (δ 1).op (yonedaEquiv g)
  use σ
  exact {
    edge₀ := by
      have arr : f.arrow 2 = (f.interval 1 2).arrow 1 := rfl
      rw [arr, ← horn_data.h₀, Truncated.spine_arrow, mkOfSucc_2_1]
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj, len_mk,
        id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
        Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      have : yonedaEquiv.symm horn_data.σ₀ = stdSimplex.δ 0 ≫ g
          := by rw [← mcofork_up0 horn_data, h, ← Category.assoc, horn₃₁.incl₀]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₀ this]
      rfl
    edge₁ := by
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj, len_mk,
        id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
        Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      have : yonedaEquiv.symm horn_data.σ₂ = stdSimplex.δ 2 ≫ g
          := by rw [← mcofork_up2 horn_data, h, ← Category.assoc, horn₃₁.incl₂]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₂ this]
      apply congr_fun
      apply Prefunctor.congr_map
      apply (Opposite.op_inj_iff _ _).2
      symm; exact @δ_comp_δ 1 1 1 (by norm_num)
    edge₂ := by
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj, len_mk,
        id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
        Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      have : yonedaEquiv.symm horn_data.σ₃ = stdSimplex.δ 3 ≫ g
          := by rw [← mcofork_up3 horn_data, h, ← Category.assoc, horn₃₁.incl₃]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₃ this]
      apply congr_fun
      apply Prefunctor.congr_map
      apply (Opposite.op_inj_iff _ _).2
      symm; exact @δ_comp_δ 1 1 2 (by apply Fin.le_iff_val_le_val.2; norm_num)
  }
end horn₃₁
end horn_from_horn_data31

/- define the structures Edge and CompStruct for a 2-truncated simplicial set `X : Truncated 2`
  and vertices `x₀`, ..., `x₃`
-/
section comp_struct
variable {X : Truncated 2}
variable {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}

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

section fill31_comp_struct

variable {S : SSet}
variable
    {x₀ x₁ x₂ x₃ : ((truncation 2).obj S) _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂)
    (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₁ e₁₃ e₀₃)

include S x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃ h₀₂ h₁₃ h
open horn₃₁
#check horn₃₁.multispan_index

/- steps of constructing fill31' from (g : Δ[3] ⟶ X):
  . construct a multicofork from the given CompStructs
  . construct a map h : Λ[3, 1] ⟶ X such that h = Λ[3, 1].ι ≫ g
  . make a CompStruct with simplex given by g, prove equalities
-/
def π' (a : R) : (Δ[2] ⟶ S) := match a with
  | ⟨0, _⟩ => yonedaEquiv.symm h₁₃.simplex
  | ⟨1, _⟩ => by contradiction
  | ⟨2, _⟩ => yonedaEquiv.symm h.simplex
  | ⟨3, _⟩ => yonedaEquiv.symm h₀₂.simplex

-- The multicofork ⨿ Δ[1] ⇉ ⨿ Δ[2] → X defined by sending Δ[2]s to
-- each of the three simplices in the combinatorial `horn_data`
def multicofork_from_data : Limits.Multicofork multispan_index :=
  Limits.Multicofork.ofπ multispan_index S
    (π' h₀₂ h₁₃ h)
    (by
      rintro ⟨⟨⟨i, i_ne_1⟩, ⟨j, j_ne_1⟩⟩, i_lt_j⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp [J, multispan_index, π']
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      -- rw doesn't work because the statement is about `SSet`, not `Truncated 2`
      . apply Eq.trans
        exact h₁₃.h₀₂
        symm; exact h.h₁₂
      . apply Eq.trans
        exact h₁₃.h₀₁
        symm; exact h₀₂.h₁₂
      . apply Eq.trans
        exact h.h₀₁
        symm; exact h₀₂.h₀₁)

-- using the fact that Λ[3, 1] is the coequalizer gives a map Λ[3, 1] → X
def horn_from_data : Λ[3, 1].toSSet ⟶ S := Limits.IsColimit.desc horn₃₁.isMulticoeq
  (multicofork_from_data h₀₂ h₁₃ h)

-- TODO rename these to something more useful
lemma mcofork_up0 : horn₃₁.ι₀ ≫ (horn_from_data h₀₂ h₁₃ h) = yonedaEquiv.symm h₁₃.simplex :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data h₀₂ h₁₃ h) (.right R₀)

lemma mcofork_up2 : horn₃₁.ι₂ ≫ (horn_from_data h₀₂ h₁₃ h) = yonedaEquiv.symm h.simplex :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data h₀₂ h₁₃ h) (.right R₂)

lemma mcofork_up3 : horn₃₁.ι₃ ≫ (horn_from_data h₀₂ h₁₃ h) = yonedaEquiv.symm h₀₂.simplex :=
  horn₃₁.isMulticoeq.fac (multicofork_from_data h₀₂ h₁₃ h) (.right R₃)

-- TODO add congruence lemma?
def fill31_from_horn_extension'
    (g : Δ[3] ⟶ S)
    (comm : horn_from_data h₀₂ h₁₃ h = Λ[3, 1].ι ≫ g) :
    Nonempty (CompStruct e₀₂ e₂₃ e₀₃) := by
  have y0 : yonedaEquiv.symm h₁₃.simplex = stdSimplex.δ 0 ≫ g := by
    rw [← mcofork_up0, comm, ← Category.assoc, horn₃₁.incl₀]
  have y2 : yonedaEquiv.symm h.simplex = stdSimplex.δ 2 ≫ g := by
    rw [← mcofork_up2, comm, ← Category.assoc, horn₃₁.incl₂]
  have y3 : yonedaEquiv.symm h₀₂.simplex = stdSimplex.δ 3 ≫ g := by
    rw [← mcofork_up3, comm, ← Category.assoc, horn₃₁.incl₃]
  apply Nonempty.intro
  exact {
    simplex := S.map (δ 1).op (yonedaEquiv g)
    h₀₁ := by
      rw [← h₀₂.h₀₂]
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
        len_mk, id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj,
        Nat.reduceAdd, Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ _ y3]
      apply congr_fun
      apply Prefunctor.congr_map
      apply (Opposite.op_inj_iff _ _).2
      symm; exact @δ_comp_δ _ 1 2 (by apply Fin.le_iff_val_le_val.2; norm_num)
    h₁₂ := by
      rw [← h₁₃.h₁₂]
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
      rw [← h.h₀₂]
      dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj,
        len_mk, id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj,
        Nat.reduceAdd, Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        fullSubcategoryInclusion.map]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ _ y2]
      apply congr_fun
      apply Prefunctor.congr_map
      apply (Opposite.op_inj_iff _ _).2
      symm; exact @δ_comp_δ _ 1 1 (le_refl 1)
  }

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
