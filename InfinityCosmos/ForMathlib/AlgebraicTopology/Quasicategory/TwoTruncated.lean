import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.Quasicategory.Basic

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn

open Simplicial SimplexCategory
open CategoryTheory SimplexCategory.Truncated Truncated.Hom SimplicialObject
open SimplicialObject.Truncated

-- TODO should these go into the SimplexCategory.Basics file?
namespace SimplexCategory

lemma mkOfSucc_2_0 : @mkOfSucc 2 0 = SimplexCategory.δ 2 := by ext i; fin_cases i <;> rfl
lemma mkOfSucc_2_1 : @mkOfSucc 2 1 = SimplexCategory.δ 0 := by ext i; fin_cases i <;> rfl

end SimplexCategory

namespace SSet
namespace Truncated

-- TODO place this somewhere else
def diagonal {n m : ℕ} (h1 : 1 ≤ m := by omega) (h2 : n ≤ m := by omega)
  (X : Truncated m) : X _⦋n⦌ₘ ⟶ X _⦋1⦌ₘ
  := X.map (tr (SimplexCategory.diag n)).op

def diagonal2 {X : Truncated 2} (σ : X _⦋2⦌₂) : X _⦋1⦌₂ := diagonal _ _ X σ

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
  h₂₂ : X.map (tr (SimplexCategory.δ 2)).op σ₂ = f.arrow 0
  h₂₀ : X.map (tr (SimplexCategory.δ 0)).op σ₂ = X.map (tr (SimplexCategory.δ 1)).op σ₀

/--
Given a path `f` of length 3 in a 2-truncated simplicial set `X` and
horn_data `a`, `filling_simplex a σ` is the proposition that `σ` is a 2-simplex
that "fills in" the missing face of the horn defined by `a`. This is the (3, 1)-filling property.
-/
structure filling_simplex {X : Truncated 2} {f : X.Path 3} (a : horn_data f) (σ : X _⦋2⦌₂) : Prop where
  edge₀ : X.map (tr (SimplexCategory.δ 0)).op σ = f.arrow 2
  edge₁ : X.map (tr (SimplexCategory.δ 1)).op σ = X.map (tr (SimplexCategory.δ 1)).op a.σ₂
  edge₂ : X.map (tr (SimplexCategory.δ 2)).op σ = X.map (tr (SimplexCategory.δ 1)).op a.σ₃

-- TODO more lemmas or delete this
lemma arrow_2_eq_edge_σ₀ {X : Truncated 2} {f : X.Path 3} {a : horn_data f}
  : f.arrow 2 = X.map (SimplexCategory.δ 0).op a.σ₀ := by
  have : f.arrow 2 = (f.interval 1 2).arrow 1 := rfl
  rw [← a.h₀, spine_arrow, mkOfSucc_2_1] at this
  exact this

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
  h₁₂ : X.map (tr (SimplexCategory.δ 2)).op σ₁ = X.map (tr (SimplexCategory.δ 1)).op σ₃
  h₁₀ : X.map (tr (SimplexCategory.δ 0)).op σ₁ = f.arrow 2

/--
Given a path `f` of length 3 in a 2-truncated simplicial set `X` and
horn_data `a`, `filling_simplex a σ` is the proposition that `σ` is a 2-simplex
that "fills in" the missing face of the horn defined by `a`. This is the (3, 1)-filling property.
-/
structure filling_simplex {X : Truncated 2} {f : X.Path 3} (a : horn_data f) (σ : X _⦋2⦌₂) : Prop where
  edge₀ : X.map (tr (SimplexCategory.δ 0)).op σ = X.map (tr (SimplexCategory.δ 1)).op a.σ₀
  edge₁ : X.map (tr (SimplexCategory.δ 1)).op σ = X.map (tr (SimplexCategory.δ 1)).op a.σ₁
  edge₂ : X.map (tr (SimplexCategory.δ 2)).op σ = f.arrow 0
end fill32

structure Quasicategory₂ (X : Truncated 2) where
  fill21 (f : Path X 2) : ∃ (σ : X _⦋2⦌₂), spine X 2 _ σ = f
  fill31 {f : Path X 3} (a : fill31.horn_data f) : ∃ σ₁ : X _⦋2⦌₂, fill31.filling_simplex a σ₁
  fill32 {f : Path X 3} (a : fill32.horn_data f) : ∃ σ₁ : X _⦋2⦌₂, fill32.filling_simplex a σ₁

end Truncated

open horn₂₁

def path_edge₀ {X : SSet} (f : Path X 2) : Δ[1] ⟶ X := yonedaEquiv.symm (f.arrow 1)
def path_edge₂ {X : SSet} (f : Path X 2) : Δ[1] ⟶ X := yonedaEquiv.symm (f.arrow 0)

section aux_lemmata_horn21
open SimplexCategory

-- TODO cleanup proof
lemma map_yonedaEquiv {n m : ℕ} {X : SSet} (f : .mk n ⟶ .mk m) (g : Δ[m] ⟶ X) : X.map f.op (yonedaEquiv g)
  = g.app (Opposite.op (mk n)) (stdSimplex.objEquiv.symm f)
  := by
  have g_nat := g.naturality f.op
  let id_m : (mk m) ⟶ (mk m) := SimplexCategory.Hom.id (mk m)
  have : yonedaEquiv g = g.app (Opposite.op (mk m)) (stdSimplex.objEquiv.symm id_m) := rfl
  rw [this]
  have : X.map f.op (g.app (Opposite.op (mk m)) (stdSimplex.objEquiv.symm id_m)) =
    (g.app (Opposite.op (mk m)) ≫ X.map f.op) (stdSimplex.objEquiv.symm id_m) := rfl
  rw [← g_nat] at this
  rw [this]
  -- TODO stdSimplex.map_id is probably helpful here
  have : Δ[m].map f.op (stdSimplex.objEquiv.symm id_m) = stdSimplex.objEquiv.symm f := by aesop_cat
  dsimp
  rw [this]
  rfl

lemma push_yonedaEquiv {n m k : ℕ} {X : SSet} (f : .mk n ⟶ .mk m) (σ : X.obj (Opposite.op (.mk m)))
    {s : .mk m ⟶ .mk k} {g : Δ[k] ⟶ X}
    (h : yonedaEquiv.symm σ = stdSimplex.map s ≫ g)
  : X.map f.op σ = X.map (f ≫ s).op (yonedaEquiv g)
  := by
    rw [← Equiv.apply_symm_apply yonedaEquiv σ, h]
    have : yonedaEquiv (stdSimplex.map s ≫ g) = X.map s.op (yonedaEquiv g) := by
      rw [yonedaEquiv_comp, map_yonedaEquiv, stdSimplex.yonedaEquiv_map]
    rw [this, ← FunctorToTypes.map_comp_apply, ← op_comp]

lemma map_comp_yonedaEquiv_symm {n m : ℕ} {X : SSet} (f : .mk n ⟶ .mk m) (s : X.obj (.op (.mk m)))
  : stdSimplex.map f ≫ yonedaEquiv.symm s = yonedaEquiv.symm (X.map f.op s) := by
    apply yonedaEquiv.apply_eq_iff_eq_symm_apply.1
    let s' := yonedaEquiv.symm s
    have : s = yonedaEquiv s' := (Equiv.symm_apply_eq yonedaEquiv).mp rfl
    rw [this, map_yonedaEquiv, yonedaEquiv_comp, Equiv.apply_symm_apply yonedaEquiv _,
      stdSimplex.yonedaEquiv_map]

def path_edges_comm {X : SSet} {f : SSet.Path X 2} : pt₁ ≫ path_edge₀ f = pt₀ ≫ path_edge₂ f := by
    dsimp only [pt₀, pt₁, path_edge₀, path_edge₂]
    rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm, f.arrow_src 1, f.arrow_tgt 0]
    rfl

def horn_from_path {X : SSet} (f : SSet.Path X 2) : Λ[2, 1].toSSet ⟶ X
  := Limits.PushoutCocone.IsColimit.desc horn_is_pushout (path_edge₀ f) (path_edge₂ f)
    path_edges_comm
end aux_lemmata_horn21

section horn_from_horn_data31
open horn₃₁
namespace horn₃₁

variable {X : SSet} {f : ((truncation 2).obj X).Path 3}
variable (horn_data : Truncated.fill31.horn_data f)

def π (a : horn₃₁.R) : (Δ[2] ⟶ X) := match a with
  | ⟨0, h⟩ => yonedaEquiv.symm horn_data.σ₀
  | ⟨1, h⟩ => by contradiction
  | ⟨2, h⟩ => yonedaEquiv.symm horn_data.σ₂
  | ⟨3, h⟩ => yonedaEquiv.symm horn_data.σ₃

-- The multicofork ⨿ Δ[1] ⇉ ⨿ Δ[2] → X defined by sending Δ[2]s to
-- each of the three simplices in the combinatorial `horn_data`
def multicofork_from_data : Limits.Multicofork multispan_index
    := Limits.Multicofork.ofπ multispan_index X
      (π horn_data)
      (by
      rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp only [J, multispan_index, π, Fin.castSucc, Fin.pred,
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

lemma mcofork_up0 : horn₃₁.ι₀ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₀
  := horn₃₁.isMulticoeq.fac (multicofork_from_data horn_data) (.right R₀)

lemma mcofork_up2 : horn₃₁.ι₂ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₂
  := horn₃₁.isMulticoeq.fac (multicofork_from_data horn_data) (.right R₂)

lemma mcofork_up3 : horn₃₁.ι₃ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₃
  := horn₃₁.isMulticoeq.fac (multicofork_from_data horn_data) (.right R₃)

/-- Given a 3-simplex `g : Δ[3] → X` extending the map `horn_data : Λ[3, 1].toSSet → X` along
the inclusion Λ[3, 1] → Δ[3], there exists a 2-simplex satisfying the (3, 1)-filling property
(namely, `yonedaEquiv g`).
-/
def fill31_from_horn_extension (g : Δ[3] ⟶ X) (h : horn_from_data horn_data = Λ[3, 1].ι ≫ g)
  : ∃ σ : ((truncation 2).obj X) _⦋2⦌₂, Truncated.fill31.filling_simplex horn_data σ
  := by
  let σ := X.map (SimplexCategory.δ 1).op (yonedaEquiv g)
  use σ
  constructor
  . have arr : f.arrow 2 = (f.interval 1 2).arrow 1 := rfl
    rw [arr, ← horn_data.h₀, Truncated.spine_arrow, mkOfSucc_2_1]
    dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj, len_mk,
      id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
      Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
      fullSubcategoryInclusion.map]
    have : yonedaEquiv.symm horn_data.σ₀ = stdSimplex.δ 0 ≫ g
        := by rw [← mcofork_up0 horn_data, h, ← Category.assoc, horn₃₁.incl₀]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₀ this]
    rfl
  . dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj, len_mk,
      id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
      Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
      fullSubcategoryInclusion.map]
    have : yonedaEquiv.symm horn_data.σ₂ = stdSimplex.δ 2 ≫ g
        := by rw [← mcofork_up2 horn_data, h, ← Category.assoc, horn₃₁.incl₂]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₂ this]
    apply congr_fun
    apply Prefunctor.congr_map
    apply (Opposite.op_inj_iff _ _).2
    symm; exact @SimplexCategory.δ_comp_δ 1 1 1 (by norm_num)
  . dsimp only [truncation, SimplicialObject.truncation, inclusion, whiskeringLeft_obj_obj, len_mk,
      id_eq, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj, Nat.reduceAdd,
      Fin.isValue, tr, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
      fullSubcategoryInclusion.map]
    have : yonedaEquiv.symm horn_data.σ₃ = stdSimplex.δ 3 ≫ g
        := by rw [← mcofork_up3 horn_data, h, ← Category.assoc, horn₃₁.incl₃]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₃ this]
    apply congr_fun
    apply Prefunctor.congr_map
    apply (Opposite.op_inj_iff _ _).2
    symm; exact @SimplexCategory.δ_comp_δ 1 1 2 (by apply Fin.le_iff_val_le_val.2; norm_num)

end horn₃₁
end horn_from_horn_data31

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
def multicofork_from_data : Limits.Multicofork multispan_index
    := Limits.Multicofork.ofπ multispan_index X
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
      . exact horn_data.h₁₂
    )

-- using the fact that Λ[3, 2] is the coequalizer gives a map Λ[3, 2] → X
def horn_from_data : Λ[3, 2].toSSet ⟶ X := Limits.IsColimit.desc isMulticoeq
  (multicofork_from_data horn_data)

-- some commutations guaranteed by the multicofork diagram
abbrev R₀ : R := ⟨0, by omega⟩
abbrev R₁ : R := ⟨1, by omega⟩
abbrev R₃ : R := ⟨3, by omega⟩

lemma mcofork_up0 : ι₀ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₀
  := isMulticoeq.fac (multicofork_from_data horn_data) (.right R₀)

lemma mcofork_up1 : ι₁ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₁
  := isMulticoeq.fac (multicofork_from_data horn_data) (.right R₁)

lemma mcofork_up3 : ι₃ ≫ (horn_from_data horn_data) = yonedaEquiv.symm horn_data.σ₃
  := isMulticoeq.fac (multicofork_from_data horn_data) (.right R₃)

/-- Given a 3-simplex `g : Δ[3] → X` extending the map `horn_data : Λ[3, 2].toSSet → X` along
the inclusion Λ[3, 2] → Δ[3], there exists a 2-simplex satisfying the (3, 2)-filling property
(namely, `yonedaEquiv g`).
-/
def fill32_from_horn_extension (g : Δ[3] ⟶ X) (h : horn_from_data horn_data = Λ[3, 2].ι ≫ g)
  : ∃ σ : ((truncation 2).obj X) _⦋2⦌₂, Truncated.fill32.filling_simplex horn_data σ
  := by
  let σ := X.map (SimplexCategory.δ 2).op (yonedaEquiv g)
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
    exact @SimplexCategory.δ_comp_δ 1 0 1 (Fin.zero_le _)
  . have : yonedaEquiv.symm horn_data.σ₁ = stdSimplex.δ 1 ≫ g
        := by rw [← mcofork_up1 horn_data, h, ← Category.assoc, incl₁]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, push_yonedaEquiv _ horn_data.σ₁ this]
    apply congr_fun
    apply Prefunctor.congr_map
    apply (Opposite.op_inj_iff _ _).2
    exact @SimplexCategory.δ_comp_δ 1 1 1 (Fin.ge_of_eq rfl)
  .
    have : f.arrow 0 = (f.interval 0 2).arrow 0 := rfl
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
    symm; exact @SimplexCategory.δ_comp_δ 1 2 2 (Fin.ge_of_eq rfl)

end horn₃₂
end horn_from_horn_data32

def two_truncatation_of_qc_is_2_trunc_qc {X : SSet} [Quasicategory X] :
  Truncated.Quasicategory₂ ((truncation 2).obj X) where
  fill21 f := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp) (horn_from_path f)
    let g' := yonedaEquiv g
    use g'
    ext i
    fin_cases i
    . dsimp only [Fin.isValue, Fin.zero_eta]
      rw [truncation_spine]
      . simp [@Truncated.spine_arrow 1 _ 1 (by norm_num)]
        have h₂ : X.map (mkOfSucc 0).op g' = yonedaEquiv (hornTwo_edge₂ ≫ Λ[2, 1].ι ≫ g)
          := by
          have map_yoneda : X.map (mkOfSucc 0).op g' = g.app (Opposite.op (mk 1))
            (stdSimplex.objEquiv.symm (mkOfSucc 0))
            := map_yonedaEquiv (mkOfSucc 0) g
          have mkOfSucc_δ : (@mkOfSucc 2 0) = SimplexCategory.δ 2 := by ext x; fin_cases x <;> aesop
          rw [map_yoneda, mkOfSucc_δ, ← Category.assoc]
          rfl
        rw [h₂]
        have : f.arrow 0 = yonedaEquiv (path_edge₂ f) := by
          unfold path_edge₂
          exact (Equiv.symm_apply_eq yonedaEquiv).mp rfl
        rw [this]
        apply yonedaEquiv.congr_arg
        simp at h
        rw [← h]
        exact CategoryTheory.Limits.PushoutCocone.IsColimit.inr_desc
          horn_is_pushout (path_edge₀ f) (path_edge₂ f) path_edges_comm
      norm_num
    -- TODO finish i = 1 case, even better: generalize so same general thm holds for both cases
    . sorry
  fill31 horn_data := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one
      Fin.one_lt_last (horn₃₁.horn_from_data horn_data)
    exact horn₃₁.fill31_from_horn_extension horn_data g h
  fill32 horn_data := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling (by decide)
      (by decide) (horn₃₂.horn_from_data horn_data)
    exact horn₃₂.fill32_from_horn_extension horn_data g h
