import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.Quasicategory.Basic

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Horn

open Simplicial SimplexCategory
open CategoryTheory SimplexCategory.Truncated Truncated.Hom SimplicialObject
open SimplicialObject.Truncated

namespace SSet
namespace Truncated

-- TODO place this somewhere else
def diagonal {n m : ℕ} (h1 : 1 ≤ m := by omega) (h2 : n ≤ m := by omega)
  (X : Truncated m) : X _⦋n⦌ₘ ⟶ X _⦋1⦌ₘ
  := X.map (tr (SimplexCategory.diag n)).op

-- TODO cleanup and generalize if possible
def shortcut3 (X : Truncated 2) (f : Path X 3) (σ : X _⦋2⦌₂)
  (h : spine X 2 _ σ = f.interval 0 2) : Path X 2 where
  vertex i := match i with
    | 0 => f.vertex ⟨0, by linarith⟩
    | i => f.vertex ⟨i + 1, by omega⟩
  arrow i := match i with
    | 0 => diagonal _ _ X σ
    | i => f.arrow ⟨i + 1, by omega⟩
  arrow_src i := match i with
    | 0 => by
      dsimp only [Nat.reduceAdd, trunc, SimplicialObject.Truncated.trunc, incl,
        whiskeringLeft_obj_obj, len_mk, id_eq, Functor.comp_obj, Functor.op_obj, Fin.isValue, tr,
        diagonal, diag, Nat.cast_ofNat, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        Fin.castSucc_zero, Int.reduceNeg, Int.reduceMul, Int.reduceAdd, Int.reduceSub,
        Int.rawCast.eq_1, Int.cast_id, Nat.rawCast.eq_1, Int.cast_ofNat_Int, Int.ofNat_eq_coe,
        eq_mp_eq_cast, cast_eq, Fin.zero_eta]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, δ_one_mkOfLe 0 2 _]
      have : (spine X 2 _ σ).vertex 0 = f.vertex 0 := by rw [h]; rfl
      rw [← this]
      rfl
    | 1 => f.arrow_src 2
  arrow_tgt i := match i with
    | 0 => by
      dsimp only [Nat.reduceAdd, trunc, SimplicialObject.Truncated.trunc, incl,
        whiskeringLeft_obj_obj, len_mk, id_eq, Functor.comp_obj, Functor.op_obj, Fin.isValue, tr,
        diagonal, diag, Nat.cast_ofNat, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        Fin.succ_zero_eq_one, Int.reduceNeg, Int.reduceMul, Int.reduceAdd, Int.reduceSub,
        Int.rawCast.eq_1, Int.cast_id, Nat.rawCast.eq_1, Int.cast_ofNat_Int, Int.ofNat_eq_coe,
        eq_mp_eq_cast, cast_eq, Fin.zero_eta, Fin.val_one, Fin.reduceFinMk]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, δ_zero_mkOfLe 0 2 _]
      have : (spine X 2 _ σ).vertex 2 = f.vertex 2 := by rw [h]; rfl
      rw [← this]
      rfl
    | 1 => f.arrow_tgt 2

def shortcut0 (X : Truncated 2) (f : Path X 3) (σ : X _⦋2⦌₂)
  (h : spine X 2 _ σ = f.interval 1 2) : Path X 2 where
  vertex i := match i with
    | 2 => f.vertex ⟨3, by omega⟩
    | i => f.vertex ⟨i, by omega⟩
  arrow i := match i with
    | 1 => diagonal _ _ X σ
    | 0 => f.arrow ⟨0, by omega⟩
  arrow_src i := match i with
    | 1 => by
      dsimp [diagonal, diag, tr, trunc, SimplicialObject.Truncated.trunc, incl,
        whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op, Fin.castSucc, Fin.castAdd, Fin.castLE]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, δ_one_mkOfLe 0 2 _]
      have : (spine X 2 _ σ).vertex 0 = f.vertex 1 := by
        obtain ⟨h, _⟩ := Path.ext_iff.1 h
        rw [h]
        rfl
      dsimp at this
      rw [← this]
    | 0 => f.arrow_src 0
  arrow_tgt i := match i with
    | 1 => by
      dsimp [diagonal, diag, tr, trunc, SimplicialObject.Truncated.trunc, incl,
        whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op, Fin.castSucc, Fin.castAdd, Fin.castLE]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, δ_zero_mkOfLe 0 2 _]
      have : (spine X 2 _ σ).vertex 2 = f.vertex 3 := by
        obtain ⟨h, _⟩ := Path.ext_iff.1 h
        rw [h]
        rfl
      dsimp at this
      rw [← this]
    | 0 => f.arrow_tgt 0

def diagonal2 {X : Truncated 2} (σ : X _⦋2⦌₂) : X _⦋1⦌₂ := diagonal _ _ X σ

namespace fill31

structure adjacency {X : Truncated 2} (f : X.Path 3) where
  σ₃ : X _⦋2⦌₂
  σ₀ : X _⦋2⦌₂
  σ₂ : X _⦋2⦌₂
  h₃ : spine X 2 _ σ₃ = f.interval 0 2
  h₀ : spine X 2 _ σ₀ = f.interval 1 2
  h₂ : spine X 2 _ σ₂ = shortcut0 X f σ₀ h₀

structure adjacency' {X : Truncated 2} (f : X.Path 3) where
  σ₃ : X _⦋2⦌₂
  σ₀ : X _⦋2⦌₂
  σ₂ : X _⦋2⦌₂
  h₃ : spine X 2 _ σ₃ = f.interval 0 2
  h₀ : spine X 2 _ σ₀ = f.interval 1 2
  h₂₀ : X.map (tr (SimplexCategory.δ 2)).op σ₂ = f.arrow 0
  h₂₁ : X.map (tr (SimplexCategory.δ 0)).op σ₂ = X.map (tr (SimplexCategory.δ 1)).op σ₀

end fill31

structure Quasicategory₂ (X : Truncated 2) where
  fill21 (f : Path X 2) : ∃ (σ : X _⦋2⦌₂), spine X 2 _ σ = f
  fill31 (f : Path X 3) (a : fill31.adjacency f)
    : ∃ (σ₁ : X _⦋2⦌₂), spine X 2 _ σ₁ = shortcut3 X f a.σ₃ a.h₃
      ∧ (diagonal2 σ₁ = diagonal2 a.σ₂)
  fill32 (f : Path X 3)
    (σ₃ : X _⦋2⦌₂) (h₃ : spine X 2 _ σ₃ = f.interval 0 2)
    (σ₀ : X _⦋2⦌₂) (h₀ : spine X 2 _ σ₀ = f.interval 1 2)
    (σ₁ : X _⦋2⦌₂) (h₁ : spine X 2 _ σ₁ = shortcut3 X f σ₃ h₃)
    : ∃ (σ₂ : X _⦋2⦌₂), spine X 2 _ σ₂ = shortcut0 X f σ₀ h₀
      ∧ (diagonal2 σ₂ = diagonal2 σ₁)

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

section multicofork
open horn₃₁

variable {X : SSet} {f : ((truncation 2).obj X).Path 3}
variable (adj_data : Truncated.fill31.adjacency' f)

def π (a : horn₃₁.R) : (Δ[2] ⟶ X) := match a with
  | ⟨0, h⟩ => yonedaEquiv.symm adj_data.σ₀
  | ⟨1, h⟩ => by contradiction
  | ⟨2, h⟩ => yonedaEquiv.symm adj_data.σ₂
  | ⟨3, h⟩ => yonedaEquiv.symm adj_data.σ₃

--lemma multicofork_comm (a : J.L) :
--  multispan_index.fst a ≫ π σ₃ σ₀ σ₂ (J.fst a) = multispan_index.snd a ≫ π σ₃ σ₀ σ₂ (J.snd a)
--  := by sorry

-- TODO sorry
def multicofork_from_data : Limits.Multicofork horn₃₁.multispan_index
    := Limits.Multicofork.ofπ horn₃₁.multispan_index X
      (π adj_data)
      (by
      have simplicial₁ : @mkOfSucc 2 0 = SimplexCategory.δ 2 := by
          ext i
          fin_cases i <;> aesop
      have simplicial₂ : @mkOfSucc 2 1 = SimplexCategory.δ 0 := by
        ext i
        fin_cases i <;> aesop
      rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp only [J, multispan_index, π, Fin.castSucc, Fin.pred,
          Fin.castAdd, Fin.subNat, Fin.castLE]
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      -- TODO collect useful identities for mkOfSucc, diag for 2-simplices
      . symm; exact adj_data.h₂₁
      . have : (f.interval 1 2).arrow 0 = (f.interval 0 2).arrow 1 := rfl
        rw [← adj_data.h₃, ← adj_data.h₀, Truncated.spine_arrow,
          Truncated.spine_arrow, simplicial₁, simplicial₂] at this
        exact this
      . have : f.arrow 0 = (f.interval 0 2).arrow 0 := rfl
        rw [← adj_data.h₃, ← adj_data.h₂₀, Truncated.spine_arrow,
          simplicial₁] at this
        exact this
    )

#check multicofork_from_data

def horn_from_path3 : Λ[3, 1].toSSet ⟶ X := Limits.IsColimit.desc horn₃₁.isMulticoeq
  (multicofork_from_data adj_data)

#check horn_from_path3

abbrev R₀ : horn₃₁.R := ⟨0, by omega⟩
abbrev R₂ : horn₃₁.R := ⟨2, by omega⟩
abbrev R₃ : horn₃₁.R := ⟨3, by omega⟩

lemma mcofork_up0' : horn₃₁.ι₀ ≫ (horn_from_path3 adj_data) = yonedaEquiv.symm adj_data.σ₀
  := horn₃₁.isMulticoeq.fac (multicofork_from_data adj_data) (.right R₀)

lemma mcofork_up2' : horn₃₁.ι₂ ≫ (horn_from_path3 adj_data) = yonedaEquiv.symm adj_data.σ₂
  := horn₃₁.isMulticoeq.fac (multicofork_from_data adj_data) (.right R₂)

lemma mcofork_up3' : horn₃₁.ι₃ ≫ (horn_from_path3 adj_data) = yonedaEquiv.symm adj_data.σ₃
  := horn₃₁.isMulticoeq.fac (multicofork_from_data adj_data) (.right R₃)

end multicofork

lemma two_truncatation_of_qc_is_2_trunc_qc {X : SSet} [Quasicategory X] :
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
  fill31 adj_data := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling Fin.zero_lt_one (by simp) (horn_from_path3 σ₃ σ₀ σ₂)
    let g' := X.map (SimplexCategory.δ 1).op (yonedaEquiv g)
    use g'
    constructor
    . ext i
      fin_cases i
      . dsimp [Truncated.shortcut3, truncation_spine, Truncated.Path.arrow, Truncated.diagonal]
        dsimp [truncation, SimplicialObject.truncation, inclusion, tr]
        unfold g'
        rw [← FunctorToTypes.map_comp_apply, ← op_comp]
        have : yonedaEquiv.symm σ₃ = horn₃₁.ι₃ ≫ Λ[3, 1].ι ≫ g := by rw [← mcofork_up3' σ₃ σ₀ σ₂, h]
        rw [push_yonedaEquiv _ σ₃ this]
        have : mkOfSucc 0 ≫ SimplexCategory.δ 1 = diag 2 ≫ SimplexCategory.δ 3 := by
          ext i
          fin_cases i <;> aesop
        rw [this]
        rfl
      . dsimp [Truncated.shortcut3, truncation_spine, Truncated.Path.arrow, Truncated.diagonal]
        dsimp [truncation, SimplicialObject.truncation, inclusion, tr]
        unfold g'
        rw [← FunctorToTypes.map_comp_apply, ← op_comp]
        have : Truncated.Path₁.arrow f 2 = X.map (SimplexCategory.δ 0).op σ₀ := by
          have : Truncated.Path₁.arrow f 2 = (f.interval 1 2).arrow 1 := by
            dsimp only [Truncated.Path.interval, Truncated.Path.arrow]; rfl
          rw [this, ← h₀]
          rw [Truncated.spine_arrow]
          dsimp [truncation, SimplicialObject.truncation, inclusion, tr]
          --TODO this is a nice general congruence we should use elsewhere
          apply congr_fun
          apply Prefunctor.congr_map
          apply (Opposite.op_inj_iff _ _).2
          ext i; fin_cases i <;> aesop
        rw [this]
        have : yonedaEquiv.symm σ₀ = horn₃₁.ι₀ ≫ Λ[3, 1].ι ≫ g := by rw [← mcofork_up0' σ₃ σ₀ σ₂, h]
        rw [push_yonedaEquiv _ σ₀ this]
        have : mkOfSucc 1 ≫ SimplexCategory.δ 1 = SimplexCategory.δ 3 ≫ SimplexCategory.δ 0 := by
          ext i
          fin_cases i <;> aesop
        rw [this]
        rfl
    . dsimp [Truncated.diagonal2, Truncated.diagonal, truncation, SimplicialObject.truncation, inclusion, tr]
      have : yonedaEquiv.symm σ₂ = horn₃₁.ι₂ ≫ Λ[3, 1].ι ≫ g := by rw [← mcofork_up2' σ₃ σ₀ σ₂, h]
      unfold g'
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      rw [push_yonedaEquiv _ σ₂ this]
      have : diag 2 ≫ SimplexCategory.δ 1 = diag 2 ≫ SimplexCategory.δ 2 := by
        ext i
        fin_cases i <;> aesop
      rw [this]
      rfl
  fill32 := sorry
