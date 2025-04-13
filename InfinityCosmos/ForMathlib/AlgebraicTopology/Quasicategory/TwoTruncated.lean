import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.Quasicategory.Basic

open SimplexCategory
open CategoryTheory SimplexCategory.Truncated Truncated.Hom SimplicialObject
open SimplicialObject.Truncated

namespace SSet
namespace Truncated


def diagonal {n m : ℕ} (h1 : 1 ≤ m := by omega) (h2 : n ≤ m := by omega)
  (X : Truncated m) : X _⦋n⦌ₘ ⟶ X _⦋1⦌ₘ
  := X.map (tr (SimplexCategory.diag n)).op

-- TODO these next two should probably go into the file where δ_zero_mkOfSucc live
-- same proof as δ_zero_mkOfSucc
def δ_zero_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 0 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) j := by
  ext x
  fin_cases x
  aesop

-- same proof as δ_one_mkOfSucc
def δ_one_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 1 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) i := by
  ext x
  fin_cases x
  aesop

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
      have : (spine X 2 _ σ).vertex 0 = f.vertex 0 := by
        obtain ⟨h, _⟩ := Path.ext_iff.1 h
        rw [h]
        rfl
      dsimp only [Nat.reduceAdd, Nat.add_zero, len_mk, id_eq, Fin.isValue, spine_vertex] at this
      rw [← this]
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
      have : (spine X 2 _ σ).vertex 2 = f.vertex 2 := by
        obtain ⟨h, _⟩ := Path.ext_iff.1 h
        rw [h]
        rfl
      dsimp only [Nat.reduceAdd, Nat.add_zero, len_mk, id_eq, Fin.isValue, spine_vertex] at this
      rw [← this]
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

structure Quasicat (X : Truncated 2) where
  fill21 (f : Path X 2) : ∃ (σ : X _⦋2⦌₂), spine X 2 _ σ = f
  fill31 (f : Path X 3)
    (σ₃ : X _⦋2⦌₂) (h₃ : spine X 2 _ σ₃ = f.interval 0 2)
    (σ₀ : X _⦋2⦌₂) (h₀ : spine X 2 _ σ₀ = f.interval 1 2)
    (σ₂ : X _⦋2⦌₂) (h₂ : spine X 2 _ σ₂ = shortcut0 X f σ₀ h₀)
    : ∃ (σ₁ : X _⦋2⦌₂), spine X 2 _ σ₁ = shortcut3 X f σ₃ h₃
  fill32 (f : Path X 3)
    (σ₃ : X _⦋2⦌₂) (h₃ : spine X 2 _ σ₃ = f.interval 0 2)
    (σ₀ : X _⦋2⦌₂) (h₀ : spine X 2 _ σ₀ = f.interval 1 2)
    (σ₁ : X _⦋2⦌₂) (h₁ : spine X 2 _ σ₁ = shortcut3 X f σ₃ h₃)
    : ∃ (σ₂ : X _⦋2⦌₂), spine X 2 _ σ₂ = shortcut0 X f σ₀ h₀
end Truncated

open Simplicial
open SimplexCategory

#check horn
#check Δ[2]
#check @SimplexCategory.δ 1 0
#check yoneda.map (SimplexCategory.δ 0)
#check yonedaEquiv_yoneda_map
#check stdSimplex.yonedaEquiv_map
#check stdSimplex.map 
#check Λ[2, 1].ι

#check horn.const
#check horn.primitiveEdge

-- define the natural maps Δ[1] ⟶ Λ[2, 1] selecting the nontrivial edges
def e₀ := horn.edge 2 1 0 1 (by norm_num) (by norm_num)
def e₂ := horn.edge 2 1 1 2 (Fin.le_iff_val_le_val.2 (by norm_num)) (by aesop)

def hornTwo_edge₀ : Δ[1] ⟶ Λ[2,1] := yonedaEquiv.symm e₀
def hornTwo_edge₂ : Δ[1] ⟶ Λ[2,1] := yonedaEquiv.symm e₂

def pt₀ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 0)
def pt₁ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 1)


#check Limits.PushoutCocone.IsColimit.desc'

-- these are left as sorries, see Joel's PRs (TODO) proving these 
--TODO first sorry should be trivial
def horn_pushout : Limits.PushoutCocone pt₀ pt₁ := Limits.PushoutCocone.mk hornTwo_edge₀ hornTwo_edge₂ 
  (by 
    ext n a 
    dsimp [pt₀, pt₁, hornTwo_edge₀, hornTwo_edge₂, yonedaEquiv, yonedaCompUliftFunctorEquiv, e₀, e₂]
    sorry
    --dsimp [horn.edge, stdSimplex.edge, stdSimplex.objMk, stdSimplex.objEquiv, Equiv.ulift]
  )
def horn_is_pushout : Limits.IsColimit horn_pushout := by sorry
  
def path_edge₀ {X : SSet} (f : Path X 2) : Δ[1] ⟶ X := yonedaEquiv.symm (f.arrow 1)
def path_edge₂ {X : SSet} (f : Path X 2) : Δ[1] ⟶ X := yonedaEquiv.symm (f.arrow 0)

#check Limits.PushoutCocone.IsColimit.desc' horn_is_pushout 

--TODO this sorry should be clear using f.arrow_tgt and f.arrow_src
def horn_from_path {X : SSet} (f : SSet.Path X 2) : Λ[2, 1].toSSet ⟶ X 
  := Limits.PushoutCocone.IsColimit.desc horn_is_pushout (path_edge₀ f) (path_edge₂ f) (by sorry) 

#check yonedaEquiv
#check mkOfSucc
#check map_yonedaEquiv


-- TODO in the proof, we can now use universal property of pushout (this should 
-- be part of horn_from_path data now) ... Also make use of bunch of lemmas related to the 
-- various yonedas used!

universe u 

#check horn_pushout.inr

#check Quasicategory.hornFilling

lemma two_truncatation_of_qc_is_2_trunc_qc {X : SSet.{u}} [Quasicategory X] :
  Truncated.Quasicat ((SSet.truncation 2).obj X) where
  fill21 f := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling.{u} (Fin.zero_lt_one) (by simp) (horn_from_path f)
    let g' := yonedaEquiv g
    use g'
    ext i
    fin_cases i
    . dsimp only [Fin.isValue, Fin.zero_eta]
      rw [truncation_spine] 
      . simp [Truncated.spine_arrow]
        -- TODO apply yonedaEquiv to reduce the statement to the commutativity given by pushout diagram 
        -- TODO want to apply map_yonedaEquiv but this is weird with all the universes
        --rw [map_yonedaEquiv g _ (mkOfSucc 0)]
        --have h₁ : X.map (mkOfSucc 0).op g' = g.app (Opposite.op (mk 1)) 
        --  (stdSimplex.objEquiv.symm (SimplexCategory.δ 2)) := by sorry
        have h₂ : X.map (mkOfSucc 0).op g' = yonedaEquiv (stdSimplex.map (SimplexCategory.δ 2) ≫ g) 
          := by sorry
        rw [h₂]
        have : f.arrow 0 = yonedaEquiv (path_edge₂ f) := by sorry
        rw [this]
        apply yonedaEquiv.congr_arg 
        have : stdSimplex.map (SimplexCategory.δ 2) = hornTwo_edge₂.{u} ≫  Λ[2, 1].ι := by sorry
        rw [this]
        simp at h
        have : (hornTwo_edge₂ ≫ Λ[2, 1].ι) ≫ g = hornTwo_edge₂ ≫ (Λ[2, 1].ι ≫ g) := by aesop_cat
        rw [this]
        rw [← h]
        --TODO this sorry as the same as further above
        exact CategoryTheory.Limits.PushoutCocone.IsColimit.inr_desc 
          horn_is_pushout (path_edge₀ f) (path_edge₂ f) (by sorry)
        --sorry
      . --TODO get rid of this weird 1 + 1 ≤ 2 path 
        norm_num
    sorry
 -- TODO how can we make life easy for ourselves here?
  fill31 := sorry
  fill32 := sorry
