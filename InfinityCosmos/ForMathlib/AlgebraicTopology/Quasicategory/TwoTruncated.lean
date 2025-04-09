import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.Quasicategory.Basic

open SimplexCategory
open CategoryTheory SimplexCategory.Truncated Truncated.Hom SimplicialObject
open SimplicialObject.Truncated

namespace SSet
namespace Truncated

#check tr

def diagonal {n m : ℕ} (h1 : 1 ≤ m := by omega) (h2 : n ≤ m := by omega)
  (X : Truncated m) : X _⦋n⦌ₘ ⟶ X _⦋1⦌ₘ
  := X.map (tr (SimplexCategory.diag n)).op

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

def e₁ := horn.edge 2 1 0 1 (by norm_num) (by norm_num)
def e₂ := horn.edge 2 1 1 2 (Fin.le_iff_val_le_val.2 (by norm_num)) (by aesop)

--TODO
open SimplexCategory

def horn_from_path (X : SSet) (f : SSet.Path X 2) : Λ[2, 1].toSSet ⟶ X
  := ⟨fun n horn ↦ by
    rw [horn_eq_iSup] at horn
    sorry
    , by sorry⟩

lemma two_truncatation_of_qc_is_2_trunc_qc {X : SSet} [Quasicategory X] :
  Truncated.Quasicat ((SSet.truncation 2).obj X) where
  fill21 f := by
    obtain ⟨g, h⟩ := Quasicategory.hornFilling (Fin.zero_lt_one) (by simp) (horn_from_path X f)
    use yonedaEquiv g
    sorry
  fill31 := sorry
  fill32 := sorry
