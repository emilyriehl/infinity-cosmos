import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory SimplexCategory

namespace SimplexCategory

def δ_zero_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    δ 0 ≫ mkOfLe i j h = (mk 0).const (mk n) j := by
  ext x; fin_cases x; simp [δ, mkOfLe, const]

def δ_one_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    δ 1 ≫ mkOfLe i j h = (mk 0).const (mk n) i := by
  ext x; fin_cases x; simp [δ, mkOfLe, const]

end SimplexCategory
