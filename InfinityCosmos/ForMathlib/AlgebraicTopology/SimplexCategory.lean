import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory Simplicial SimplexCategory Limits

namespace SimplexCategory

/-- The object `⦋0⦌` is terminal in `SimplexCategory`.-/
def isTerminalZero : IsTerminal (⦋0⦌ : SimplexCategory) :=
  IsTerminal.ofUniqueHom (fun _ ↦ const _ ⦋0⦌ 0) (fun _ _ => eq_const_to_zero _)

def δ_zero_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 0 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) j := by
  ext x
  fin_cases x
  aesop

def δ_one_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 1 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) i := by
  ext x
  fin_cases x
  aesop

end SimplexCategory
