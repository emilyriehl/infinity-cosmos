import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Simplicial SimplexCategory Limits

namespace SimplexCategory

/-- The object `[0]` is terminal in `SimplexCategory`.-/
def isTerminalZero : IsTerminal ([0] : SimplexCategory) :=
  IsTerminal.ofUniqueHom (fun _ ↦ const _ [0] 0) (fun _ _ => eq_const_to_zero _)

lemma δ_one_zero : δ (n := 1) 0 = mkOfSucc 1 := by
  ext i
  fin_cases i <;> rfl

lemma δ_one_one : δ (n := 1) 1 = diag 2 := by
  ext i
  fin_cases i <;> rfl

lemma δ_one_two : δ (n := 1) 2 = mkOfSucc 0 := by
  ext i
  fin_cases i <;> rfl

end SimplexCategory
