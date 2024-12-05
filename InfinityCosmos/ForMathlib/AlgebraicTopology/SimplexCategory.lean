import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Simplicial SimplexCategory Limits

namespace SimplexCategory

/-- The object `[0]` is terminal in `SimplexCategory`.-/
def isTerminalZero : IsTerminal ([0] : SimplexCategory) :=
  IsTerminal.ofUniqueHom (fun _ ↦ const _ [0] 0) (fun _ _ => eq_const_to_zero _)

lemma δ_one_diag {n : ℕ} : δ 1 ≫ diag n = const [0] [n] 0 := by
  ext x
  fin_cases x
  rfl

lemma δ_zero_diag {n : ℕ} : δ 0 ≫ diag n = const [0] [n] n := by
  ext x
  fin_cases x
  rfl

end SimplexCategory
