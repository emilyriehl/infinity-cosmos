import Mathlib.AlgebraicTopology.SimplicialSet.Basic

open CategoryTheory Simplicial SimplexCategory SimplexCategory.Truncated
    SimplexCategory.Truncated.Hom
    
namespace SSet.Truncated

/-- A trivial equivalence making explicit whether an object is in a truncated simplicial set,
allowing `rw` in place of `dsimp` in proofs. See also `trunc_map` and `trunc_map'`. -/
def truncEquiv {S : SSet} (m : ℕ) {a : SimplexCategory} (ha : a.len ≤ m := by trunc) :
    S.obj (Opposite.op a) ≃ ((truncation m).obj S).obj (Opposite.op ⟨a, ha⟩) :=
  Equiv.refl _

lemma trunc_map {S : SSet} {m : ℕ} {a b : SimplexCategory}
    (ha : a.len ≤ m := by trunc) (hb : b.len ≤ m := by trunc)
    {f : a ⟶ b} {σ : S.obj (Opposite.op b)} :
    ((truncation m).obj S).map (tr f).op (truncEquiv m hb σ) = S.map f.op σ := rfl

lemma trunc_map' {S : SSet} {m : ℕ} {a b : SimplexCategory}
    (ha : a.len ≤ m := by trunc) (hb : b.len ≤ m := by trunc)
    {f : a ⟶ b} {σ : truncation m |>.obj S |>.obj (Opposite.op ⟨b, hb⟩)} :
    ((truncation m).obj S).map (tr f).op σ = S.map f.op σ := rfl

end SSet.Truncated
