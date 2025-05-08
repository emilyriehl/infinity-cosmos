import Mathlib.AlgebraicTopology.SimplicialSet.Basic

open Simplicial SimplexCategory CategoryTheory SimplexCategory.Truncated Truncated.Hom
  SimplicialObject SimplicialObject.Truncated

namespace SSet
namespace Truncated

/--
The idea behind this trivial equivalence and `trunc_map`, `trunc_map'`
is to make explicit whether an object is in a truncated simplicial set;
this allows us to replace `dsimp`s in proofs by `rw`s.
-/
def truncEquiv {S : SSet} (m : ℕ) {a : SimplexCategory} (ha : a.len ≤ m := by trunc) :
    S.obj (Opposite.op a) ≃ ((truncation m).obj S).obj (Opposite.op ⟨a, ha⟩) where
  toFun := id
  invFun := id
  left_inv := congrFun rfl
  right_inv := congrFun rfl

lemma trunc_map {S : SSet} {m : ℕ} {a b : SimplexCategory}
    (ha : a.len ≤ m := by trunc) (hb : b.len ≤ m := by trunc)
    {f : a ⟶ b} {σ : S.obj (Opposite.op b)} :
    ((truncation m).obj S).map (tr f).op (truncEquiv m hb σ) = S.map f.op σ := rfl

lemma trunc_map' {S : SSet} {m : ℕ} {a b : SimplexCategory}
    (ha : a.len ≤ m := by trunc) (hb : b.len ≤ m := by trunc)
    {f : a ⟶ b} {σ : truncation m |>.obj S |>.obj (Opposite.op ⟨b, hb⟩)} :
    ((truncation m).obj S).map (tr f).op σ = S.map f.op σ := rfl
