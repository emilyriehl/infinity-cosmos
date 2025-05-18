import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

open Simplicial SimplexCategory CategoryTheory

namespace SSet
section yonedaEquiv_lemmas

/--
A variant of `CategoryTheory.map_yonedaEquiv` specialized to simplicial sets.
-/
lemma map_yonedaEquiv {n m : ℕ} {X : SSet} (f : ⦋n⦌ ⟶ ⦋m⦌) (g : Δ[m] ⟶ X) :
    X.map f.op (yonedaEquiv g) = g.app (.op ⦋n⦌) (stdSimplex.objEquiv.symm f) := by
  change (g.app (.op ⦋m⦌) ≫ X.map f.op) (stdSimplex.objEquiv.symm (𝟙 _)) =
     g.app (.op ⦋n⦌) (stdSimplex.objEquiv.symm f)
  rw [← g.naturality]
  dsimp
  have : Δ[m].map f.op (stdSimplex.objEquiv.symm (𝟙 _)) = stdSimplex.objEquiv.symm f := by
    aesop_cat
  rw [this]
  rfl

/--
If a simplex `σ` of a simplicial set `X` is equivalent to a composition `stdSimplex.map s ≫ g`
then we can pull the `stdSimplex.map s` out from under an application of any `X.map f.op`.
-/
lemma push_yonedaEquiv {n m k : ℕ} {X : SSet} {f : ⦋m⦌ ⟶ ⦋n⦌}
    {σ : X.obj (.op ⦋n⦌)} {s : ⦋n⦌ ⟶ ⦋k⦌} {g : Δ[k] ⟶ X}
    (h : yonedaEquiv.symm σ = stdSimplex.map s ≫ g) :
    X.map f.op σ = X.map (f ≫ s).op (yonedaEquiv g) := by
  rw [← Equiv.apply_symm_apply yonedaEquiv σ, h]
  have : yonedaEquiv (stdSimplex.map s ≫ g) = X.map s.op (yonedaEquiv g) := by
    rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_map, ← map_yonedaEquiv]
  rw [this, ← FunctorToTypes.map_comp_apply, ← op_comp]

/--
A variant of `map_yonedaEquiv`.
-/
lemma map_yonedaEquiv' {n m : ℕ} {X : SSet} (f : ⦋m⦌ ⟶ ⦋n⦌) {g : Δ[n] ⟶ X} :
    yonedaEquiv (stdSimplex.map f ≫ g) = X.map f.op (yonedaEquiv g) := by
  rw [yonedaEquiv_comp, map_yonedaEquiv, ← stdSimplex.yonedaEquiv_map]

/--
A specialization of `push_yonedaEquiv` to the case where `s` is the identity.
-/
lemma push_yonedaEquiv' {n m : ℕ} {X : SSet} {f : ⦋m⦌ ⟶ ⦋n⦌}
    {σ : X.obj (.op ⦋m⦌)} {g : Δ[n] ⟶ X}
    (h : yonedaEquiv.symm σ = stdSimplex.map f ≫ g) :
    σ = X.map f.op (yonedaEquiv g) := by
  rw [← map_yonedaEquiv']
  apply (Equiv.symm_apply_eq yonedaEquiv).1
  exact h

/--
Another version of `map_yonedaEquiv`, but at the level of functions `Δ[n] ⟶ X`.
-/
lemma map_comp_yonedaEquiv_symm {n m : ℕ} {X : SSet} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (s : X.obj (.op ⦋m⦌)) :
    stdSimplex.map f ≫ yonedaEquiv.symm s = yonedaEquiv.symm (X.map f.op s) := by
  apply yonedaEquiv.apply_eq_iff_eq_symm_apply.1
  let s' := yonedaEquiv.symm s
  have : s = yonedaEquiv s' := (Equiv.symm_apply_eq yonedaEquiv).mp rfl
  rw [this, map_yonedaEquiv, yonedaEquiv_comp, Equiv.apply_symm_apply yonedaEquiv _,
    stdSimplex.yonedaEquiv_map]

end yonedaEquiv_lemmas
