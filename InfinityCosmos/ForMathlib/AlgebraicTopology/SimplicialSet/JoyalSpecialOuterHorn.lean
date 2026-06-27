import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join

/-!
# Vertex bookkeeping for the Joyal special outer horn argument

This file records the horn-side combinatorics for the base case
`∂Δ[p] ⋆̂ Λ[m,k]`.  The actual comparison with the image of the
Leibniz join under `joinStdSimplex` still needs simplex-level naturality
of that isomorphism with respect to the two standard-simplex factors.
-/

open CategoryTheory Simplicial Opposite

namespace SSet

universe u

/-- The left block vertex inside the ordinal sum `[p] ⋆ [m] = [p+m+1]`. -/
def joinLeftVertex (p m : ℕ) (i : Fin (p + 1)) : Fin (p + m + 2) :=
  ⟨i, by omega⟩

/-- The right block vertex inside the ordinal sum `[p] ⋆ [m] = [p+m+1]`. -/
def joinRightVertex (p m : ℕ) (j : Fin (m + 1)) : Fin (p + m + 2) :=
  ⟨p + 1 + j, by have := j.isLt; omega⟩

@[simp]
lemma joinLeftVertex_val (p m : ℕ) (i : Fin (p + 1)) :
    (joinLeftVertex p m i : ℕ) = i :=
  rfl

@[simp]
lemma joinRightVertex_val (p m : ℕ) (j : Fin (m + 1)) :
    (joinRightVertex p m j : ℕ) = p + 1 + j :=
  rfl

lemma joinLeftVertex_ne_joinRightVertex (p m : ℕ)
    (i : Fin (p + 1)) (j : Fin (m + 1)) :
    joinLeftVertex p m i ≠ joinRightVertex p m j := by
  apply Fin.ne_of_val_ne
  simp
  omega

lemma joinRightVertex_injective (p m : ℕ) :
    Function.Injective (joinRightVertex p m) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin (p + m + 2) => (x : ℕ)) h
  simpa using Nat.add_left_cancel hv

/-- Tensoring a left coface with an identity is the coface missing the corresponding
left-block vertex, up to the associativity casts in the ordinal arithmetic. -/
lemma tensorHomOf_δ_left (p m : ℕ) (i : Fin (p + 2)) :
    AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ i) (𝟙 ⦋m⦌) =
      eqToHom (by
        have h : p + m + 1 = (p + 1) + m := by omega
        simp [AugmentedSimplexCategory.tensorObjOf, h]) ≫
      SimplexCategory.δ (joinLeftVertex (p + 1) m i) ≫
      eqToHom (by
        simp [AugmentedSimplexCategory.tensorObjOf]) := by
  ext r : 3
  simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ, joinLeftVertex,
    Fin.succAbove, Fin.addCases]
  grind

/-- Tensoring an identity with a right coface is the coface missing the corresponding
right-block vertex, up to the associativity casts in the ordinal arithmetic. -/
lemma tensorHomOf_δ_right (p m : ℕ) (j : Fin (m + 2)) :
    AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋p⦌) (SimplexCategory.δ j) =
      eqToHom (by
        have h : p + m + 1 = p + (m + 1) := by omega
        simp [AugmentedSimplexCategory.tensorObjOf, h]) ≫
      SimplexCategory.δ (joinRightVertex p (m + 1) j) ≫
      eqToHom (by
        simp [AugmentedSimplexCategory.tensorObjOf]) := by
  ext r : 3
  simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ, joinRightVertex,
    Fin.succAbove, Fin.addCases]
  grind

/-- A simplex lies in the complementary face `{i}ᶜ` iff it misses vertex `i`. -/
lemma mem_face_compl_singleton_iff {n d : ℕ} (i : Fin (n + 1))
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (stdSimplex.face {i}ᶜ).obj (op ⦋d⦌) ↔ i ∉ Set.range x := by
  rw [stdSimplex.mem_face_iff]
  simp only [Finset.mem_compl, Finset.mem_singleton]
  constructor
  · rintro h ⟨k, rfl⟩
    exact h k rfl
  · intro h k hk
    exact h ⟨k, hk⟩

/-- Membership in the target horn, split by the two ordinal-sum vertex blocks. -/
lemma mem_joyalBase_horn_iff {p m d : ℕ} (k : Fin (m + 1))
    (s : (Δ[p + m + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (horn (p + m + 1) (joinRightVertex p m k)).obj (op ⦋d⦌) ↔
      (∃ i : Fin (p + 1), joinLeftVertex p m i ∉ Set.range s) ∨
        (∃ j : Fin (m + 1), j ≠ k ∧ joinRightVertex p m j ∉ Set.range s) := by
  rw [mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨v, hv_ne, hv_missing⟩
    rcases Nat.lt_or_ge (v : ℕ) (p + 1) with hv_left | hv_right
    · let i : Fin (p + 1) := ⟨v, hv_left⟩
      have hv_eq : v = joinLeftVertex p m i := by
        apply Fin.ext
        rfl
      exact Or.inl ⟨i, by simpa [hv_eq] using hv_missing⟩
    · have hv_bound : (v : ℕ) - (p + 1) < m + 1 := by
        have := v.isLt
        omega
      let j : Fin (m + 1) := ⟨(v : ℕ) - (p + 1), hv_bound⟩
      have hv_eq : v = joinRightVertex p m j := by
        apply Fin.ext
        simp [joinRightVertex, j]
        omega
      refine Or.inr ⟨j, ?_, by simpa [hv_eq] using hv_missing⟩
      intro hj
      exact hv_ne (by rw [hv_eq, hj])
  · rintro (⟨i, hi⟩ | ⟨j, hj_ne, hj⟩)
    · exact ⟨joinLeftVertex p m i, joinLeftVertex_ne_joinRightVertex p m i k, hi⟩
    · exact ⟨joinRightVertex p m j, fun h => hj_ne (joinRightVertex_injective p m h), hj⟩

/-- The target horn as the union of the shifted left-boundary faces and shifted right-horn faces. -/
lemma joyalBase_horn_eq_vertexBlocks (p m : ℕ) (k : Fin (m + 1)) :
    horn.{u} (p + m + 1) (joinRightVertex p m k) =
      (⨆ i : Fin (p + 1), stdSimplex.face {joinLeftVertex p m i}ᶜ) ⊔
        (⨆ j : {j : Fin (m + 1) // j ≠ k},
          stdSimplex.face {joinRightVertex p m j.1}ᶜ) := by
  ext n x
  induction n using Opposite.rec with
  | _ n =>
    induction n using SimplexCategory.rec with
    | _ d =>
      rw [mem_joyalBase_horn_iff]
      rw [Subfunctor.max_obj, Set.mem_union, Subfunctor.iSup_obj, Set.mem_iUnion,
        Subfunctor.iSup_obj, Set.mem_iUnion]
      constructor
      · rintro (⟨i, hi⟩ | ⟨j, hj_ne, hj⟩)
        · exact Or.inl ⟨i, (mem_face_compl_singleton_iff _ _).mpr hi⟩
        · exact Or.inr ⟨⟨j, hj_ne⟩, (mem_face_compl_singleton_iff _ _).mpr hj⟩
      · rintro (⟨i, hi⟩ | ⟨⟨j, hj_ne⟩, hj⟩)
        · exact Or.inl ⟨i, (mem_face_compl_singleton_iff _ _).mp hi⟩
        · exact Or.inr ⟨j, hj_ne, (mem_face_compl_singleton_iff _ _).mp hj⟩

/-- The F-horn image identity once the left-boundary and right-horn face-image
computations have been supplied. -/
theorem fhorn_identity_of_faceImages (p m : ℕ) (k : Fin (m + 1))
    (H1 : (Subcomplex.range (joinMap (∂Δ[p] : (Δ[p] : SSet.{u}).Subcomplex).ι
            (𝟙 (Δ[m] : SSet.{u})))).image (joinStdSimplex.{u} p m).hom =
          ⨆ i : Fin (p + 1), stdSimplex.face {joinLeftVertex p m i}ᶜ)
    (H2 : (Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u}))
            (Λ[m, k] : (Δ[m] : SSet.{u}).Subcomplex).ι)).image
            (joinStdSimplex.{u} p m).hom =
          ⨆ j : {j : Fin (m + 1) // j ≠ k},
            stdSimplex.face {joinRightVertex p m j.1}ᶜ) :
    (Subcomplex.range
          (joinMap (∂Δ[p] : (Δ[p] : SSet.{u}).Subcomplex).ι
            (𝟙 (Δ[m] : SSet.{u}))) ⊔
        Subcomplex.range
          (joinMap (𝟙 (Δ[p] : SSet.{u}))
            (Λ[m, k] : (Δ[m] : SSet.{u}).Subcomplex).ι)).image
          (joinStdSimplex.{u} p m).hom =
      horn.{u} (p + m + 1) (joinRightVertex p m k) := by
  rw [image_sup, H1, H2, ← joyalBase_horn_eq_vertexBlocks]

/-- Image transport along an `eqToHom` between simplicial sets. -/
lemma image_eqToHom_aux {X Y : SSet.{u}} (h : X = Y) (A : X.Subcomplex) :
    A.image (eqToHom h) = h ▸ A := by
  subst h
  simp [Subcomplex.image_id]

/-- The right `tensorHomOf` coface range is the shifted right-block face. -/
lemma range_tensorHomOf_right (p M : ℕ) (j : Fin (M + 2)) :
    Subcomplex.range (stdSimplex.{u}.map
        (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋p⦌) (SimplexCategory.δ j))) =
      stdSimplex.face {joinRightVertex p (M + 1) j}ᶜ := by
  rw [tensorHomOf_δ_right p M j, Functor.map_comp, Functor.map_comp,
      eqToHom_map, eqToHom_map, Subcomplex.range_comp, Subcomplex.range_eq_top,
      Subcomplex.image_top, Subcomplex.range_comp,
      show stdSimplex.{u}.map (SimplexCategory.δ (joinRightVertex p (M + 1) j))
          = stdSimplex.{u}.δ (joinRightVertex p (M + 1) j) from rfl,
      stdSimplex.range_δ, image_eqToHom_aux]

/-- The left `tensorHomOf` coface range is the shifted left-block face. -/
lemma range_tensorHomOf_left (p m : ℕ) (i : Fin (p + 2)) :
    Subcomplex.range (stdSimplex.{u}.map
        (AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ i) (𝟙 ⦋m⦌))) =
      stdSimplex.face {joinLeftVertex (p + 1) m i}ᶜ := by
  rw [tensorHomOf_δ_left p m i, Functor.map_comp, Functor.map_comp,
      eqToHom_map, eqToHom_map, Subcomplex.range_comp, Subcomplex.range_eq_top,
      Subcomplex.image_top, Subcomplex.range_comp,
      show stdSimplex.{u}.map (SimplexCategory.δ (joinLeftVertex (p + 1) m i))
          = stdSimplex.{u}.δ (joinLeftVertex (p + 1) m i) from rfl,
      stdSimplex.range_δ, image_eqToHom_aux]

/-- The right-horn join image is the supremum of its shifted right-block faces. -/
theorem fhorn_H2 (p M : ℕ) (k : Fin (M + 1 + 1)) :
    (Subcomplex.range (joinMap (𝟙 (Δ[p] : SSet.{u}))
        (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι)).image
        (joinStdSimplex.{u} p (M + 1)).hom =
      ⨆ j : {j : Fin (M + 1 + 1) // j ≠ k},
        stdSimplex.face {joinRightVertex p (M + 1) j.1}ᶜ := by
  rw [image_range_joinMap_horn_eq_iSup_right]
  exact iSup_congr (fun j => range_tensorHomOf_right p M j.1)

/-- The left-boundary join image is the supremum of its shifted left-block faces. -/
theorem fhorn_H1 (P M : ℕ) :
    (Subcomplex.range (joinMap (∂Δ[P + 1] : (Δ[P + 1] : SSet.{u}).Subcomplex).ι
        (𝟙 (Δ[M + 1] : SSet.{u})))).image (joinStdSimplex.{u} (P + 1) (M + 1)).hom =
      ⨆ i : Fin (P + 1 + 1),
        stdSimplex.face {joinLeftVertex (P + 1) (M + 1) i}ᶜ := by
  rw [image_range_joinMap_boundary_eq_iSup P (M + 1)]
  exact iSup_congr (fun i => range_tensorHomOf_left P (M + 1) i)

/-- The full base-case F-horn image identity for `p, m ≥ 1`. -/
theorem fhorn_image_identity (P M : ℕ) (k : Fin (M + 1 + 1)) :
    (Subcomplex.range
          (joinMap (∂Δ[P + 1] : (Δ[P + 1] : SSet.{u}).Subcomplex).ι
            (𝟙 (Δ[M + 1] : SSet.{u}))) ⊔
        Subcomplex.range
          (joinMap (𝟙 (Δ[P + 1] : SSet.{u}))
            (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι)).image
          (joinStdSimplex.{u} (P + 1) (M + 1)).hom =
      horn.{u} ((P + 1) + (M + 1) + 1) (joinRightVertex (P + 1) (M + 1) k) :=
  fhorn_identity_of_faceImages (P + 1) (M + 1) k (fhorn_H1 P M) (fhorn_H2 (P + 1) M k)

lemma joyalBaseIndex_interior (p m : ℕ) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    (0 : Fin (p + m + 1 + 1)) < joinRightVertex p m k ∧
      joinRightVertex p m k < Fin.last (p + m + 1) := by
  have hkm : (k : ℕ) < m := by
    rw [Fin.lt_def, Fin.val_last] at hk
    exact hk
  constructor
  · rw [Fin.lt_def]
    simp [joinRightVertex]
  · rw [Fin.lt_def, Fin.val_last]
    simp [joinRightVertex]
    omega

/-- The target horn in the base case is an inner horn. -/
lemma joyalBase_innerAnodyne (p m : ℕ) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    innerAnodyneExtensions.{u}
      (Λ[p + m + 1, joinRightVertex p m k].ι) :=
  let ⟨h0, hn⟩ := joyalBaseIndex_interior p m k hk
  innerAnodyneExtensions.horn_ι h0 hn

end SSet
