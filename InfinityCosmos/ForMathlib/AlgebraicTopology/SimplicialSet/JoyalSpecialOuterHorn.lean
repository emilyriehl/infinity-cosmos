import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

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
