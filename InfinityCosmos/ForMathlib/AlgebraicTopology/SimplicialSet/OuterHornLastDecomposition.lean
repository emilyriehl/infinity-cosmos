/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.JoyalSpecialOuterHorn

/-!
# Outer (`i = last`) horn as a Leibniz join — the geometric heart of Layer C

Identifies the last outer-horn inclusion with a generating Leibniz join:
`outerHornLast_iso_leibnizJoin` exhibits `Λ[n+2, last].ι` as the join
`(∂Δ[n] ↪ Δ[n]) ⋆̂ ({0}ᶜ ↪ Δ[1])`. This arrow-isomorphism is what transports the coslice Leibniz
filler to the special-outer-horn filler `SpecialOuterHorn.fill_last`. The membership criterion
`mem_outerHorn_last_iff` decomposes the horn by its two ordinal-sum vertex blocks. A standard
join-of-simplices computation, as used in the proof of the Joyal pushout-product.
-/

open CategoryTheory Simplicial Opposite Limits MorphismProperty

namespace SSet

universe u


/-- Membership in the outer horn `Λ[(M+1)+1+1, last]`, split by the two
ordinal-sum vertex blocks: missing some left vertex, or missing the front
right vertex `0` (the cone neighbour). -/
lemma mem_outerHorn_last_iff {M d : ℕ}
    (s : (Δ[(M + 1) + 1 + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (horn ((M + 1) + 1 + 1) (joinRightVertex (M + 1) 1 1)).obj (op ⦋d⦌) ↔
      (∃ i : Fin (M + 2), joinLeftVertex (M + 1) 1 i ∉ Set.range s) ∨
        (joinRightVertex (M + 1) 1 0 ∉ Set.range s) := by
  rw [mem_horn_iff_notMem_range]
  have hR0 : (joinRightVertex (M + 1) 1 (0 : Fin 2) : ℕ) = M + 2 := by
    simp [joinRightVertex_val]
  have hR1 : (joinRightVertex (M + 1) 1 (1 : Fin 2) : ℕ) = M + 3 := by
    simp [joinRightVertex_val]
  constructor
  · rintro ⟨v, hv_ne, hv_missing⟩
    have hvne : (v : ℕ) ≠ M + 3 := fun h => hv_ne (Fin.ext (h.trans hR1.symm))
    rcases Nat.lt_or_ge (v : ℕ) (M + 2) with hlt | hge
    · left
      refine ⟨⟨(v : ℕ), hlt⟩, ?_⟩
      have hvj : v = joinLeftVertex (M + 1) 1 ⟨(v : ℕ), hlt⟩ :=
        Fin.ext (by simp [joinLeftVertex_val])
      rwa [hvj] at hv_missing
    · right
      have hub : (v : ℕ) < M + 4 := by have := v.isLt; omega
      have hv_eq : v = joinRightVertex (M + 1) 1 0 :=
        Fin.ext (by rw [hR0]; omega)
      rwa [hv_eq] at hv_missing
  · rintro (⟨i, hi⟩ | h)
    · exact ⟨joinLeftVertex (M + 1) 1 i,
        joinLeftVertex_ne_joinRightVertex (M + 1) 1 i 1, hi⟩
    · refine ⟨joinRightVertex (M + 1) 1 0, ?_, h⟩
      intro heq
      exact absurd (joinRightVertex_injective (M + 1) 1 heq) (by decide)

/-- The outer horn `Λ[(M+1)+1+1, last]` as the union of the shifted left-boundary
faces and the single front right-vertex face.  (i = last dual of
`outerHorn_zero_eq_vertexBlocks`.) -/
lemma outerHorn_last_eq_vertexBlocks (M : ℕ) :
    horn.{u} ((M + 1) + 1 + 1) (joinRightVertex (M + 1) 1 1) =
      (⨆ i : Fin (M + 2), stdSimplex.face {joinLeftVertex (M + 1) 1 i}ᶜ) ⊔
        stdSimplex.face {joinRightVertex (M + 1) 1 0}ᶜ := by
  ext n x
  induction n using Opposite.rec with
  | _ n =>
    induction n using SimplexCategory.rec with
    | _ d =>
      rw [mem_outerHorn_last_iff, Subfunctor.max_obj, Set.mem_union,
        Subfunctor.iSup_obj, Set.mem_iUnion]
      constructor
      · rintro (⟨i, hi⟩ | h)
        · exact Or.inl ⟨i, (mem_face_compl_singleton_iff _ _).mpr hi⟩
        · exact Or.inr ((mem_face_compl_singleton_iff _ _).mpr h)
      · rintro (⟨i, hi⟩ | h)
        · exact Or.inl ⟨i, (mem_face_compl_singleton_iff _ _).mp hi⟩
        · exact Or.inr ((mem_face_compl_singleton_iff _ _).mp h)

/-- Front-vertex block image: the join image of `Δ[r] ⋆ ({last} ↪ Δ[1])` is the
missing-front-right-vertex face. -/
theorem ohorn_front_last (r : ℕ) :
    (Subcomplex.range (joinMap
        (𝟙 (Δ[r] : SSet.{u}))
        (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι)).image
        (joinStdSimplex.{u} r 1).hom =
      stdSimplex.face {joinRightVertex r 1 0}ᶜ := by
  have hfac : (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι =
      (stdSimplex.faceSingletonComplIso (0 : Fin 2)).inv ≫ stdSimplex.δ (0 : Fin 2) := by
    rw [← boundary.ι_ι (0 : Fin 2), ← Category.assoc,
      boundary.faceSingletonComplIso_inv_ι (0 : Fin 2)]
    exact (boundary.faceι_ι (0 : Fin 2)).symm
  have hrange : Subcomplex.range (joinMap
        (𝟙 (Δ[r] : SSet.{u}))
        (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι) =
      Subcomplex.range (joinMap (𝟙 (Δ[r] : SSet.{u}))
        (stdSimplex.{u}.map (SimplexCategory.δ (0 : Fin 2)))) := by
    haveI : IsIso (joinMap (𝟙 (Δ[r] : SSet.{u}))
        (stdSimplex.faceSingletonComplIso (0 : Fin 2)).inv) := by
      rw [joinMap_id_left]
      exact Functor.map_isIso _ _
    rw [hfac, show stdSimplex.δ (0 : Fin 2)
          = stdSimplex.{u}.map (SimplexCategory.δ (0 : Fin 2)) from rfl,
      joinMap_comp_right, Subcomplex.range_comp, Subcomplex.range_eq_top,
      Subcomplex.image_top]
  rw [hrange, image_range_joinMap_right r 0 1 (SimplexCategory.δ (0 : Fin 2)),
    range_tensorHomOf_right r 0 (0 : Fin 2)]

/-- Back-boundary block image: the join image of `∂Δ[M+1] ⋆ Δ[1]` is the supremum
of the shifted left faces. -/
theorem ohorn_back_last (M : ℕ) :
    (Subcomplex.range (joinMap
        (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
        (𝟙 (Δ[1] : SSet.{u})))).image
        (joinStdSimplex.{u} (M + 1) 1).hom =
      ⨆ i : Fin (M + 2), stdSimplex.face {joinLeftVertex (M + 1) 1 i}ᶜ := by
  rw [image_range_joinMap_boundary_eq_iSup M 1]
  exact iSup_congr (fun i => range_tensorHomOf_left M 1 i)

/-- The outer-horn image identity (i = last): the join image of the union of the
two blocks is the outer horn `Λ[(M+1)+1+1, last]`. -/
theorem outer_fhorn_image_identity_last (M : ℕ) :
    (Subcomplex.range
          (joinMap (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
            (𝟙 (Δ[1] : SSet.{u}))) ⊔
        Subcomplex.range
          (joinMap (𝟙 (Δ[M + 1] : SSet.{u}))
            (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι)).image
          (joinStdSimplex.{u} (M + 1) 1).hom =
      horn.{u} ((M + 1) + 1 + 1) (joinRightVertex (M + 1) 1 1) := by
  rw [image_sup, ohorn_back_last M, ohorn_front_last (M + 1),
    ← outerHorn_last_eq_vertexBlocks M]

/-- The generating outer (i = last) Leibniz join, as an arrow. -/
noncomputable abbrev genCellOuterLast (M : ℕ) : Arrow SSet.{u} :=
  Arrow.mk (leibnizJoin
    (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
    (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι)

/-- The target outer (i = last) horn inclusion, as an arrow. -/
abbrev targetHornOuterLast (M : ℕ) : Arrow SSet.{u} :=
  Arrow.mk (Λ[(M + 1) + 1 + 1, joinRightVertex (M + 1) 1 1].ι)

/-- The outer (i = last) F-horn identity as the range of the actual generating
Leibniz join after the standard-simplex join isomorphism. -/
theorem genCellOuterLast_range_image_identity (M : ℕ) :
    Subcomplex.range
        (leibnizJoin (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
            (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι ≫
          (joinStdSimplex.{u} (M + 1) 1).hom) =
      horn.{u} ((M + 1) + 1 + 1) (joinRightVertex (M + 1) 1 1) := by
  rw [Subcomplex.range_comp, range_leibnizJoin, sup_comm]
  exact outer_fhorn_image_identity_last M

/-- The generating outer (i = last) Leibniz join is a monomorphism. -/
theorem genCellOuterLast_mono (M : ℕ) :
    Mono (leibnizJoin (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
      (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι) :=
  leibnizJoin_mono _ _ inferInstance inferInstance

/-- **Outer (i = last) arrow-iso.**  The generating outer Leibniz join
`(∂Δ[n] ↪ Δ[n]) ⋆̂ ({last} ↪ Δ[1])` is isomorphic, as an arrow, to the outer horn
inclusion `Λ[n+2, last].ι` (here `n = M+1`). -/
noncomputable def genCellOuterLast_iso_targetHornOuterLast (M : ℕ) :
    genCellOuterLast.{u} M ≅ targetHornOuterLast.{u} M := by
  haveI := genCellOuterLast_mono M
  haveI : Mono (leibnizJoin
      (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
      (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι ≫
        (joinStdSimplex.{u} (M + 1) 1).hom) := inferInstance
  have hrange :
      Subcomplex.range (leibnizJoin
          (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
          (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι ≫
        (joinStdSimplex.{u} (M + 1) 1).hom) =
        Λ[(M + 1) + 1 + 1, joinRightVertex (M + 1) 1 1] :=
    genCellOuterLast_range_image_identity M
  refine (Arrow.isoMk (Iso.refl _) (joinStdSimplex.{u} (M + 1) 1) (by rfl) :
      genCellOuterLast.{u} M ≅
        Arrow.mk (leibnizJoin
          (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
          (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι ≫
            (joinStdSimplex.{u} (M + 1) 1).hom)) ≪≫ ?_
  exact arrowMk_iso_of_mono_range _ hrange

/-- The missing vertex of the i = last outer horn is the final vertex. -/
lemma joinRightVertex_last (M : ℕ) :
    joinRightVertex (M + 1) 1 1 = Fin.last ((M + 1) + 1 + 1) := by
  apply Fin.ext
  simp [joinRightVertex_val, Fin.val_last]

/-- The geometric heart of Layer C: the outer (`i = last`) horn inclusion is the generating
Leibniz join `Λ[n+2, last].ι ≅ (∂Δ[n] ↪ Δ[n]) ⋆̂ ({0}ᶜ ↪ Δ[1])` (here `n = M+1`). -/
noncomputable def outerHornLast_iso_leibnizJoin (M : ℕ) :
    Arrow.mk (Λ[(M + 1) + 1 + 1, joinRightVertex (M + 1) 1 1].ι) ≅
      Arrow.mk (leibnizJoin
        (∂Δ[M + 1] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
        (stdSimplex.face {(0 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex).ι) :=
  (genCellOuterLast_iso_targetHornOuterLast M).symm

end SSet
