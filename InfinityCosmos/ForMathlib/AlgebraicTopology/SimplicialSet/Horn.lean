import Mathlib.AlgebraicTopology.SimplicialSet.Horn

open Simplicial SSet CategoryTheory Subcomplex

namespace SSet

def hornFaceIncl {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (h : j ≠ i)
  : Δ[n] ⟶ Λ[n + 1, i] := yonedaEquiv.symm (horn.face i j h)

lemma horn_face_δ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (h : j ≠ i) :
  (hornFaceIncl i j h) ≫ Λ[n + 1, i].ι = stdSimplex.δ j := rfl

/-!
Statements about the pushout
Δ[0]  →  Δ[1]
 ↓        ↓
Δ[1]  → Λ[2, 1] .
-/
namespace horn₂₁

abbrev ι₀ : Δ[1] ⟶ Λ[2, 1] := hornFaceIncl 1 0 (by norm_num)
abbrev ι₂ : Δ[1] ⟶ Λ[2, 1] := hornFaceIncl 1 2 (by simp)

lemma incl₀ : ι₀ ≫ Λ[2, 1].ι = stdSimplex.δ 0 := rfl
lemma incl₂ : ι₂ ≫ Λ[2, 1].ι = stdSimplex.δ 2 := rfl

abbrev pt₀ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 0)
abbrev pt₁ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 1)

lemma sq_commutes : pt₁ ≫ ι₀ = pt₀ ≫ ι₂ := by
  apply (instMonoι Λ[2, 1]).right_cancellation
  symm
  exact @stdSimplex.δ_comp_δ _ _ _ 0 1 (by norm_num)

def pushout : Limits.PushoutCocone pt₁ pt₀
  := Limits.PushoutCocone.mk ι₀ ι₂ sq_commutes

-- TODO Joel's PRs (see e.g. mathlib PR #23872) proves this and more
def pushoutIsPushout : Limits.IsColimit pushout := by sorry

end horn₂₁

/-!
Various constructions and statements about the (multi)coequalizer
`⨿ Δ[1] ⇉ ⨿ Δ[2] → Λ[3, 1]` (for more detail, see Goerss & Jardine Lemma 3.1)
-/
namespace horn₃₁

abbrev ι₀ : Δ[2] ⟶ Λ[3, 1] := hornFaceIncl 1 0 (by norm_num)
abbrev ι₂ : Δ[2] ⟶ Λ[3, 1] := hornFaceIncl 1 2 (by decide)
abbrev ι₃ : Δ[2] ⟶ Λ[3, 1] := hornFaceIncl 1 3 (by decide)

lemma incl₀ : ι₀ ≫ Λ[3, 1].ι = stdSimplex.δ 0 := rfl
lemma incl₂ : ι₂ ≫ Λ[3, 1].ι = stdSimplex.δ 2 := rfl
lemma incl₃ : ι₃ ≫ Λ[3, 1].ι = stdSimplex.δ 3 := rfl

/--
Index types for the left (indexed by the three edges attached to the vertex 1)
and right (indexed by the three faces of `Λ[3, 1]`) coproducts in the coequalizer.
-/
inductive L where
  | e₀₁ : L
  | e₁₂ : L
  | e₁₃ : L

inductive R where
  | f₀ : R
  | f₂ : R
  | f₃ : R

def J : Limits.MultispanShape where
  L := L
  R := R
  fst e := match e with
    | L.e₀₁ => R.f₂
    | L.e₁₂ => R.f₃
    | L.e₁₃ => R.f₀
  snd e := match e with
    | L.e₀₁ => R.f₃
    | L.e₁₂ => R.f₀
    | L.e₁₃ => R.f₂

open SimplexCategory

/--
The multispan is of the form `⨿ Δ[1] ⇉ ⨿ Δ[2]` where
the `fst` and `snd` maps `Δ[1] ⟶ Δ[2]` are chosen
to be consistent to their layout in `Λ[3, 1]`.
-/
def multispanIndex : Limits.MultispanIndex J SSet where
  left _ := Δ[1]
  right _ := Δ[2]
  fst e := match e with
    | L.e₀₁ => stdSimplex.δ 2
    | L.e₁₂ => stdSimplex.δ 0
    | L.e₁₃ => stdSimplex.δ 1
  snd e := match e with
    | L.e₀₁ => stdSimplex.δ 2
    | L.e₁₂ => stdSimplex.δ 2
    | L.e₁₃ => stdSimplex.δ 0

def π : R → (Δ[2] ⟶ Λ[3, 1]) := fun e ↦ match e with
  | R.f₀ => hornFaceIncl 1 0 (by norm_num)
  | R.f₂ => hornFaceIncl 1 2 (by simp)
  | R.f₃ => hornFaceIncl 1 3 (by simp)

lemma fork_comm : ∀ p : L, multispanIndex.fst p ≫ π (J.fst p)
    = multispanIndex.snd p ≫ π (J.snd p) := by
  rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
  all_goals
    dsimp only [multispanIndex, J, π]
    apply (instMonoι Λ[3, 1]).right_cancellation
    rw [Category.assoc, horn_face_δ, Category.assoc, horn_face_δ]
  . symm; exact @stdSimplex.δ_comp_δ _ _ 1 2 2 (by rfl)
  . exact @stdSimplex.δ_comp_δ _ _ 1 0 2 (by norm_num)
  . symm; exact @stdSimplex.δ_comp_δ _ _ 1 0 1 (by norm_num)

def multicofork := Limits.Multicofork.ofπ multispanIndex Λ[3, 1] π fork_comm

-- TODO this should be also handled by Joel's PR (e.g. mathlib pr #23872)
def isMulticoeq : Limits.IsColimit multicofork := by sorry

end horn₃₁

/-!
Various constructions and statements about the (multi)coequalizer
`⨿ Δ[1] ⇉ ⨿ Δ[2] → Λ[3, 2]` (for more detail, see Goerss & Jardine Lemma 3.1)
-/
namespace horn₃₂

abbrev ι₀ : Δ[2] ⟶ Λ[3, 2] := hornFaceIncl 2 0 (by decide)
abbrev ι₁ : Δ[2] ⟶ Λ[3, 2] := hornFaceIncl 2 1 (by decide)
abbrev ι₃ : Δ[2] ⟶ Λ[3, 2] := hornFaceIncl 2 3 (by decide)

lemma incl₀ : ι₀ ≫ Λ[3, 2].ι = stdSimplex.δ 0 := rfl
lemma incl₁ : ι₁ ≫ Λ[3, 2].ι = stdSimplex.δ 1 := rfl
lemma incl₃ : ι₃ ≫ Λ[3, 2].ι = stdSimplex.δ 3 := rfl

/--
Index types for the left (indexed by the three edges attached to the vertex 2)
and right (indexed by the three faces of `Λ[3, 2]`) coproducts in the coequalizer.
-/
inductive L where
  | e₀₂ : L
  | e₁₂ : L
  | e₂₃ : L

inductive R where
  | f₀ : R
  | f₁ : R
  | f₃ : R

def J : Limits.MultispanShape where
  L := L
  R := R
  fst e := match e with
    | L.e₀₂ => R.f₁
    | L.e₁₂ => R.f₃
    | L.e₂₃ => R.f₀
  snd e := match e with
    | L.e₀₂ => R.f₃
    | L.e₁₂ => R.f₀
    | L.e₂₃ => R.f₁

open SimplexCategory

/--
The multispan is of the form `⨿ Δ[1] ⇉ ⨿ Δ[2]` where
the `fst` and `snd` maps `Δ[1] ⟶ Δ[2]` are chosen
to be consistent to their layout in `Λ[3, 2]`.
-/
def multispanIndex : Limits.MultispanIndex J SSet where
  left _ := Δ[1]
  right _ := Δ[2]
  fst e := match e with
    | L.e₀₂ => stdSimplex.δ 2
    | L.e₁₂ => stdSimplex.δ 0
    | L.e₂₃ => stdSimplex.δ 0
  snd e := match e with
    | L.e₀₂ => stdSimplex.δ 1
    | L.e₁₂ => stdSimplex.δ 2
    | L.e₂₃ => stdSimplex.δ 0

def π : R → (Δ[2] ⟶ Λ[3, 2]) := fun e ↦ match e with
  | R.f₀ => hornFaceIncl 2 0 (by simp)
  | R.f₁ => hornFaceIncl 2 1 (by simp)
  | R.f₃ => hornFaceIncl 2 3 (by simp)

lemma fork_comm : ∀ p : L, multispanIndex.fst p ≫ π (J.fst p)
    = multispanIndex.snd p ≫ π (J.snd p) := by
  rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
  all_goals
    dsimp only [multispanIndex, J, π]
    apply (instMonoι Λ[3, 2]).right_cancellation
    rw [Category.assoc, horn_face_δ, Category.assoc, horn_face_δ]
  . symm; exact @stdSimplex.δ_comp_δ _ _ 1 1 2 (by simp)
  . exact @stdSimplex.δ_comp_δ _ _ 1 0 2 (by norm_num)
  . exact @stdSimplex.δ_comp_δ _ _ 1 0 0 (by rfl)

def multicofork := Limits.Multicofork.ofπ multispanIndex Λ[3, 2] π fork_comm

-- TODO this should be also handled by Joel's PR
def multicoforkIsMulticoeq : Limits.IsColimit multicofork := by sorry

end horn₃₂
end SSet
