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
Index types for the left and right coproducts in the coequalizer.
-/
def R := { x : Fin 4 // x ≠ 1 }
def L := { p : R × R // p.1.val < p.2.val }

def J : Limits.MultispanShape where
    L := L
    R := R
    fst p := p.val.1
    snd p := p.val.2

open SimplexCategory

def multispanIndex : Limits.MultispanIndex J SSet where
  left  _ := Δ[1]
  right _ := Δ[2]
  fst p := stdSimplex.map (δ (Fin.pred p.val.2.val (Fin.ne_zero_of_lt p.property)).castSucc)
  snd p := stdSimplex.map (δ p.val.1.val)

def π : R → (Δ[2] ⟶ Λ[3, 1]) := fun ⟨x, h⟩ ↦ hornFaceIncl 1 x h

lemma fork_comm : ∀ p : L, multispanIndex.fst p ≫ π (J.fst p)
    = multispanIndex.snd p ≫ π (J.snd p) := by
  rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
  dsimp only [multispanIndex, J, π]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    apply (instMonoι Λ[3, 1]).right_cancellation
    dsimp only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, ne_eq, Fin.zero_eta, Fin.reducePred,
      Fin.castSucc_one, Fin.val_one, Fin.val_zero]
    rw [Category.assoc, Category.assoc]
    symm
  exact @stdSimplex.δ_comp_δ _ _ _ 0 1 (by norm_num)
  exact @stdSimplex.δ_comp_δ _ _ _ 0 2 (by norm_num)
  exact @stdSimplex.δ_comp_δ _ _ _ 2 2 (by norm_num)

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

def R := { x : Fin 4 // x ≠ 2 }
def L := { p : R × R // p.1.val < p.2.val }

def J : Limits.MultispanShape where
    L := L
    R := R
    fst p := p.val.1
    snd p := p.val.2

open SimplexCategory

def multispanIndex : Limits.MultispanIndex J SSet where
  left  _ := Δ[1]
  right _ := Δ[2]
  fst p := stdSimplex.map (δ (Fin.pred p.val.2.val (Fin.ne_zero_of_lt p.property)).castSucc)
  snd p := stdSimplex.map (δ p.val.1.val)

def π : R → (Δ[2] ⟶ Λ[3, 2]) := fun ⟨x, h⟩ ↦ hornFaceIncl 2 x h

lemma fork_comm : ∀ p : L, multispanIndex.fst p ≫ π (J.fst p)
    = multispanIndex.snd p ≫ π (J.snd p) := by
  rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
  dsimp only [multispanIndex, J, π]
  apply (instMonoι Λ[3, 2]).right_cancellation
  rw [Category.assoc, Category.assoc, horn_face_δ, horn_face_δ]
  dsimp [CosimplicialObject.δ]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    dsimp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one, ne_eq, Fin.zero_eta, Fin.pred_one]
  . rfl
  . symm; exact @SimplexCategory.δ_comp_δ' 1 0 3 (by decide)
  . symm; exact @SimplexCategory.δ_comp_δ' 1 1 3 (by decide)

def multicofork := Limits.Multicofork.ofπ multispanIndex Λ[3, 2] π fork_comm

-- TODO this should be also handled by Joel's PR
def multicoforkIsMulticoeq : Limits.IsColimit multicofork := by sorry

end horn₃₂
end SSet
