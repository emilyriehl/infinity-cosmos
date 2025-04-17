import Mathlib.AlgebraicTopology.SimplicialSet.Horn

namespace horn₂₁

open Simplicial CategoryTheory SSet

--
-- all statements about the pushout
-- Δ[0]  →  Δ[1]
--  ↓        ↓
-- Δ[1]  → Λ[2, 1]
-- are left as sorries, see Joel's PRs (TODO) proving these

-- define the natural maps Δ[1] ⟶ Λ[2, 1] selecting the nontrivial edges
def horn21_incl (i : Fin 3) (h : i ≠ 1)
  : Δ[1] ⟶ Λ[2, 1] := yonedaEquiv.symm (horn.face 1 i h)

def hornTwo_edge₀ : Δ[1] ⟶ Λ[2, 1] := horn21_incl 0 (by norm_num)
def hornTwo_edge₂ : Δ[1] ⟶ Λ[2, 1] := horn21_incl 2 (by omega)

def pt₀ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 0)
def pt₁ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 1)

lemma sq_commutes : pt₁ ≫ hornTwo_edge₀ = pt₀ ≫ hornTwo_edge₂ := by
  apply (instMonoι Λ[2, 1]).right_cancellation
  symm
  exact @stdSimplex.δ_comp_δ _ _ _ 0 1 (by norm_num)

def horn_pushout : Limits.PushoutCocone pt₁ pt₀
  := Limits.PushoutCocone.mk hornTwo_edge₀ hornTwo_edge₂ sq_commutes

def horn_is_pushout : Limits.IsColimit horn_pushout := by sorry

end horn₂₁

namespace horn₃₁

open Simplicial CategoryTheory SSet

def horn31_incl (i : Fin 4) (h : i ≠ 1)
  : Δ[2] ⟶ Λ[3, 1] := yonedaEquiv.symm (horn.face 1 i h)

abbrev ι₀ : Δ[2] ⟶ Λ[3, 1] := horn31_incl 0 (by norm_num)
abbrev ι₂ : Δ[2] ⟶ Λ[3, 1] := horn31_incl 2 (by omega)
abbrev ι₃ : Δ[2] ⟶ Λ[3, 1] := horn31_incl 3 (by omega)

def R := { x : Fin 4 // x ≠ 1 }
def L := { p : R × R // p.1.val < p.2.val }

def J : Limits.MultispanShape where
    L := L
    R := R
    fst p := p.val.1
    snd p := p.val.2

open SimplexCategory

def multispan_index : Limits.MultispanIndex J SSet where
  left  _ := Δ[1]
  right _ := Δ[2]
  fst p := stdSimplex.map (δ (Fin.pred p.val.2.val (Fin.ne_zero_of_lt p.property)).castSucc)
  snd p := stdSimplex.map (δ p.val.1.val)

def π : R → (Δ[2] ⟶ Λ[3, 1]) := fun ⟨x, h⟩ ↦ horn31_incl x h

#check CosimplicialObject.δ stdSimplex
#check @CosimplicialObject.δ_comp_δ SSet _ stdSimplex
#check @stdSimplex.δ_comp_δ SSet _ 2 1 2
#check Fin.le_of_lt

def fork_comm : ∀ p : L, multispan_index.fst p ≫ π (J.fst p)
  = multispan_index.snd p ≫ π (J.snd p) := by
    rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
    dsimp only [multispan_index, J, π]
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals
      apply (instMonoι Λ[3, 1]).right_cancellation
      dsimp
      rw [Category.assoc, Category.assoc]
      symm
    exact @stdSimplex.δ_comp_δ _ _ _ 0 1 (by norm_num)
    exact @stdSimplex.δ_comp_δ _ _ _ 0 2 (by norm_num)
    exact @stdSimplex.δ_comp_δ _ _ _ 2 2 (by norm_num)

#check stdSimplex.δ_comp_δ (Fin.le_of_lt Fin.zero_lt_one)

def multicofork_horn := Limits.Multicofork.ofπ multispan_index Λ[3, 1] π fork_comm

-- TODO this should be also handled by Joel's PR
def isMulticoeq : Limits.IsColimit multicofork_horn := by sorry

end horn₃₁
