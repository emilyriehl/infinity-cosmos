import Mathlib.AlgebraicTopology.SimplicialSet.Horn

namespace horn₂₁

open Simplicial CategoryTheory SSet

--
-- all statements about the pushout
-- Δ[0]  →  Δ[1]
--  ↓        ↓
-- Δ[1]  → Λ[2, 1]
-- are left as sorries, see Joel's PRs (TODO) proving these
--

-- TODO explicit universes
universe u

-- define the natural maps Δ[1] ⟶ Λ[2, 1] selecting the nontrivial edges
def e₀ := horn.edge 2 1 1 2 (Fin.le_iff_val_le_val.2 (by norm_num)) (by aesop)
def e₂ := horn.edge 2 1 0 1 (by norm_num) (by norm_num)

def hornTwo_edge₀ : Δ[1] ⟶ Λ[2, 1] := yonedaEquiv.symm e₀
def hornTwo_edge₂ : Δ[1] ⟶ Λ[2, 1] := yonedaEquiv.symm e₂

def pt₀ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 0)
def pt₁ : Δ[0] ⟶ Δ[1] := stdSimplex.map (SimplexCategory.δ 1)

lemma is_std_edge₀ : hornTwo_edge₀ ≫ Λ[2, 1].ι = stdSimplex.map.{u} (SimplexCategory.δ 0)
  := by
  let Δ2_edge₀ := stdSimplex.edge.{u} 2 1 2 (by apply Fin.le_iff_val_le_val.2; norm_num)
  have is_std_edge₀' : Λ[2, 1].ι.app _ e₀ = Δ2_edge₀ := by rfl
  have edge_eq₀ : Δ2_edge₀ = stdSimplex.objEquiv.symm.{u} (SimplexCategory.δ 0)
    := by
    apply stdSimplex.objEquiv.apply_eq_iff_eq_symm_apply.1
    ext x; fin_cases x <;> aesop
  apply yonedaEquiv.apply_eq_iff_eq.1
  dsimp only [hornTwo_edge₀]
  rw [stdSimplex.yonedaEquiv_map]
  rw [← edge_eq₀, ← is_std_edge₀']
  aesop

-- TODO this is symmetric to the above so should be generalized!
lemma is_std_edge₂ : hornTwo_edge₂ ≫ Λ[2, 1].ι = stdSimplex.map.{u} (SimplexCategory.δ 2)
  := by sorry

def horn_pushout : Limits.PushoutCocone pt₁ pt₀ := Limits.PushoutCocone.mk hornTwo_edge₀ hornTwo_edge₂
  (by
    apply (instMonoι Λ[2, 1]).right_cancellation
    rw [Category.assoc, is_std_edge₀, Category.assoc, is_std_edge₂]
    dsimp only [pt₀, pt₁]
    rw [← Functor.map_comp, ← Functor.map_comp]
    have : SimplexCategory.δ 1 ≫ SimplexCategory.δ 0 = SimplexCategory.δ 0 ≫ @SimplexCategory.δ 1 2
      := (@SimplexCategory.δ_comp_δ 0 0 1 (by norm_num)).symm
    rw [this])

def horn_is_pushout : Limits.IsColimit horn_pushout := by sorry

end horn₂₁


namespace horn₃₁
universe u

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
    have aux i h : horn31_incl i h ≫ Λ[3, 1].ι = stdSimplex.δ i := rfl
    rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
    dsimp only [multispan_index, J, π]
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals
      apply (instMonoι Λ[3, 1]).right_cancellation
      dsimp
      rw [Category.assoc, Category.assoc, aux, aux]
      symm
    exact @stdSimplex.δ_comp_δ _ _ _ 0 1 (by norm_num)
    exact @stdSimplex.δ_comp_δ _ _ _ 0 2 (by norm_num)
    exact @stdSimplex.δ_comp_δ _ _ _ 2 2 (by norm_num)

#check stdSimplex.δ_comp_δ (Fin.le_of_lt Fin.zero_lt_one)

def multicofork_horn := Limits.Multicofork.ofπ multispan_index Λ[3, 1] π fork_comm

-- TODO this should be also handled by Joel's PR
def isMulticoeq : Limits.IsColimit multicofork_horn := by sorry

end horn₃₁
