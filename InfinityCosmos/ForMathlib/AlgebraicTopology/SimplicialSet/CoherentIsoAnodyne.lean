/-
Copyright (c) 2026 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

open CategoryTheory Simplicial SimplicialObject Opposite

namespace SSet

universe u

/-- The alternating `n`-simplex of `coherentIso`, starting at the given vertex. -/
noncomputable def coherentIso.altSimplex (n : ℕ) (start : Fin 2) : coherentIso _⦋n⦌ :=
  coherentIso.equivFun.symm (fun i => ⟨(start.val + i.val) % 2, Nat.mod_lt _ (by norm_num)⟩)

namespace coherentIso

lemma equivFun_homInclusion_app {n : ℕ} (y : (Δ[1] : SSet) _⦋n⦌)
    (j : Fin (n + 1)) :
    equivFun (homInclusion.app (op ⦋n⦌) y) j = y j := by
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective y
  rw [homInclusion, yonedaEquiv_symm_app_objEquiv_symm]
  change ULift.down (hom.edge.obj (f.toOrderHom j)) = f.toOrderHom j
  by_cases h : f.toOrderHom j = 0
  · rw [h]
    rfl
  · rw [Fin.eq_one_of_ne_zero _ h]
    rfl

lemma mem_range_homInclusion_iff {n : ℕ} {x : coherentIso _⦋n⦌} :
    x ∈ (Subcomplex.range homInclusion).obj (op ⦋n⦌) ↔ Monotone (equivFun x) := by
  constructor
  · rintro ⟨y, rfl⟩
    intro a b h
    rw [equivFun_homInclusion_app y a, equivFun_homInclusion_app y b]
    exact stdSimplex.monotone_apply y h
  · intro hx
    let y : (Δ[1] : SSet) _⦋n⦌ := stdSimplex.objMk (n := ⦋1⦌) (m := op ⦋n⦌)
      { toFun := equivFun x, monotone' := hx }
    refine ⟨y, ?_⟩
    apply equivFun.injective
    funext j
    rw [equivFun_homInclusion_app y j]
    rfl

lemma val_equivFun_altSimplex (n : ℕ) (start : Fin 2) (j : Fin (n + 1)) :
    (equivFun (altSimplex n start) j).val = (start.val + j.val) % 2 := rfl

lemma equivFun_σ {n : ℕ} (i : Fin (n + 1)) (x : coherentIso _⦋n⦌) (j : Fin (n + 2)) :
    equivFun (coherentIso.σ i x) j = equivFun x (i.predAbove j) := rfl

lemma equivFun_δ {n : ℕ} (i : Fin (n + 2)) (x : coherentIso _⦋n + 1⦌)
    (j : Fin (n + 1)) :
    equivFun (coherentIso.δ i x) j = equivFun x (i.succAbove j) := rfl

lemma exists_adjacent_eq_of_degenerate {n : ℕ} {x : coherentIso _⦋n + 1⦌}
    (hx : x ∈ coherentIso.degenerate (n + 1)) :
    ∃ i : Fin (n + 1), equivFun x i.castSucc = equivFun x i.succ := by
  rw [degenerate_eq_iUnion_range_σ] at hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨i, y, rfl⟩ := hx
  exact ⟨i, by rw [equivFun_σ, equivFun_σ, Fin.predAbove_castSucc_self,
    Fin.predAbove_succ_self]⟩

lemma degenerate_of_adjacent_eq {n : ℕ} {x : coherentIso _⦋n + 1⦌} {i : Fin (n + 1)}
    (h : equivFun x i.castSucc = equivFun x i.succ) :
    x ∈ coherentIso.degenerate (n + 1) := by
  rw [degenerate_eq_iUnion_range_σ]
  refine Set.mem_iUnion.2 ⟨i, coherentIso.δ i.castSucc x, ?_⟩
  apply equivFun.injective
  funext j
  rw [equivFun_σ, equivFun_δ]
  by_cases hj : j = i.castSucc
  · subst hj
    rw [Fin.predAbove_castSucc_self, Fin.succAbove_of_le_castSucc _ _ (le_refl _)]
    exact h.symm
  · rw [Fin.succAbove_predAbove hj]

lemma mem_nonDegenerate_iff {n : ℕ} (x : coherentIso _⦋n + 1⦌) :
    x ∈ coherentIso.nonDegenerate (n + 1) ↔
      ∀ i : Fin (n + 1), equivFun x i.castSucc ≠ equivFun x i.succ := by
  rw [mem_nonDegenerate_iff_notMem_degenerate]
  exact ⟨fun hx i hi => hx (degenerate_of_adjacent_eq hi),
    fun hx hdeg => let ⟨i, hi⟩ := exists_adjacent_eq_of_degenerate hdeg; hx i hi⟩

lemma altSimplex_nonDegenerate (n : ℕ) (start : Fin 2) :
    altSimplex n start ∈ coherentIso.nonDegenerate n := by
  cases n with
  | zero =>
      rw [nondegenerate_zero]
      trivial
  | succ m =>
      rw [mem_nonDegenerate_iff]
      intro i hi
      have hv := congrArg Fin.val hi
      simp only [val_equivFun_altSimplex, Fin.val_castSucc, Fin.val_succ] at hv
      omega

lemma not_monotone_altSimplex_zero (s : ℕ) :
    ¬ Monotone (equivFun (altSimplex (s + 2) 0)) := by
  intro h
  let i : Fin ((s + 2) + 1) := ⟨1, by omega⟩
  let j : Fin ((s + 2) + 1) := ⟨2, by omega⟩
  have hle : i ≤ j := by
    rw [Fin.le_iff_val_le_val]
    change (1 : ℕ) ≤ 2
    omega
  have hbad := h hle
  have hv := Fin.le_iff_val_le_val.1 hbad
  norm_num [i, j, val_equivFun_altSimplex] at hv

lemma not_monotone_altSimplex_one (s : ℕ) :
    ¬ Monotone (equivFun (altSimplex (s + 1) 1)) := by
  intro h
  let i : Fin ((s + 1) + 1) := ⟨0, by omega⟩
  let j : Fin ((s + 1) + 1) := ⟨1, by omega⟩
  have hle : i ≤ j := by
    rw [Fin.le_iff_val_le_val]
    change (0 : ℕ) ≤ 1
    omega
  have hbad := h hle
  have hv := Fin.le_iff_val_le_val.1 hbad
  norm_num [i, j, val_equivFun_altSimplex] at hv

lemma δ_zero_altSimplex (n : ℕ) (start : Fin 2) :
    coherentIso.δ (0 : Fin (n + 2)) (altSimplex (n + 1) start) =
      altSimplex n (start + 1) := by
  apply equivFun.injective
  ext j
  rw [equivFun_δ, val_equivFun_altSimplex, val_equivFun_altSimplex,
    Fin.succAbove_zero, Fin.val_succ]
  fin_cases start <;> omega

lemma eq_altSimplex_of_alternating {n : ℕ} (x : coherentIso _⦋n⦌)
    (h : ∀ i : Fin n, equivFun x i.castSucc ≠ equivFun x i.succ) :
    x = altSimplex n (equivFun x 0) := by
  apply equivFun.injective
  funext j
  apply Fin.val_injective
  rw [val_equivFun_altSimplex]
  induction j using Fin.induction with
  | zero =>
      simp [Nat.mod_eq_of_lt (equivFun x 0).isLt]
  | succ i ih =>
      have hv : (equivFun x i.castSucc).val ≠ (equivFun x i.succ).val :=
        fun e => h i (Fin.val_injective e)
      have b0 := (equivFun x i.succ).isLt
      have b1 := (equivFun x i.castSucc).isLt
      rw [Fin.val_castSucc] at ih
      rw [Fin.val_succ]
      omega

lemma eq_altSimplex_of_nonDegenerate {n : ℕ} {x : coherentIso.{u} _⦋n⦌}
    (hx : x ∈ coherentIso.nonDegenerate n) :
    x = altSimplex n (equivFun x 0) := by
  cases n with
  | zero =>
      exact eq_altSimplex_of_alternating x (by intro i; exact Fin.elim0 i)
  | succ m =>
      exact eq_altSimplex_of_alternating x ((mem_nonDegenerate_iff x).1 hx)

lemma monotone_altSimplex_zero (start : Fin 2) :
    Monotone (equivFun (altSimplex 0 start : coherentIso.{u} _⦋0⦌)) := by
  intro a b h
  fin_cases a
  fin_cases b
  rfl

lemma monotone_altSimplex_one_zero :
    Monotone (equivFun (altSimplex 1 0 : coherentIso.{u} _⦋1⦌)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [Fin.le_iff_val_le_val, val_equivFun_altSimplex] at h ⊢

/-- The Moss pairing core for the range of the forward-edge inclusion
`Δ[1] ⟶ coherentIso`. -/
noncomputable def homInclusionRangePairingCore :
    (Subcomplex.range homInclusion.{u}).PairingCore where
  ι := ℕ
  dim s := s + 1
  simplex s := altSimplex (s + 2) 0
  index s := 0
  nonDegenerate₁ s := by
    exact altSimplex_nonDegenerate (s + 2) 0
  nonDegenerate₂ s := by
    rw [δ_zero_altSimplex]
    exact altSimplex_nonDegenerate (s + 1) (0 + 1)
  notMem₁ s := by
    rw [mem_range_homInclusion_iff]
    exact not_monotone_altSimplex_zero.{u} s
  notMem₂ s := by
    rw [δ_zero_altSimplex]
    rw [mem_range_homInclusion_iff]
    exact not_monotone_altSimplex_one.{u} s
  injective_type₁' := by
    intro s t h
    have hd := S.dim_eq_of_mk_eq h
    omega
  injective_type₂' := by
    intro s t h
    rw [δ_zero_altSimplex, δ_zero_altSimplex] at h
    have hd := S.dim_eq_of_mk_eq h
    omega
  type₁_ne_type₂' := by
    intro s t h
    rw [δ_zero_altSimplex] at h
    have hd := S.dim_eq_of_mk_eq h
    obtain rfl : t = s + 1 := by omega
    have hx : altSimplex (s + 2) 0 = altSimplex (s + 1 + 1) (0 + 1) := by
      simpa using
        (S.ext_iff (altSimplex (s + 2) 0) (altSimplex (s + 1 + 1) (0 + 1))).1 h
    have hv := congrArg (fun x => equivFun x 0) hx
    have hvv := congrArg Fin.val hv
    norm_num [val_equivFun_altSimplex] at hvv
  surjective' := by
    intro x
    obtain ⟨n, y, hy, hyNot, rfl⟩ := Subcomplex.N.mk_surjective x
    have hyAlt := eq_altSimplex_of_nonDegenerate hy
    have hnotMono : ¬ Monotone (equivFun y) := by
      intro hmono
      exact hyNot ((mem_range_homInclusion_iff).2 hmono)
    by_cases hstart : equivFun y 0 = 0
    · cases n with
      | zero =>
          exfalso
          apply hnotMono
          rw [hyAlt, hstart]
          exact monotone_altSimplex_zero.{u} 0
      | succ n =>
          cases n with
          | zero =>
              exfalso
              apply hnotMono
              rw [hyAlt, hstart]
              exact monotone_altSimplex_one_zero.{u}
          | succ s =>
              refine ⟨s, Or.inl ?_⟩
              change S.mk y = S.mk (altSimplex (s + 2) 0)
              rw [hyAlt, hstart]
    · have hstart1 : equivFun y 0 = 1 := Fin.eq_one_of_ne_zero _ hstart
      cases n with
      | zero =>
          exfalso
          apply hnotMono
          rw [hyAlt, hstart1]
          exact monotone_altSimplex_zero.{u} 1
      | succ s =>
          refine ⟨s, Or.inr ?_⟩
          rw [δ_zero_altSimplex]
          change S.mk y = S.mk (altSimplex (s + 1) (0 + 1))
          rw [hyAlt, hstart1]
          rfl

lemma δ_altSimplex_zero_eq_iff (s : ℕ) (i : Fin (s + 1 + 2)) :
    coherentIso.δ i (altSimplex (s + 2) (0 : Fin 2) : coherentIso.{u} _⦋s + 2⦌) =
      coherentIso.δ (0 : Fin (s + 1 + 2)) (altSimplex (s + 2) 0) ↔ i = 0 := by
  constructor
  · intro hi
    by_contra hi0
    have hv := congrArg (fun z => equivFun z (0 : Fin (s + 1 + 1))) hi
    rw [equivFun_δ, equivFun_δ, Fin.succAbove_ne_zero_zero hi0, Fin.succAbove_zero] at hv
    have hvv := congrArg Fin.val hv
    norm_num [val_equivFun_altSimplex] at hvv
  · rintro rfl
    rfl

lemma homInclusionRangePairingCore_isUniquelyCodimOneFace (s : ℕ) :
    S.IsUniquelyCodimOneFace
      (homInclusionRangePairingCore.{u}.type₂ s).toS
      (homInclusionRangePairingCore.{u}.type₁ s).toS := by
  dsimp [homInclusionRangePairingCore, Subcomplex.PairingCore.type₁,
    Subcomplex.PairingCore.type₂]
  change S.IsUniquelyCodimOneFace
    (S.mk (coherentIso.δ (0 : Fin (s + 1 + 2))
      (altSimplex (s + 2) (0 : Fin 2) : coherentIso.{u} _⦋s + 2⦌)))
    (S.mk (altSimplex (s + 2) (0 : Fin 2)))
  rw [S.IsUniquelyCodimOneFace.iff]
  refine ⟨0, rfl, ?_⟩
  intro i hi
  exact (δ_altSimplex_zero_eq_iff.{u} s i).1 hi

instance homInclusionRangePairingCore_isProper :
    homInclusionRangePairingCore.{u}.IsProper where
  isUniquelyCodimOneFace s :=
    homInclusionRangePairingCore_isUniquelyCodimOneFace (s : ℕ)

/-- The natural-number rank function for the Moss pairing on `range homInclusion`. -/
noncomputable def homInclusionRangePairingCoreRankFunction :
    homInclusionRangePairingCore.{u}.RankFunction ℕ where
  rank s := (s : ℕ)
  lt := by
    intro x y hxy
    have hne : x ≠ y := hxy.1
    have hltN : (homInclusionRangePairingCore.{u}.type₂ x).toN <
        (homInclusionRangePairingCore.{u}.type₁ y).toN := by
      simpa [Subcomplex.N.lt_iff] using hxy.2
    have hdim := SSet.N.dim_lt_of_lt hltN
    rw [Subcomplex.PairingCore.type₂_dim, Subcomplex.PairingCore.type₁_dim] at hdim
    dsimp [homInclusionRangePairingCore] at x y hne hdim ⊢
    omega

instance homInclusionRangePairingCore_isRegular :
    homInclusionRangePairingCore.{u}.IsRegular :=
  homInclusionRangePairingCoreRankFunction.isRegular

instance homInclusion_mono : Mono homInclusion.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro y z h
  cases n using Opposite.rec
  rename_i n
  cases n using SimplexCategory.rec
  rename_i n
  ext j
  have hf := congrArg (fun x => equivFun x j) h
  rw [equivFun_homInclusion_app y j, equivFun_homInclusion_app z j] at hf
  exact congrArg Fin.val hf

theorem homInclusionRange_anodyneExtensions :
    anodyneExtensions (Subcomplex.range homInclusion.{u}).ι :=
  homInclusionRangePairingCore.{u}.pairing.anodyneExtensions

theorem homInclusion_anodyneExtensions : anodyneExtensions homInclusion.{u} := by
  rw [← Subcomplex.toRange_ι homInclusion.{u}]
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
    homInclusionRange_anodyneExtensions

end coherentIso

end SSet
