/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.FibrationConservative
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
/-!
# Terminal-base reduction for the last outer-horn lifting

Reduces the right lifting property of a left fibration over a terminal object against the last
outer horn `Λ[n+1, last].ι` to the special-outer-horn filler. Everything except the filler itself
is discharged here from the proven inputs: quasicategoricity of the source
(`quasicategory_of_leftFibration_isTerminal`, via the in-tree `quasicategory_iff_of_isTerminal`),
the lifting reduction `rlp_rightHorn_of_isTerminal_of_fill`, the invertible-final-edge
side-condition (free over a terminal base, by conservativity `leftFibration_conservative`), and
the dimension-1 base case `fill_lastHorn_dim1`. The packaged
`leftFibration_rlp_rightHorn_of_isTerminal_of_fillLast` takes the `i = last` filler as the
hypothesis `hfill`; that filler is `SpecialOuterHorn.fill_last`, supplied in
`CoherentIsoLiftClose`.
-/
open CategoryTheory Simplicial Opposite Finset Limits MorphismProperty
universe u
namespace SSet

/-! ## Reduction (from proven inputs): lifting over a terminal base = filling the horn in `X`. -/

theorem rlp_rightHorn_of_isTerminal_of_fill {X Y : SSet.{u}} (p : X ⟶ Y) (hY : IsTerminal Y)
    {n : ℕ}
    (hfill : ∀ (τ : (Λ[n + 1, Fin.last (n + 1)] : SSet.{u}) ⟶ X),
        ∃ σ : Δ[n + 1] ⟶ X, τ = Λ[n + 1, Fin.last (n + 1)].ι ≫ σ) :
    HasLiftingProperty (Λ[n + 1, Fin.last (n + 1)].ι) p := by
  refine ⟨fun {u v} sq => ?_⟩
  obtain ⟨σ, hσ⟩ := hfill u
  exact ⟨⟨{ l := σ, fac_left := hσ.symm, fac_right := hY.hom_ext _ _ }⟩⟩

/-! ## Conservativity payoff (from proven inputs): over a terminal base every edge of `X` is iso. -/

theorem quasicategory_of_leftFibration_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] : Quasicategory X :=
  (quasicategory_iff_of_isTerminal p hY).mpr inferInstance

theorem map_edge_isIsoSimplex_of_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) {x₀ x₁ : X _⦋0⦌} (g : Edge x₀ x₁) :
    IsIsoSimplex (g.map p).edge := by
  have hsub : Subsingleton (Y _⦋1⦌) := by
    have ht : IsTerminal (Y.obj (op ⦋1⦌)) := hY.isTerminalObj ((evaluation _ _).obj (op ⦋1⦌)) Y
    haveI : Unique (Y _⦋1⦌) := Types.isTerminalEquivUnique _ ht
    infer_instance
  have heq : (g.map p).edge = (Edge.id (p.app (op ⦋0⦌) x₀)).edge := Subsingleton.elim _ _
  rw [heq]; exact isIsoSimplex_id _

theorem edge_isIso_of_leftFibration_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] {x₀ x₁ : X _⦋0⦌} (g : Edge x₀ x₁) :
    Nonempty g.IsIso :=
  haveI := quasicategory_of_leftFibration_isTerminal p hY
  leftFibration_conservative g
    (Edge.isIso_of_isIsoSimplex _ (map_edge_isIsoSimplex_of_isTerminal p hY g))

/-- Every 1-simplex of `X` is an iso simplex; the invertibility side-condition is free. -/
theorem isIsoSimplex_of_leftFibration_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] (s : X _⦋1⦌) : IsIsoSimplex s := by
  obtain ⟨he⟩ := edge_isIso_of_leftFibration_isTerminal p hY (Edge.mk s rfl rfl)
  exact isIsoSimplex_of_edge he

/-! ## The special-outer-horn gap and the dim-1 base case. -/

/-- Final edge `[n+1, n+2]` of `Λ[n+2, last]`. -/
def finalEdge {n : ℕ} : (Λ[n + 2, (Fin.last (n + 2))] : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) (Fin.last (n + 2)) ⟨n + 1, by omega⟩ (Fin.last (n + 2))
    (by simp [Fin.le_def]) (by
    have hset : ({(Fin.last (n + 2)), (⟨n + 1, by omega⟩ : Fin (n + 3)),
        (Fin.last (n + 2))} : Finset (Fin (n + 3))) = {⟨n + 1, by omega⟩, Fin.last (n + 2)} := by
      ext x; simp [or_comm]
    rw [hset, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]; omega)

theorem fill_lastHorn_dim1 {X : SSet.{u}} (τ : (Λ[1, Fin.last 1] : SSet.{u}) ⟶ X) :
    ∃ σ : Δ[1] ⟶ X, τ = Λ[1, Fin.last 1].ι ≫ σ := by
  refine ⟨stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)
      ≫ horn.ι (Fin.last 1) 0 (by decide) ≫ τ, ?_⟩
  apply horn.hom_ext
  intro j hj
  have hjeq : j = 0 := by
    fin_cases j
    · rfl
    · exact absurd rfl hj
  subst hjeq
  rw [← horn.yonedaEquiv_ι (Fin.last 1) 0 hj, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
  apply congrArg
  rw [← Category.assoc, horn.ι_ι, ← Category.assoc]
  have hcollapse : stdSimplex.δ (0 : Fin 2)
      ≫ stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) = 𝟙 _ := by
    show stdSimplex.map (SimplexCategory.δ 0) ≫ stdSimplex.map _ = 𝟙 _
    rw [← Functor.map_comp,
      Subsingleton.elim (SimplexCategory.δ 0 ≫ SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌),
      CategoryTheory.Functor.map_id]
  rw [hcollapse, Category.id_comp]

/-! ## The target, modulo the special-outer-horn filler (the sole residual gap). -/

/-- `leftFibration_rlp_rightHorn_of_isTerminal`, reduced to the special-outer-horn filler
`hfill` (`SpecialOuterHorn.fill_last`). Everything else — quasicategoricity of `X`,
the reduction, the invertibility side-condition (discharged via conservativity), and the dim-1
base case — is proved from the listed proven inputs. The hypothesis `hfill` is the genuine gap. -/
theorem leftFibration_rlp_rightHorn_of_isTerminal_of_fillLast
    {X Y : SSet.{u}} (p : X ⟶ Y) (hY : IsTerminal Y) [LeftFibration p]
    (hfill : ∀ {k : ℕ} (τ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X),
        IsIsoSimplex (τ.app (op ⦋1⦌) finalEdge) →
        ∃ σ : Δ[k + 2] ⟶ X, τ = Λ[k + 2, Fin.last (k + 2)].ι ≫ σ)
    {n : ℕ} :
    HasLiftingProperty (Λ[n + 1, Fin.last (n + 1)].ι) p := by
  apply rlp_rightHorn_of_isTerminal_of_fill p hY
  intro τ
  obtain _ | k := n
  · exact fill_lastHorn_dim1 τ
  · exact hfill τ (isIsoSimplex_of_leftFibration_isTerminal p hY _)

end SSet
