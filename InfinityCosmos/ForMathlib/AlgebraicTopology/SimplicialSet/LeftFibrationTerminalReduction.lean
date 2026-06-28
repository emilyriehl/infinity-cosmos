import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.FibrationConservative
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
/-!
# LeftFibration.lean:114 — scope + partial assembly for #117

`leftFibration_rlp_rightHorn_of_isTerminal`: a left fibration over a terminal object lifts the
right-most (last) outer horn `Λ[n+1, last].ι` (Kerodon 019D).

This file isolates the EXACT residual obstruction. Everything except the special-outer-horn
filling (Kerodon 019F, the `fill_last` producer) is discharged here from the proven inputs:
  * `quasicategory_iff_of_isTerminal` (in-tree),
  * `leftFibration_conservative` (in-tree, FibrationConservative.lean),
  * terminal-base subsingleton.
The sole hypothesis `hfill` is the 019F last-outer-horn filler, which is NOT among the proven
inputs (it is still `sorry` in `sj_joyal_assemble`/`wrap_1` and is the same gap blocking
`CoherentIso.lean:201`). Its invertible-final-edge SIDE-CONDITION is shown to be free.
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

/-- Every 1-simplex of `X` is an iso simplex; the 019F invertibility side-condition is free. -/
theorem isIsoSimplex_of_leftFibration_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] (s : X _⦋1⦌) : IsIsoSimplex s := by
  obtain ⟨he⟩ := edge_isIso_of_leftFibration_isTerminal p hY (Edge.mk s rfl rfl)
  exact isIsoSimplex_of_edge he

/-! ## The 019F gap and the dim-1 base case. -/

/-- Final edge `[n+1, n+2]` of `Λ[n+2, last]` (verbatim from `sj_joyal_assemble`). -/
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

/-! ## The target, modulo the 019F filler (the sole residual gap). -/

/-- `leftFibration_rlp_rightHorn_of_isTerminal`, reduced to the 019F special-outer-horn filler
`hfill` (Kerodon 019F = `SpecialOuterHorn.fill_last`). Everything else — quasicategoricity of `X`,
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
