import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.SpecialOuterHornOpDuality
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.SpecialOuterHornFillLast
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibrationTerminalReduction
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCoreKan
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration

open CategoryTheory HomotopicalAlgebra Simplicial Opposite Limits MorphismProperty
open scoped SSet.modelCategoryQuillen

/-!
# Special-outer-horn close: the relocated tracked theorems

Assembles the special-outer-horn cascade (Joyal's special outer horn filler) into the
foundational quasicategory results it underwrites:

* `SpecialOuterHorn.fill_zero` — the `i = 0` outer-horn filler, obtained from `fill_last` for
  `A.op` by op-duality (Route B, `SpecialOuterHornOpDuality`);
* `coherentIso.lift` — every invertible edge of a quasicategory extends to a map out of
  `coherentIso` (relocated from `CoherentIso.lean`). This is the forward direction of the
  homotopy-coherent-isomorphism characterization (blueprint `prop:coherent-iso`), the result
  whose proof requires special-outer-horn filling;
* `leftFibration_rlp_rightHorn_of_isTerminal` and its consumers
  `kanComplex_of_leftFibration_isTerminal` / `kanComplex_fiber_of_leftFibration` (relocated from
  `LeftFibration.lean`).

These are foundational infrastructure. The Brown factorization lemma (Lemma 1.5.12, blueprint
`lem:brown-fact`, issue #117) is a separate ∞-cosmos-level construction in `Isofibrations.lean`;
`coherentIso.lift` underwrites the 2-of-3 equivalence calculus used by its corollary, but is not
on the dependency path of the core factorization itself.
-/

namespace SSet
universe u

namespace Close117

/-! ## hPQ glue: the op'd horn's `finalEdge` is `σ`'s `initialEdge` (Route B side-condition) -/

/-- `stdSimplex.opIso` carries the `Λ[·,last]` `finalEdge` to the `Λ[·,0]` `initialEdge`. -/
lemma homEdge {m : ℕ} :
    ((SpecialOuterHorn.finalEdge.{u} (n := m)).val : Δ[m+2] _⦋1⦌)
      = (stdSimplex.opIso.{u} ⦋m + 2⦌).hom.app (op ⦋1⦌)
          ((SpecialOuterHorn.initialEdge.{u} (n := m)).val) := by
  rw [stdSimplex.opIso_hom_app_hom_apply]
  refine stdSimplex.ext _ _ (fun i => ?_)
  rw [stdSimplex.opObjEquiv_apply]
  simp only [SpecialOuterHorn.finalEdge, SpecialOuterHorn.initialEdge, horn.edge_coe,
    SSet.opObjEquiv]
  fin_cases i <;> rfl

/-- `(hornOpIso 0).inv` carries `finalEdge` (op'd horn) to `initialEdge`. -/
lemma key {m : ℕ} :
    (hornOpIso.{u} (0 : Fin (m + 3))).inv.app (op ⦋1⦌) (SpecialOuterHorn.finalEdge.{u})
      = SpecialOuterHorn.initialEdge.{u} := by
  have hmor : Λ[m + 2, (0 : Fin (m + 3)).rev].ι ≫ (stdSimplex.opIso.{u} ⦋m + 2⦌).inv
      = (hornOpIso.{u} (0 : Fin (m + 3))).inv ≫ opFunctor.map (Λ[m + 2, 0].ι) := by
    rw [← cancel_epi (hornOpIso.{u} (0 : Fin (m + 3))).hom, ← Category.assoc, hornOpIso_hom_ι,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have happ := congrArg (fun φ => φ.app (op ⦋1⦌) (SpecialOuterHorn.finalEdge.{u})) hmor
  simp only [NatTrans.comp_app_apply] at happ
  apply Subtype.ext
  refine happ.symm.trans ?_
  show (stdSimplex.opIso.{u} ⦋m+2⦌).inv.app (op ⦋1⦌) ((SpecialOuterHorn.finalEdge.{u} (n:=m)).val)
      = ((SpecialOuterHorn.initialEdge.{u} (n:=m)).val)
  rw [homEdge]
  simp

end Close117

/-! ## `SSet.SpecialOuterHorn.fill_zero` (the `i = 0` outer-horn filler, via op-duality) -/

namespace SpecialOuterHorn

/-- `fill_zero` for `A` from `fill_last` for `A.op` (Route B / op-duality): apply
`fill_zero_of_fill_last` with `fill_last` at `A.op` (a `Quasicategory` via `quasicategory_op`),
discharging the edge-iso side condition by `Close117.key` + `isIsoSimplex_op`. -/
theorem fill_zero {A : SSet.{u}} [Quasicategory A] {n : ℕ}
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet) ⟶ A)
    (h_init : IsIsoSimplex (σ₀.app (op ⦋1⦌) initialEdge)) :
    ∃ σ : Δ[n + 2] ⟶ A, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ :=
  fill_zero_of_fill_last
    (A := A)
    (P := fun {m} σ => IsIsoSimplex (σ.app (op ⦋1⦌) SpecialOuterHorn.initialEdge))
    (Q := fun {m} τ => IsIsoSimplex (A := A.op) (τ.app (op ⦋1⦌) SpecialOuterHorn.finalEdge))
    (fill_last := fun {m} τ₀ hQ => SpecialOuterHorn.fill_last (A := A.op) τ₀ hQ)
    (hPQ := fun {m} σ hP => by
      have he : ((hornOpIso (0 : Fin (m + 3))).inv ≫ opFunctor.map σ).app (op ⦋1⦌)
            SpecialOuterHorn.finalEdge
          = σ.app (op ⦋1⦌) SpecialOuterHorn.initialEdge := by
        rw [NatTrans.comp_app_apply, Close117.key, opFunctor_map]; rfl
      exact he.symm ▸ isIsoSimplex_op hP)
    σ₀ h_init

end SpecialOuterHorn

/-! ## `SSet.coherentIso.lift` (relocated from `CoherentIso.lean`) -/

namespace coherentIso

/-- Every invertible edge of a quasicategory extends to a map out of `coherentIso`.
Discharges `coherentIso.lift_of_isoCore_outerHornFiller` with the special-outer-horn
producer `isoCore_outerHornFiller_of_producer fill_zero fill_last`. -/
theorem lift {A : SSet.{u}} [Quasicategory A] {a₀ a₁ : A _⦋0⦌} {e : Edge a₀ a₁}
    (he : e.IsIso) :
    ∃ F : coherentIso.{u} ⟶ A, (coherentIso.hom.map F).edge = e.edge :=
  coherentIso.lift_of_isoCore_outerHornFiller he
    (isoCore_outerHornFiller_of_producer
      (fun {_} σ₀ h => SpecialOuterHorn.fill_zero σ₀ h)
      (fun {_} σ₀ h => SpecialOuterHorn.fill_last σ₀ h))

end coherentIso

/-! ## `SSet.leftFibration_rlp_rightHorn_of_isTerminal` (relocated from `LeftFibration.lean`) -/

/-- A left fibration over a terminal object lifts against the single right-most (last) outer horn.
Discharged from `leftFibration_rlp_rightHorn_of_isTerminal_of_fillLast` and the proven
`SpecialOuterHorn.fill_last`. -/
theorem leftFibration_rlp_rightHorn_of_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] {n : ℕ} :
    HasLiftingProperty (Λ[n + 1, Fin.last (n + 1)].ι) p := by
  haveI : Quasicategory X := quasicategory_of_leftFibration_isTerminal p hY
  exact leftFibration_rlp_rightHorn_of_isTerminal_of_fillLast p hY
    (fun {k} τ h => SpecialOuterHorn.fill_last τ h)

/-- A left fibration whose target is terminal has a Kan-complex source. -/
theorem kanComplex_of_leftFibration_isTerminal {X Y : SSet.{u}} (p : X ⟶ Y)
    (hY : IsTerminal Y) [LeftFibration p] : KanComplex X := by
  show IsFibrant X
  rw [isFibrant_iff_of_isTerminal p hY, modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [modelCategoryQuillen.J, iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  rcases lt_or_eq_of_le (Fin.le_last i) with hlt | heq
  · exact mem_leftFibrations p _ ⟨i, hlt⟩
  · subst heq
    exact leftFibration_rlp_rightHorn_of_isTerminal p hY

/-- The fiber of a left fibration over a vertex is a Kan complex. -/
theorem kanComplex_fiber_of_leftFibration {X S : SSet.{u}} (p : X ⟶ S)
    [LeftFibration p] (s : Δ[0] ⟶ S) :
    KanComplex (Limits.pullback p s) := by
  have hsnd : leftFibrations (Limits.pullback.snd p s) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p s)
      (mem_leftFibrations p)
  have : LeftFibration (Limits.pullback.snd p s) := ⟨hsnd⟩
  exact kanComplex_of_leftFibration_isTerminal (Limits.pullback.snd p s)
    stdSimplex.isTerminalObj₀

end SSet
