import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCore
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# Op-duality plumbing for `fill_zero` (infinity-cosmos #117, Route B)

Route B reduces `fill_zero` for `A` to `fill_last` for `A.op`: the `i = 0` outer horn
`Λ[n+2,0] → A` corresponds under vertex-reversal to the `i = last` outer horn
`Λ[n+2,last] → A.op` (`(0 : Fin (n+3)).rev = Fin.last (n+2)`), avoiding the join entirely.

Pieces built here (all `lake env lean` clean, axioms `[propext, Classical.choice, Quot.sound]`):

* `hornOpIso` / `hornOpIso_hom_ι` — the horn-op arrow-iso: `opFunctor` carries the inner/outer
  horn inclusion `Λ[n+2,i].ι` to `Λ[n+2, i.rev].ι` (up to `stdSimplex.opIso`).
* `quasicategory_op` — `Quasicategory A.op` from `[Quasicategory A]` (mathlib `Op.lean` TODO).
* `isIsoSimplex_op` — op-invariance of iso 1-simplices.
* `opSimplexMap` — Δ-self-duality transport of a filler `Δ[n+2] → A.op` back to `Δ[n+2] → A`.
* `fill_zero_of_fill_last` — the reduction skeleton (takes the absolute `fill_last` as a hyp).
-/

open CategoryTheory Simplicial Opposite

namespace SSet

/-! ## Horn-op arrow-iso (#3) -/

section HornOpIso
variable {n : ℕ}

/-- The image of the subcomplex `Λ[n+2,i].op ⊆ Δ[n+2].op` under `stdSimplex.opIso` is
`Λ[n+2, i.rev]`. -/
lemma image_op_horn (i : Fin (n + 3)) :
    (Λ[n + 2, i].op).image (stdSimplex.opIso ⦋n + 2⦌).hom = Λ[n + 2, i.rev] := by
  rw [← Subcomplex.preimage_inv]
  simpa only [IsIso.Iso.inv_hom] using op_horn i

/-- `toImage` along the iso `stdSimplex.opIso.hom` is an isomorphism. -/
lemma isIso_toImage_op_horn (i : Fin (n + 3)) :
    IsIso ((Λ[n + 2, i].op).toImage (stdSimplex.opIso ⦋n + 2⦌).hom) := by
  haveI hmono : Mono ((Λ[n + 2, i].op).toImage (stdSimplex.opIso ⦋n + 2⦌).hom ≫
      ((Λ[n + 2, i].op).image (stdSimplex.opIso ⦋n + 2⦌).hom).ι) := by
    rw [Subcomplex.toImage_ι]; infer_instance
  haveI : Mono ((Λ[n + 2, i].op).toImage (stdSimplex.opIso ⦋n + 2⦌).hom) :=
    mono_of_mono _ ((Λ[n + 2, i].op).image (stdSimplex.opIso ⦋n + 2⦌).hom).ι
  exact isIso_of_mono_of_epi _

/-- The op-functor carries the horn `Λ[n+2,i]` to `Λ[n+2, i.rev]`. -/
noncomputable def hornOpIso (i : Fin (n + 3)) :
    opFunctor.obj (Λ[n + 2, i] : SSet) ≅ (Λ[n + 2, i.rev] : SSet) :=
  @asIso _ _ _ _ ((Λ[n + 2, i].op).toImage (stdSimplex.opIso ⦋n + 2⦌).hom)
      (isIso_toImage_op_horn i) ≪≫
    Subcomplex.eqToIso (image_op_horn i)

/-- The arrow-iso square: `opFunctor` sends the horn inclusion `Λ[n+2,i].ι` to the
`i.rev` horn inclusion, up to `stdSimplex.opIso`. -/
@[reassoc]
lemma hornOpIso_hom_ι (i : Fin (n + 3)) :
    (hornOpIso i).hom ≫ Λ[n + 2, i.rev].ι =
      opFunctor.map (Λ[n + 2, i].ι) ≫ (stdSimplex.opIso ⦋n + 2⦌).hom := by
  show (hornOpIso i).hom ≫ Λ[n + 2, i.rev].ι =
      (Λ[n + 2, i].op).ι ≫ (stdSimplex.opIso ⦋n + 2⦌).hom
  simp only [hornOpIso, Iso.trans_hom, asIso_hom, Subcomplex.eqToIso_hom, Category.assoc,
    Subcomplex.homOfLE_ι]
  exact Subcomplex.toImage_ι _ _

end HornOpIso

/-! ## `Quasicategory A.op` (#1) -/

/-- The opposite of a quasicategory is a quasicategory. -/
instance quasicategory_op (A : SSet) [Quasicategory A] : Quasicategory A.op where
  hornFilling' n i σ₀ h0 hn := by
    have h0' : 0 < i.rev := by
      rw [show (0 : Fin (n + 3)) = (Fin.last (n + 2)).rev from (Fin.rev_last (n + 2)).symm]
      exact Fin.rev_lt_rev.mpr hn
    have hn' : i.rev < Fin.last (n + 2) := by
      rw [show Fin.last (n + 2) = (0 : Fin (n + 3)).rev from (Fin.rev_zero (n + 2)).symm]
      exact Fin.rev_lt_rev.mpr h0
    let ff : Functor.FullyFaithful opFunctor := opEquivalence.fullyFaithfulFunctor
    let eA : A.op.op ≅ A := (opFunctorCompOpFunctorIso).app A
    obtain ⟨τ, hτ⟩ := Quasicategory.hornFilling' (S := A)
      ((hornOpIso i).inv ≫ opFunctor.map σ₀ ≫ eA.hom) h0' hn'
    refine ⟨ff.preimage ((stdSimplex.opIso ⦋n + 2⦌).hom ≫ τ ≫ eA.inv), ?_⟩
    apply ff.map_injective
    rw [Functor.map_comp, ff.map_preimage, ← hornOpIso_hom_ι_assoc,
      ← Category.assoc (Λ[n + 2, i.rev].ι) τ eA.inv, ← hτ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## Op-invariance of iso 1-simplices (#2) -/

section IsoCore
variable {A : SSet} {x₀ x₁ x₂ : A _⦋0⦌}

/-- An edge of `A`, regarded as an edge of `A.op` with source and target swapped. -/
def Edge.op (e : Edge (X := A) x₀ x₁) : Edge (X := A.op) x₁ x₀ :=
  Edge.mk (X := A.op) e.edge
    (by simp only [op_δ]; exact e.tgt_eq)
    (by simp only [op_δ]; exact e.src_eq)

@[simp] lemma Edge.op_edge (e : Edge (X := A) x₀ x₁) : (e.op).edge = e.edge := rfl

/-- A composition structure in `A`, regarded as one in `A.op` (reversing the order). -/
def Edge.CompStruct.op {e₀₁ : Edge (X := A) x₀ x₁} {e₁₂ : Edge (X := A) x₁ x₂}
    {e₀₂ : Edge (X := A) x₀ x₂} (c : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    Edge.CompStruct (X := A.op) e₁₂.op e₀₁.op e₀₂.op :=
  Edge.CompStruct.mk (X := A.op) c.simplex
    (by simp only [op_δ]; exact c.d₀)
    (by simp only [op_δ]; exact c.d₂)
    (by simp only [op_δ]; exact c.d₁)

/-- `Edge.id` is preserved (as a 1-simplex) by passing to `A.op`. -/
lemma Edge.id_op_edge (x : A _⦋0⦌) :
    (Edge.id (X := A) x).op.edge = (Edge.id (X := A.op) x).edge := by
  simp only [Edge.op_edge, Edge.id_edge, op_σ]; rfl

/-- An isomorphism edge in `A`, regarded as an isomorphism edge in `A.op`. -/
def Edge.IsIso.op {hom : Edge (X := A) x₀ x₁} (I : hom.IsIso) : (hom.op).IsIso where
  inv := I.inv.op
  homInvId := (I.invHomId.op).ofEq rfl rfl (Edge.id_op_edge x₁)
  invHomId := (I.homInvId.op).ofEq rfl rfl (Edge.id_op_edge x₀)

/-- Op-invariance of iso 1-simplices: an iso 1-simplex of `A` is an iso 1-simplex of `A.op`. -/
theorem isIsoSimplex_op {s : A _⦋1⦌} (hs : IsIsoSimplex s) :
    IsIsoSimplex (A := A.op) s :=
  isIsoSimplex_of_isIso (A := A.op) hs.some.op rfl

end IsoCore

/-! ## Δ-op transport and the `fill_zero` reduction (#4 + assembly) -/

/-- Transport a filler `Δ[n+2] ⟶ A.op` back to a filler `Δ[n+2] ⟶ A`, using the
self-duality `stdSimplex.opIso : Δ[n+2].op ≅ Δ[n+2]` and full-faithfulness of `opFunctor`. -/
noncomputable def opSimplexMap {A : SSet} {n : ℕ} (τ : Δ[n + 2] ⟶ A.op) : Δ[n + 2] ⟶ A :=
  (opEquivalence.fullyFaithfulFunctor).preimage ((stdSimplex.opIso ⦋n + 2⦌).hom ≫ τ)

@[simp]
lemma opFunctor_map_opSimplexMap {A : SSet} {n : ℕ} (τ : Δ[n + 2] ⟶ A.op) :
    opFunctor.map (opSimplexMap τ) = (stdSimplex.opIso ⦋n + 2⦌).hom ≫ τ :=
  (opEquivalence.fullyFaithfulFunctor).map_preimage _

/-- Op-reduction skeleton (Route B): `fill_zero` for `A` follows from `fill_last` for `A.op`.

`P` is the `i = 0` special-edge (iso) side-condition on `A`, `Q` the `i = last` side-condition
on `A.op`; `hPQ` transports `P` to `Q` along the horn op-iso `hornOpIso` — that transport is
discharged by `isIsoSimplex_op`.  Once the absolute `fill_last` lands it instantiates the
`fill_last` hypothesis.  Note `(0 : Fin (n+3)).rev = Fin.last (n+2)` definitionally. -/
theorem fill_zero_of_fill_last {A : SSet}
    (P : ∀ {m : ℕ}, ((Λ[m + 2, 0] : SSet) ⟶ A) → Prop)
    (Q : ∀ {m : ℕ}, ((Λ[m + 2, Fin.last (m + 2)] : SSet) ⟶ A.op) → Prop)
    (fill_last : ∀ {m : ℕ} (τ₀ : (Λ[m + 2, Fin.last (m + 2)] : SSet) ⟶ A.op),
      Q τ₀ → ∃ τ : Δ[m + 2] ⟶ A.op, τ₀ = Λ[m + 2, Fin.last (m + 2)].ι ≫ τ)
    (hPQ : ∀ {m : ℕ} (σ₀ : (Λ[m + 2, 0] : SSet) ⟶ A), P σ₀ →
      Q ((hornOpIso (0 : Fin (m + 3))).inv ≫ opFunctor.map σ₀))
    {n : ℕ} (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ A) (hσ₀ : P σ₀) :
    ∃ σ : Δ[n + 2] ⟶ A, σ₀ = Λ[n + 2, 0].ι ≫ σ := by
  obtain ⟨τ, hτ⟩ := fill_last ((hornOpIso (0 : Fin (n + 3))).inv ≫ opFunctor.map σ₀) (hPQ σ₀ hσ₀)
  refine ⟨opSimplexMap τ, ?_⟩
  haveI : opFunctor.Faithful := (opEquivalence.fullyFaithfulFunctor).faithful
  apply opFunctor.map_injective
  rw [Functor.map_comp, opFunctor_map_opSimplexMap, ← hornOpIso_hom_ι_assoc]
  have hτ' : Λ[n + 2, (0 : Fin (n + 3)).rev].ι ≫ τ =
      (hornOpIso (0 : Fin (n + 3))).inv ≫ opFunctor.map σ₀ := hτ.symm
  rw [hτ', Iso.hom_inv_id_assoc]

end SSet
