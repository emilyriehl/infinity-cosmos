import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.SetTheory.Cardinal.Ordinal

universe u
open CategoryTheory Simplicial Limits Opposite MorphismProperty HomotopicalAlgebra
open SSet.relativeCellComplexOfMono

/-!
# Single-cell presentation of monomorphisms of simplicial sets

Every monomorphism of simplicial sets lies in the weak saturation of the boundary inclusions
`∂Δ[n] ↪ Δ[n]`: any morphism class `W` stable under isomorphism, cobase change and transfinite
composition that contains the boundary inclusions contains every monomorphism
(`monomorphisms_le_of_boundary_singleCell`), with no coproduct-closure hypothesis. The proof
filters each skeletal step by the within-dimension filtration `psi`, exhibiting it as a
transfinite composition of single boundary-cell pushouts (`skeletonStep_mem`,
`mono_mem_of_skeletonStep`). This is the saturation bookkeeping under the Joyal pushout-product.
Reference: Kerodon 0077 (Proposition 1.5.5.14) and the skeletal filtration of Kerodon §1.5.3–1.5.4.
-/

namespace SSet.singleCell


variable {Y : SSet.{u}} {d : ℕ} (y : Y _⦋d⦌) (hy : y ∈ Y.nonDegenerate d)
  (A : Y.Subcomplex)
  (hA : A.preimage (yonedaEquiv.symm y) = (∂Δ[d] : (Δ[d] : SSet.{u}).Subcomplex))

include hA in
lemma range_bd_comp_le : Subcomplex.range ((∂Δ[d]).ι ≫ yonedaEquiv.symm y) ≤ A := by
  rw [← Subcomplex.image_eq_range, Subcomplex.image_le_iff, hA]

lemma range_cmap_le : Subcomplex.range (yonedaEquiv.symm y) ≤ A ⊔ Subcomplex.ofSimplex y := by
  rw [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]; exact le_sup_right

noncomputable def tmap : (∂Δ[d] : SSet.{u}) ⟶ (A : SSet.{u}) :=
  Subcomplex.lift ((∂Δ[d]).ι ≫ yonedaEquiv.symm y) (range_bd_comp_le y A hA)

noncomputable def bmap : Δ[d] ⟶ ((A ⊔ Subcomplex.ofSimplex y : Y.Subcomplex) : SSet.{u}) :=
  Subcomplex.lift (yonedaEquiv.symm y) (range_cmap_le y A)

noncomputable def rmap : (A : SSet.{u}) ⟶ ((A ⊔ Subcomplex.ofSimplex y : Y.Subcomplex) : SSet.{u}) :=
  Subcomplex.homOfLE le_sup_left

include hA in
lemma single_w : tmap y A hA ≫ rmap y A = (∂Δ[d]).ι ≫ bmap y A := by
  rw [← cancel_mono (Subcomplex.ι _)]
  simp only [tmap, bmap, rmap, Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.lift_ι]

lemma bmap_app_val {n : SimplexCategoryᵒᵖ} (s : Δ[d].obj n) :
    ((bmap y A).app n s).val = (yonedaEquiv.symm y).app n s := rfl

lemma bmap_app_objEquiv_symm {n : ℕ} (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋d⦌) :
    ((bmap y A).app (op ⦋n⦌) (stdSimplex.objEquiv.symm f)).val = Y.map f.op y := rfl

include hA hy in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
lemma single_isPushout :
    IsPushout (tmap y A hA) (∂Δ[d]).ι (rmap y A) (bmap y A) where
  w := single_w y A hA
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨n⟩⟩ ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2 (IsPushout.isColimit ?_)
    have hmono : Mono ((rmap y A).app (op ⦋n⦌)) :=
      (NatTrans.mono_iff_mono_app _).1 (by rw [rmap]; infer_instance) _
    refine Types.isPushout_of_isPullback_of_mono' (r := (rmap y A).app (op ⦋n⦌)) ?_ ?_ ?_
    · rw [Types.isPullback_iff]
      refine ⟨congr_app (single_w y A hA) (op ⦋n⦌), ?_, ?_⟩
      · rintro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨-, h2⟩
        exact Subtype.ext (by simpa using h2)
      · rintro ⟨a, ha⟩ s hs
        have hval : a = (yonedaEquiv.symm y).app (op ⦋n⦌) s := congr_arg Subtype.val hs
        have hmem : s ∈ (A.preimage (yonedaEquiv.symm y)).obj (op ⦋n⦌) := by
          show (yonedaEquiv.symm y).app _ s ∈ A.obj _
          rw [← hval]; exact ha
        rw [hA] at hmem
        exact ⟨⟨s, hmem⟩, Subtype.ext hval.symm, rfl⟩
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨z, hz⟩
      rw [Subfunctor.max_obj] at hz
      rcases hz with hzA | hzO
      · exact Or.inl ⟨⟨z, hzA⟩, Subtype.ext rfl⟩
      · rw [Subcomplex.mem_ofSimplex_obj_iff] at hzO
        obtain ⟨f, rfl⟩ := hzO
        exact Or.inr ⟨stdSimplex.objEquiv.symm f, Subtype.ext (bmap_app_objEquiv_symm y A f)⟩
    · rintro s₁ s₂ hs₁ hs₂ h
      obtain ⟨f₁, rfl⟩ := stdSimplex.objEquiv.symm.surjective s₁
      obtain ⟨f₂, rfl⟩ := stdSimplex.objEquiv.symm.surjective s₂
      have hval : Y.map f₁.op y = Y.map f₂.op y := by
        rw [← bmap_app_objEquiv_symm y A f₁, ← bmap_app_objEquiv_symm y A f₂]
        exact congr_arg Subtype.val h
      have hf₁ : (stdSimplex.objEquiv.symm f₁ : Δ[d].obj (op ⦋n⦌)) ∉ (∂Δ[d]).obj (op ⦋n⦌) :=
        fun hmem ↦ hs₁ ⟨⟨_, hmem⟩, rfl⟩
      haveI e1 : Epi f₁ := by simpa [SimplexCategory.epi_iff_surjective, boundary] using! hf₁
      have : f₁ = f₂ := Y.unique_nonDegenerate_map (Y.map f₁.op y) f₁ ⟨y, hy⟩ rfl f₂ ⟨y, hy⟩ hval
      rw [this])⟩


open MorphismProperty in
include hy hA in
/-- The single-cell filtration step lies in any `W` that contains the boundary
inclusion and is stable under cobase change. NO coproduct, NO `I.pushouts`. -/
lemma rmap_mem (W : MorphismProperty SSet.{u}) [W.IsStableUnderCobaseChange]
    (hbd : W (∂Δ[d]).ι) : W (rmap y A) :=
  W.pushouts_le _ (W.pushouts_mk (single_isPushout y hy A hA) hbd)



lemma nondeg_indep {Y : SSet.{u}} {d : ℕ} {x x' : Y _⦋d⦌}
    (hx : x ∈ Y.nonDegenerate d)
    (h : x ∈ (Subcomplex.ofSimplex x').obj (op ⦋d⦌)) : x = x' := by
  rw [Subcomplex.mem_ofSimplex_obj_iff] at h
  obtain ⟨f, hf⟩ := h
  haveI : Mono f := Y.mono_of_nonDegenerate ⟨x, hx⟩ f x' hf
  obtain rfl := SimplexCategory.eq_id_of_mono f
  simpa using hf.symm

section
variable {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (d : ℕ)
  {J : Type u} [LinearOrder J] (rank : Cell i d ↪ J)

/-- within-dimension filtration. -/
def psi (γ : J) : Y.Subcomplex :=
  skeletonOfMono i d ⊔ ⨆ (c : Cell i d) (_ : rank c < γ), Subcomplex.ofSimplex c.simplex

set_option maxHeartbeats 4000000 in
lemma psi_monotone : Monotone (psi i d rank) := by
  intro γ γ' h
  apply sup_le le_sup_left
  apply iSup₂_le
  intro c hc
  exact le_sup_of_le_right (le_iSup₂_of_le c (hc.trans_le h) le_rfl)

lemma skd_le_psi (γ : J) : skeletonOfMono i d ≤ psi i d rank γ := le_sup_left

lemma ofSimplex_le_psi (γ : J) (c : Cell i d) (hc : rank c < γ) :
    Subcomplex.ofSimplex c.simplex ≤ psi i d rank γ :=
  le_sup_of_le_right (le_iSup₂_of_le c hc le_rfl)

lemma simplex_notMem_psi (γ : J) (c : Cell i d) (hc : ¬ rank c < γ) :
    c.simplex ∉ (psi i d rank γ).obj (op ⦋d⦌) := by
  rw [psi, Subfunctor.max_obj, Set.mem_union, not_or]
  refine ⟨?_, ?_⟩
  · rw [c.mem_skeletonOfMono_obj_iff]
    push_neg
    exact ⟨c.notMem, by simp⟩
  · simp only [Subfunctor.iSup_obj, Set.mem_iUnion, not_exists]
    intro c' hlt hmem
    have : c.simplex = c'.simplex := nondeg_indep c.nonDegenerate hmem
    obtain rfl : c = c' := by ext1; exact this
    exact hc hlt

lemma psi_preimage (γ : J) (c : Cell i d) (hc : ¬ rank c < γ) :
    (psi i d rank γ).preimage c.map = ∂Δ[d] := by
  rw [stdSimplex.eq_boundary_iff]
  refine ⟨?_, ?_⟩
  · have h1 : (∂Δ[d] : (Δ[d] : SSet.{u}).Subcomplex).image c.map ≤ skeletonOfMono i d := by
      rw [Subcomplex.image_le_iff, c.preimage_map]
    rw [← Subcomplex.image_le_iff]
    exact h1.trans (skd_le_psi i d rank γ)
  · rw [Ne, Subcomplex.preimage_eq_top_iff, Cell.map, Subcomplex.range_eq_ofSimplex,
        Equiv.apply_symm_apply, Subcomplex.ofSimplex_le_iff]
    exact simplex_notMem_psi i d rank γ c hc

lemma psi_bot [OrderBot J] : psi i d rank ⊥ = skeletonOfMono i d := by simp [psi]

set_option maxHeartbeats 1000000 in
lemma psi_succ [SuccOrder J] (γ : J) (hγ : ¬ IsMax γ) :
    psi i d rank (Order.succ γ) =
      psi i d rank γ ⊔ ⨆ (c : Cell i d) (_ : rank c = γ), Subcomplex.ofSimplex c.simplex := by
  apply le_antisymm
  · rw [psi]
    apply sup_le (le_sup_of_le_left (skd_le_psi i d rank γ))
    apply iSup₂_le
    intro c hc
    rw [Order.lt_succ_iff_of_not_isMax hγ] at hc
    obtain hc | rfl := hc.lt_or_eq
    · exact le_sup_of_le_left (ofSimplex_le_psi i d rank γ c hc)
    · exact le_sup_of_le_right (le_iSup₂_of_le c rfl le_rfl)
  · apply sup_le (psi_monotone i d rank (Order.le_succ γ))
    apply iSup₂_le
    intro c hc
    refine ofSimplex_le_psi i d rank (Order.succ γ) c ?_
    rw [hc]; exact Order.lt_succ_of_not_isMax hγ

set_option maxHeartbeats 1000000 in
lemma iSup_psi [OrderBot J] [NoMaxOrder J] :
    ⨆ γ, psi i d rank γ = skeletonOfMono i (d + 1) := by
  rw [skeletonOfMono_succ]
  apply le_antisymm
  · apply iSup_le
    intro γ
    apply sup_le le_sup_left
    apply iSup₂_le
    intro c _
    refine le_sup_of_le_right (le_iSup₂_of_le ⟨c.simplex, c.nonDegenerate⟩ ?_ le_rfl)
    simpa using c.notMem
  · apply sup_le
    · exact le_trans (skd_le_psi i d rank ⊥) (le_iSup _ ⊥)
    · apply iSup₂_le
      intro x hx
      set c : Cell i d := ⟨x.1, x.2, by simpa using hx⟩ with hc
      obtain ⟨γ, hγ⟩ := exists_gt (rank c)
      exact le_iSup_of_le γ (ofSimplex_le_psi i d rank γ c hγ)

set_option maxHeartbeats 1000000 in
lemma psi_iSup_iio [OrderBot J] [SuccOrder J] (m : J) (hm : Order.IsSuccLimit m) :
    ⨆ (γ : Set.Iio m), psi i d rank γ = psi i d rank m := by
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro γ hγ
    exact psi_monotone i d rank hγ.le
  · rw [psi]
    apply sup_le
    · exact le_iSup_of_le (⟨⊥, hm.bot_lt⟩ : Set.Iio m) (skd_le_psi i d rank ⊥)
    · apply iSup₂_le
      intro c hc
      exact le_iSup_of_le (⟨Order.succ (rank c), hm.succ_lt hc⟩ : Set.Iio m)
        (ofSimplex_le_psi i d rank (Order.succ (rank c)) c
          (Order.lt_succ_of_not_isMax (not_isMax_of_lt hc)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance psi_continuous [OrderBot J] [SuccOrder J] [WellFoundedLT J] :
    (psi_monotone i d rank).functor.IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← psi_iSup_iio i d rank m hm]
    apply isLUB_iSup)⟩

end

/-- `rmap_mem` with the target expressed as any subcomplex equal to `A ⊔ ofSimplex y`. -/
lemma rmap_mem' {Y : SSet.{u}} {d : ℕ} (y : Y _⦋d⦌) (hy : y ∈ Y.nonDegenerate d)
    (A : Y.Subcomplex) (hA : A.preimage (yonedaEquiv.symm y) = ∂Δ[d])
    (B : Y.Subcomplex) (hB : B = A ⊔ Subcomplex.ofSimplex y) (hle : A ≤ B)
    (W : MorphismProperty SSet.{u}) [W.IsStableUnderCobaseChange]
    (hbd : W (∂Δ[d]).ι) : W (Subcomplex.homOfLE hle) := by
  subst hB
  exact rmap_mem y hy A hA W hbd

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- any `W` from the saturation premises contains all isomorphisms. -/
lemma iso_mem (W : MorphismProperty SSet.{u}) [W.RespectsIso]
    [IsStableUnderTransfiniteComposition.{u} W] {P Q : SSet.{u}} (f : P ⟶ Q) [IsIso f] : W f :=
  (W.arrow_mk_iso_iff (Arrow.isoMk (Iso.refl P) (asIso f) (by simp))).mp (W.id_mem P)

section
variable {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (d : ℕ)
  {J : Type u} [LinearOrder J] (rank : Cell i d ↪ J)
  (W : MorphismProperty SSet.{u}) [W.RespectsIso] [W.IsStableUnderCobaseChange]
  [IsStableUnderTransfiniteComposition.{u} W]
  (hbd : ∀ n : ℕ, W (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι)

set_option maxHeartbeats 1000000 in
include hbd in
lemma psi_step_mem [SuccOrder J] (γ : J) (hγ : ¬ IsMax γ) :
    W (Subcomplex.homOfLE (psi_monotone i d rank (Order.le_succ γ))) := by
  by_cases h : ∃ c : Cell i d, rank c = γ
  · obtain ⟨c, hc⟩ := h
    have heq : psi i d rank (Order.succ γ) =
        psi i d rank γ ⊔ Subcomplex.ofSimplex c.simplex := by
      rw [psi_succ i d rank γ hγ]
      congr 1
      apply le_antisymm
      · exact iSup₂_le fun c' hc' => by rw [rank.injective (hc'.trans hc.symm)]
      · exact le_iSup₂_of_le c hc le_rfl
    exact rmap_mem' c.simplex c.nonDegenerate (psi i d rank γ)
      (psi_preimage i d rank γ c (not_lt.mpr hc.ge))
      (psi i d rank (Order.succ γ)) heq (psi_monotone i d rank (Order.le_succ γ)) W (hbd d)
  · have heq : psi i d rank (Order.succ γ) = psi i d rank γ := by
      rw [psi_succ i d rank γ hγ, sup_eq_left]
      exact iSup₂_le fun c hc => absurd ⟨c, hc⟩ h
    haveI : IsIso (Subcomplex.homOfLE (psi_monotone i d rank (Order.le_succ γ))) := by
      refine ⟨Subcomplex.homOfLE heq.le, ?_, ?_⟩ <;>
        · rw [← cancel_mono (Subcomplex.ι _)]; simp [Subcomplex.homOfLE_ι]
    exact iso_mem W _

variable [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- the within-dimension transfinite composition of single boundary cells. -/
noncomputable def baseTC :
    CategoryTheory.TransfiniteCompositionOfShape J (relativeCellComplexOfMono.r i d) where
  F := (psi_monotone i d rank).functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (psi_bot i d rank)
  isWellOrderContinuous := ⟨fun m hm => ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
    (Functor.isColimitOfIsWellOrderContinuous (psi_monotone i d rank).functor m hm)⟩⟩
  incl :=
    { app := fun γ => Subcomplex.homOfLE
        (le_trans (le_iSup (psi i d rank) γ) (iSup_psi i d rank).le)
      naturality := fun γ γ' f => by
        dsimp; rw [← cancel_mono (Subcomplex.ι _)]; simp }
  isColimit := IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      ((CompleteLattice.colimitCocone ((psi_monotone i d rank).functor)).isColimit))
    (Cocone.ext (Subcomplex.eqToIso (iSup_psi i d rank)) (fun γ => by
      dsimp; rw [← cancel_mono (Subcomplex.ι _)]; simp))
  fac := by rw [← cancel_mono (Subcomplex.ι _)]; simp

include hbd in
/-- the within-dimension transfinite composition, as a `W`-transfinite composition. -/
noncomputable def WTC :
    W.TransfiniteCompositionOfShape J (relativeCellComplexOfMono.r i d) where
  toTransfiniteCompositionOfShape := baseTC i d rank
  map_mem γ hγ := psi_step_mem i d rank W hbd γ hγ

include rank hbd in
lemma skeletonStep_mem_aux : W (relativeCellComplexOfMono.r i d) :=
  W.transfiniteCompositionsOfShape_le J _ (WTC i d rank W hbd).mem

end

/-- Each skeleton step `relativeCellComplexOfMono.r i d` lies in `W`. -/
theorem skeletonStep_mem {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (W : MorphismProperty SSet.{u}) [W.RespectsIso] [W.IsStableUnderCobaseChange]
    [IsStableUnderTransfiniteComposition.{u} W]
    (hbd : ∀ n : ℕ, W (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι) (d : ℕ) :
    W (relativeCellComplexOfMono.r i d) := by
  set C := relativeCellComplexOfMono.Cell i d with hC
  let κ := max (Cardinal.mk C) Cardinal.aleph0
  haveI : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder (le_max_right _ _)
  haveI : Nonempty κ.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff, Ne, Cardinal.ord_eq_zero]
    exact (Cardinal.aleph0_pos.trans_le (le_max_right _ _)).ne'
  haveI : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have hcard : Cardinal.mk C ≤ Cardinal.mk κ.ord.ToType := by
    rw [Cardinal.mk_ord_toType]; exact le_max_left _ _
  obtain ⟨rank⟩ := (Cardinal.le_def _ _).mp hcard
  exact skeletonStep_mem_aux i d rank W hbd

/-- If every skeleton step of a monomorphism `i` lies in `W`, then so does `i`. -/
theorem mono_mem_of_skeletonStep {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (W : MorphismProperty SSet.{u}) [IsStableUnderTransfiniteComposition.{u} W]
    (stepMem : ∀ d, W (relativeCellComplexOfMono.r i d)) : W i := by
  haveI : IsStableUnderTransfiniteComposition.{0} W :=
    IsStableUnderTransfiniteComposition.shrink₀ W
  have tc : W.TransfiniteCompositionOfShape ℕ i :=
    { (relativeCellComplexOfMono i).toTransfiniteCompositionOfShape with
      map_mem := fun j _ => stepMem j }
  exact W.transfiniteCompositionsOfShape_le ℕ _ tc.mem

/-- THE THEOREM: every monomorphism of simplicial sets is a transfinite composition of
single boundary-cell pushouts. Concretely: any `W` containing the boundary inclusions
`∂Δ[n] ⟶ Δ[n]` and closed under iso, cobase change and transfinite composition
contains every monomorphism. NO `Coproducts` closure required. -/
theorem monomorphisms_le_of_boundary_singleCell (W : MorphismProperty SSet.{u})
    [W.RespectsIso] [W.IsStableUnderCobaseChange] [IsStableUnderTransfiniteComposition.{u} W]
    (hbd : ∀ n : ℕ, W (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι) :
    MorphismProperty.monomorphisms SSet.{u} ≤ W := by
  intro X Y i (hi : Mono i)
  exact mono_mem_of_skeletonStep i W (fun d => skeletonStep_mem i W hbd d)

end SSet.singleCell
