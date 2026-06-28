import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Leibniz-join saturation interface (fixed monomorphism, varying left-anodyne slot)

Sets up the second-slot saturation argument behind the Joyal pushout-product. For a
monomorphism `j`, `leibImgR j` collects the maps `i` whose Leibniz join `leibnizJoin j i` is
inner-anodyne; `cornerIso` identifies that join with mathlib's generic Leibniz pushout, giving
stability under retracts (`leibImgR_isStableUnderRetracts`) and cobase change (`leibImgR_cobase`).
`satI_of_instances` reduces `leftAnodyneExtensions ≤ leibImgR j` to the two remaining stability
facts (coproducts, transfinite composition) plus the generators from `satJ`, using the
small-object presentation of the left-anodyne maps. Inner-anodyne maps form the weak saturation
of the inner horns; the pushout-product itself is the Joyal pushout-product.
-/

open CategoryTheory Simplicial Limits MorphismProperty SmallObject

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace SSet
universe u
noncomputable section

/-- Fix the RIGHT (left-anodyne) argument `i`; vary the LEFT (mono) argument `j`. -/
def leibImgL' {A B : SSet.{u}} (i : A ⟶ B) : MorphismProperty SSet.{u} :=
  fun _ _ j => innerAnodyneExtensions (leibnizJoin j i)

/-- Fix the LEFT (mono) argument `j`; vary the RIGHT (left-anodyne) argument `i`. -/
def leibImgR {S T : SSet.{u}} (j : S ⟶ T) : MorphismProperty SSet.{u} :=
  fun _ _ i => innerAnodyneExtensions (leibnizJoin j i)

/-! ## Small-object argument for `leftHornInclusions`. -/

lemma leftHornInclusions_eq_iSup :
    leftHornInclusions.{u} =
      ⨆ n, .ofHoms (fun i : {i : Fin (n + 2) // i < Fin.last (n + 1)} ↦ Λ[n + 1, i.1].ι) := by
  ext A B f
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    exact ⟨n, i, hn, rfl⟩
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, hn⟩, _, _⟩ := h
    exact ⟨i, hn⟩

instance : MorphismProperty.IsSmall.{u} leftHornInclusions.{u} := by
  rw [leftHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms.{u}
        (fun i : {i : Fin (n + 2) // i < Fin.last (n + 1)} ↦ Λ[n + 1, i.1].ι)) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument leftHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [leftHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} leftHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-! ## Corner bridge to mathlib's generic Leibniz-pushout Arrow-bifunctor. -/

/-- The join pushout-product square: a `PushoutObjObj j i` whose apex is the join pushout. -/
def joinSq {S T A B : SSet.{u}} (j : S ⟶ T) (i : A ⟶ B) : joinFunctor.PushoutObjObj j i where
  pt := pushout (joinMap j (𝟙 A)) (joinMap (𝟙 S) i)
  inl := pushout.inl _ _
  inr := pushout.inr _ _
  isPushout := by
    rw [← joinMap_id_left, ← Functor.flip_obj_map, ← joinMap_id_right]
    exact IsPushout.of_hasPushout _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma joinSq_ι {S T A B : SSet.{u}} (j : S ⟶ T) (i : A ⟶ B) :
    (joinSq j i).ι = leibnizJoin j i := by
  apply (joinSq j i).hom_ext
  · rw [Functor.PushoutObjObj.inl_ι]
    simp only [joinSq, leibnizJoin, pushout.inl_desc, joinMap_id_left]
  · rw [Functor.PushoutObjObj.inr_ι]
    simp only [joinSq, leibnizJoin, pushout.inr_desc, joinMap_id_right, Functor.flip_obj_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Any two pushout-product presentations of `j ⋆̂ i` have isomorphic corner maps `.ι`. -/
def pushoutObjObj_ι_arrowIso {S T A B : SSet.{u}} (j : S ⟶ T) (i : A ⟶ B)
    (sq sq' : joinFunctor.PushoutObjObj j i) :
    Arrow.mk sq.ι ≅ Arrow.mk sq'.ι := by
  refine Arrow.isoMk (sq.isPushout.isoIsPushout _ _ sq'.isPushout) (Iso.refl _) ?_
  dsimp
  apply sq.isPushout.hom_ext
  · simp [Functor.PushoutObjObj.inl_ι]
  · simp [Functor.PushoutObjObj.inr_ι]

/-- The Leibniz pushout-product functor `Arrow ⥤ Arrow` for the join with `j` fixed. -/
def Lj {S T : SSet.{u}} (j : S ⟶ T) : Arrow SSet.{u} ⥤ Arrow SSet.{u} :=
  (joinFunctor.{u}).leibnizPushout.obj (Arrow.mk j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Identifies the join Leibniz product `leibnizJoin j i` with mathlib's generic
Leibniz pushout corner map. -/
def cornerIso {S T A B : SSet.{u}} (j : S ⟶ T) (i : A ⟶ B) :
    Arrow.mk (leibnizJoin j i) ≅
      Arrow.mk ((Functor.PushoutObjObj.ofHasPushout joinFunctor j i).ι) :=
  (eqToIso (by rw [← joinSq_ι j i])) ≪≫
    pushoutObjObj_ι_arrowIso j i (joinSq j i) (Functor.PushoutObjObj.ofHasPushout joinFunctor j i)

/-! ## Instance: IsStableUnderRetracts. -/

instance leibImgR_isStableUnderRetracts {S T : SSet.{u}} (j : S ⟶ T) :
    (leibImgR j).IsStableUnderRetracts where
  of_retract {A' B' A B i' i} h hi := by
    have hiC : innerAnodyneExtensions
        ((Functor.PushoutObjObj.ofHasPushout joinFunctor j i).ι) :=
      (innerAnodyneExtensions.arrow_mk_iso_iff (cornerIso j i)).1 hi
    have hR := (show Retract (Arrow.mk i') (Arrow.mk i) from h).map (Lj j)
    have hRes := innerAnodyneExtensions.of_retract hR hiC
    exact (innerAnodyneExtensions.arrow_mk_iso_iff (cornerIso j i')).2 hRes

/-! ## Instance: IsStableUnderCobaseChange (port of first-slot `leibImgL_cobase`). -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem leibImgR_cobase {S T : SSet.{u}} (j : S ⟶ T) :
    (leibImgR j).IsStableUnderCobaseChange := by
  haveI presSpanS : PreservesColimitsOfShape WalkingSpan (joinFunctor.obj S) :=
    joinFunctor_obj_preservesConnectedColimits_of_tensorLeft WalkingSpan S
  haveI presSpanT : PreservesColimitsOfShape WalkingSpan (joinFunctor.obj T) :=
    joinFunctor_obj_preservesConnectedColimits_of_tensorLeft WalkingSpan T
  constructor
  intro A A' B B' f g f' g' sq hf
  have sqS : IsPushout (joinMap (𝟙 S) g) (joinMap (𝟙 S) f) (joinMap (𝟙 S) f')
      (joinMap (𝟙 S) g') := by
    have := sq.map (joinFunctor.obj S); simp only [← joinMap_id_left] at this; exact this
  have sqT : IsPushout (joinMap (𝟙 T) g) (joinMap (𝟙 T) f) (joinMap (𝟙 T) f')
      (joinMap (𝟙 T) g') := by
    have := sq.map (joinFunctor.obj T); simp only [← joinMap_id_left] at this; exact this
  have eq₁ : joinMap (𝟙 S) f ≫ joinMap (𝟙 S) g' = joinMap (𝟙 S) g ≫ joinMap (𝟙 S) f' := by
    rw [← joinMap_comp_right, ← joinMap_comp_right, sq.w]
  have eq₂ : joinMap j (𝟙 A) ≫ joinMap (𝟙 T) g = joinMap (𝟙 S) g ≫ joinMap j (𝟙 B) :=
    joinMap_comm j g
  set μ : pushout (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) ⟶
      pushout (joinMap j (𝟙 B)) (joinMap (𝟙 S) f') :=
    pushout.map (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) (joinMap j (𝟙 B)) (joinMap (𝟙 S) f')
      (joinMap (𝟙 T) g) (joinMap (𝟙 S) g') (joinMap (𝟙 S) g) eq₂ eq₁ with hμ
  set inlf := pushout.inl (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) with hinlf
  set inrf := pushout.inr (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) with hinrf
  set inlf' := pushout.inl (joinMap j (𝟙 B)) (joinMap (𝟙 S) f') with hinlf'
  set inrf' := pushout.inr (joinMap j (𝟙 B)) (joinMap (𝟙 S) f') with hinrf'
  have μ_inl : inlf ≫ μ = joinMap (𝟙 T) g ≫ inlf' := by simp [hμ, hinlf, hinlf', pushout.map]
  have μ_inr : inrf ≫ μ = joinMap (𝟙 S) g' ≫ inrf' := by simp [hμ, hinrf, hinrf', pushout.map]
  have ldil : inlf ≫ leibnizJoin j f = joinMap (𝟙 T) f := by simp [hinlf, leibnizJoin]
  have ldir : inrf ≫ leibnizJoin j f = joinMap j (𝟙 A') := by simp [hinrf, leibnizJoin]
  have ldil' : inlf' ≫ leibnizJoin j f' = joinMap (𝟙 T) f' := by simp [hinlf', leibnizJoin]
  have ldir' : inrf' ≫ leibnizJoin j f' = joinMap j (𝟙 B') := by simp [hinrf', leibnizJoin]
  have hcond' : joinMap j (𝟙 B) ≫ inlf' = joinMap (𝟙 S) f' ≫ inrf' := by
    simp [hinlf', hinrf', pushout.condition]
  have hcomm : μ ≫ leibnizJoin j f' = leibnizJoin j f ≫ joinMap (𝟙 T) g' := by
    apply pushout.hom_ext
    · rw [← hinlf]; simp only [← Category.assoc, μ_inl]
      rw [Category.assoc, ldil', ldil]; exact sqT.w
    · rw [← hinrf]; simp only [← Category.assoc, μ_inr]
      rw [Category.assoc, ldir', ldir]; exact (joinMap_comm j g').symm
  have colim : IsColimit (PushoutCocone.mk (leibnizJoin j f') (joinMap (𝟙 T) g') hcomm) := by
    refine PushoutCocone.IsColimit.mk hcomm
      (fun s => sqT.desc (inlf' ≫ s.inl) s.inr ?_) ?_ ?_ ?_
    · rw [← Category.assoc, ← μ_inl, Category.assoc, s.condition, ← Category.assoc, ldil]
    · intro s
      apply pushout.hom_ext
      · rw [← hinlf', ← Category.assoc, ldil', sqT.inl_desc]
      · rw [← hinrf', ← Category.assoc, ldir']
        apply sqS.hom_ext
        · rw [← Category.assoc, ← joinMap_comm j f', Category.assoc, sqT.inl_desc,
            ← Category.assoc, hcond', Category.assoc]
        · rw [← Category.assoc, ← joinMap_comm j g', Category.assoc, sqT.inr_desc,
            ← Category.assoc, ← μ_inr, Category.assoc, s.condition, ← Category.assoc, ldir]
    · intro s; exact sqT.inr_desc _ _ _
    · intro s m hl hr
      apply sqT.hom_ext
      · rw [sqT.inl_desc, ← ldil', Category.assoc, hl]
      · rw [sqT.inr_desc, hr]
  have cube : IsPushout μ (leibnizJoin j f) (leibnizJoin j f') (joinMap (𝟙 T) g') :=
    IsPushout.of_isColimit colim
  show innerAnodyneExtensions (leibnizJoin j f')
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := innerAnodyneExtensions) cube hf

/-! ## Generators from satJ. -/

theorem leftHorn_mem_leibImgR_of_satJ {S T : SSet.{u}} (j : S ⟶ T) (hj : Mono j)
    (satJ : ∀ (M : ℕ) (k : Fin (M + 1 + 1)), k < Fin.last (M + 1) →
      monomorphisms SSet.{u} ≤ leibImgL' (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι) :
    leftHornInclusions.{u} ≤ leibImgR j := by
  rintro _ _ _ ⟨k, hk⟩
  exact satJ _ k hk j hj

/-! ## satI ASSEMBLY — Cobase + Retracts now DISCHARGED as instances; needs only the
remaining two instances (Coproducts + Transfinite) + satJ. -/

theorem satI_of_two_instances {S T : SSet.{u}} (j : S ⟶ T)
    (hcp : IsStableUnderCoproducts.{u} (leibImgR j))
    (htc : (leibImgR j).IsStableUnderTransfiniteComposition.{u})
    (hgen : leftHornInclusions.{u} ≤ leibImgR j) :
    leftAnodyneExtensions.{u} ≤ leibImgR j := by
  haveI := leibImgR_cobase j
  haveI := leibImgR_isStableUnderRetracts j
  haveI := hcp; haveI := htc
  rw [leftAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]
  have h1 : (coproducts.{u} leftHornInclusions.{u}) ≤ leibImgR j :=
    (coproducts_monotone hgen).trans (coproducts_le (leibImgR j))
  have h2 : (coproducts.{u} leftHornInclusions.{u}).pushouts ≤ leibImgR j :=
    (pushouts_monotone h1).trans pushouts_le
  have h3 : (transfiniteCompositions.{u} (coproducts.{u} leftHornInclusions.{u}).pushouts)
      ≤ leibImgR j :=
    (transfiniteCompositions_monotone h2).trans (transfiniteCompositions_le (leibImgR j))
  exact (retracts_monotone h3).trans (retracts_le _)

/-- `satI` given satJ + the two remaining second-slot instances (assembly form). -/
theorem satI_of_instances {S T : SSet.{u}} (j : S ⟶ T) (hj : Mono j)
    (hcp : IsStableUnderCoproducts.{u} (leibImgR j))
    (htc : (leibImgR j).IsStableUnderTransfiniteComposition.{u})
    (satJ : ∀ (M : ℕ) (k : Fin (M + 1 + 1)), k < Fin.last (M + 1) →
      monomorphisms SSet.{u} ≤ leibImgL' (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι) :
    leftAnodyneExtensions.{u} ≤ leibImgR j :=
  satI_of_two_instances j hcp htc (leftHorn_mem_leibImgR_of_satJ j hj satJ)

theorem joyal_leftAnodyne_join_mono_of_satI {S T A B : SSet.{u}} (j : S ⟶ T)
    (satI : leftAnodyneExtensions.{u} ≤ leibImgR j)
    (i : A ⟶ B) (hi : leftAnodyneExtensions.{u} i) :
    innerAnodyneExtensions (leibnizJoin j i) :=
  satI i hi

end
end SSet
