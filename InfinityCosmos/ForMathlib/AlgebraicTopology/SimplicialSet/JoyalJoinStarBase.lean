import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinTelescopeLeft
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.RelativeCellSingleCell
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.JoyalSpecialOuterHorn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Slice
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# The Joyal pushout-product: the generator base case `satJ`

Proves `satJ`, the generator base case of the Joyal pushout-product: for an inner horn
`Λ[M+1, k]` (`k < last`), every monomorphism `j` has `leibnizJoin j (Λ[M+1,k].ι)` inner-anodyne.
The argument passes through the Day-convolution unit coherence (`starr`, `star`), identifies the
relevant join with a boundary-cell inclusion (`H1z`), and reduces to the single-cell presentation
of monomorphisms (`baseZero_of_H1`, `satJ_of_baseZero`). These generators feed `satI` and hence
the full pushout-product, Kerodon 018J (Proposition 4.3.6.4, Joyal).
-/

open CategoryTheory Simplicial Opposite Limits MorphismProperty
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.DayFunctor
open CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct
open AugmentedSimplexCategory
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace SSet
universe u
noncomputable section

/-! ### Left-unitor helpers + pointwise left-unitor inverse. -/

lemma augLeftUnitor_hom (z : AugmentedSimplexCategory) : (λ_ z).hom = 𝟙 z := by
  cases z <;> rfl

lemma AC_leftUnitor_inv (x : AC) : (λ_ x).inv = 𝟙 x := by
  apply Quiver.Hom.unop_inj
  rw [unop_inv_leftUnitor, augLeftUnitor_hom]; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
lemma leftUnitor_inv_pt (M : AugDay.{u}) (x : AC) (y : M.functor.obj x) :
    (λ_ M).inv.natTrans.app x y
      = (DayFunctor.η (𝟙_ AugDay.{u}) M).app (𝟙_ AC, x)
          (DayFunctor.ν AC (Type u) PUnit.unit, y) := by
  have hA : (λ_ M).hom.natTrans.app x
      ((DayFunctor.η (𝟙_ AugDay.{u}) M).app (𝟙_ AC, x)
        (DayFunctor.ν AC (Type u) PUnit.unit, y)) = y := by
    have hlu := LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app
      (C := AC) (V := Type u) (D := AugDay.{u}) M x
    simp only [ι_obj, ι_map] at hlu
    have h := ConcreteCategory.congr_hom hlu
      (show 𝟙_ (Type u) ⊗ M.functor.obj x from (PUnit.unit, y))
    simp only [types_comp_apply, whiskerRight_apply, leftUnitor_hom_apply,
      AC_leftUnitor_inv, M.functor.map_id, types_id_apply] at h
    exact h
  have hfun : (λ_ M).hom.natTrans ≫ (λ_ M).inv.natTrans = 𝟙 (𝟙_ AugDay.{u} ⊗ M).functor := by
    have h := congrArg DayFunctor.Hom.natTrans (λ_ M).hom_inv_id
    simpa only [comp_natTrans, id_natTrans] using h
  have hg := congrArg
    (fun (t : (𝟙_ AugDay.{u} ⊗ M).functor ⟶ (𝟙_ AugDay.{u} ⊗ M).functor) => t.app x
      ((DayFunctor.η (𝟙_ AugDay.{u}) M).app (𝟙_ AC, x)
        (DayFunctor.ν AC (Type u) PUnit.unit, y))) hfun
  simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply] at hg
  rw [hA] at hg
  exact hg

lemma inr_unit_comp {z W : AugmentedSimplexCategory} (f : (𝟙_ AugmentedSimplexCategory) ⊗ z ⟶ W) :
    inr (𝟙_ AugmentedSimplexCategory) z ≫ f = f := by
  rw [show inr (𝟙_ AugmentedSimplexCategory) z = 𝟙 z from by cases z <;> rfl]
  exact Category.id_comp f

lemma starr_core (a b : ℕ) (sn : AC) (wa : (op (inclusion.obj ⦋a⦌) : AC) ⟶ 𝟙_ AC)
    (h : (op (inclusion.obj ⦋b⦌) : AC) ⟶ sn) :
    wa ⊗ₘ h = (inclusion.map (inr' ⦋a⦌ ⦋b⦌)).op ≫ h := by
  apply Quiver.Hom.unop_inj
  show wa.unop ⊗ₘ h.unop = h.unop ≫ inclusion.map (inr' ⦋a⦌ ⦋b⦌)
  have key := inr_comp_tensorHom wa.unop h.unop
  simp only [unop_tensorUnit] at key
  rw [inr_unit_comp] at key
  exact key

instance subsingleton_ucoy_at_star (X : AC) :
    Subsingleton ((ucoyDay.{u} X).functor.obj (op WithInitial.star)) := by
  constructor
  rintro ⟨f⟩ ⟨g⟩
  apply ULift.ext
  apply Quiver.Hom.unop_inj
  exact WithInitial.starInitial.hom_ext _ _

/-! ### THE coherence `starr` (Day-convolution left-unitor / join-unit coherence). -/

/-- A unit-coherence identity for the augmented-Day-convolution presentation of the join
`Δ[a] ⋆ Δ[b]` (the `ucoy`-tensor form). -/
theorem starr (a b : ℕ) :
    ((λ_ (augmentedDay.obj (Δ[b] : SSet.{u}))).inv
        ≫ (augmentedDayUnitTo (Δ[a] : SSet.{u})) ▷ (augmentedDay.obj (Δ[b] : SSet.{u})))
      ≫ ((augmentedDayStdIso.{u} a).hom ⊗ₘ (augmentedDayStdIso.{u} b).hom)
      ≫ (ucoyTensorIso.{u} (op (inclusion.obj ⦋a⦌)) (op (inclusion.obj ⦋b⦌))).hom
      = (augmentedDayStdIso.{u} b).hom ≫ ucoyMapOf.{u} (inr' ⦋a⦌ ⦋b⦌) := by
  apply DayFunctor.hom_ext
  simp only [comp_natTrans]
  refine NatTrans.ext (funext fun x => ?_)
  cases x using Opposite.rec with
  | _ z =>
    cases z with
    | star =>
      ext y
      exact Subsingleton.elim _ _
    | of m =>
      ext y
      change
        (ConcreteCategory.hom
          ((ucoyTensorIso.{u} (op (inclusion.obj ⦋a⦌)) (op (inclusion.obj ⦋b⦌))).hom.natTrans.app
            (op (WithInitial.of m))))
          ((ConcreteCategory.hom
            (((augmentedDayStdIso.{u} a).hom ⊗ₘ (augmentedDayStdIso.{u} b).hom).natTrans.app
              (op (WithInitial.of m))))
            ((ConcreteCategory.hom
              ((augmentedDayUnitTo (Δ[a] : SSet.{u}) ▷ augmentedDay.obj (Δ[b] : SSet.{u})).natTrans.app
                (op (WithInitial.of m))))
              ((ConcreteCategory.hom
                ((λ_ (augmentedDay.obj (Δ[b] : SSet.{u}))).inv.natTrans.app (op (WithInitial.of m))))
                y)))
        =
        (ConcreteCategory.hom ((ucoyMapOf.{u} (inr' ⦋a⦌ ⦋b⦌)).natTrans.app (op (WithInitial.of m))))
          ((ConcreteCategory.hom ((augmentedDayStdIso.{u} b).hom.natTrans.app (op (WithInitial.of m)))) y)
      rw [leftUnitor_inv_pt]
      have hWR := ConcreteCategory.congr_hom
          (convolutionExtensionUnit_comp_ι_map_whiskerRight_app (C := AC) (V := Type u) (D := AugDay.{u})
            (augmentedDayUnitTo (Δ[a]:SSet.{u})) (augmentedDay.obj (Δ[b]:SSet.{u})) (𝟙_ AC) (op (WithInitial.of m)))
          (show ((ι AC (Type u) AugDay.{u}).obj (𝟙_ AugDay.{u}) ⊠ (ι AC (Type u) AugDay.{u}).obj (augmentedDay.obj (Δ[b]:SSet.{u}))).obj (𝟙_ AC, op (WithInitial.of m))
            from (DayFunctor.ν AC (Type u) PUnit.unit, y))
      simp only [ConcreteCategory.comp_apply] at hWR
      have e1 :
          (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u}) ▷ augmentedDay.obj (Δ[b]:SSet.{u})).natTrans.app (op (WithInitial.of m))))
            ((ConcreteCategory.hom ((DayFunctor.η (𝟙_ AugDay.{u}) (augmentedDay.obj (Δ[b]:SSet.{u}))).app (𝟙_ AC, op (WithInitial.of m))))
              (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit, y))
          = (ConcreteCategory.hom ((DayFunctor.η (augmentedDay.obj (Δ[a]:SSet.{u})) (augmentedDay.obj (Δ[b]:SSet.{u}))).app (𝟙_ AC, op (WithInitial.of m))))
              (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u})).natTrans.app (𝟙_ AC))
                (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit), y) := hWR
      rw [e1]
      have hTensor := ConcreteCategory.congr_hom
          (convolutionExtensionUnit_comp_ι_map_tensorHom_app (C := AC) (V := Type u) (D := AugDay.{u})
            (augmentedDayStdIso.{u} a).hom (augmentedDayStdIso.{u} b).hom (𝟙_ AC) (op (WithInitial.of m)))
          (show ((ι AC (Type u) AugDay.{u}).obj (augmentedDay.obj (Δ[a]:SSet.{u})) ⊠ (ι AC (Type u) AugDay.{u}).obj (augmentedDay.obj (Δ[b]:SSet.{u}))).obj (𝟙_ AC, op (WithInitial.of m))
            from (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u})).natTrans.app (𝟙_ AC)) (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit), y))
      simp only [ConcreteCategory.comp_apply] at hTensor
      have e2 :
          (ConcreteCategory.hom (((augmentedDayStdIso.{u} a).hom ⊗ₘ (augmentedDayStdIso.{u} b).hom).natTrans.app (op (WithInitial.of m))))
            ((ConcreteCategory.hom ((DayFunctor.η (augmentedDay.obj (Δ[a]:SSet.{u})) (augmentedDay.obj (Δ[b]:SSet.{u}))).app (𝟙_ AC, op (WithInitial.of m))))
              (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u})).natTrans.app (𝟙_ AC))
                (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit), y))
          = (ConcreteCategory.hom ((DayFunctor.η (ucoyDay.{u} (op (inclusion.obj ⦋a⦌))) (ucoyDay.{u} (op (inclusion.obj ⦋b⦌)))).app (𝟙_ AC, op (WithInitial.of m))))
              (ConcreteCategory.hom ((augmentedDayStdIso.{u} a).hom.natTrans.app (𝟙_ AC))
                (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u})).natTrans.app (𝟙_ AC))
                  (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit)),
               ConcreteCategory.hom ((augmentedDayStdIso.{u} b).hom.natTrans.app (op (WithInitial.of m))) y) := hTensor
      rw [e2]
      have e3 :
          (ConcreteCategory.hom ((ucoyTensorIso.{u} (op (inclusion.obj ⦋a⦌)) (op (inclusion.obj ⦋b⦌))).hom.natTrans.app (op (WithInitial.of m))))
            ((ConcreteCategory.hom ((DayFunctor.η (ucoyDay.{u} (op (inclusion.obj ⦋a⦌))) (ucoyDay.{u} (op (inclusion.obj ⦋b⦌)))).app (𝟙_ AC, op (WithInitial.of m))))
              (ConcreteCategory.hom ((augmentedDayStdIso.{u} a).hom.natTrans.app (𝟙_ AC))
                (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u})).natTrans.app (𝟙_ AC))
                  (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit)),
               ConcreteCategory.hom ((augmentedDayStdIso.{u} b).hom.natTrans.app (op (WithInitial.of m))) y))
          = ULift.up
              ((ConcreteCategory.hom ((augmentedDayStdIso.{u} a).hom.natTrans.app (𝟙_ AC))
                  (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u})).natTrans.app (𝟙_ AC))
                    (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit))).down
                ⊗ₘ (ConcreteCategory.hom ((augmentedDayStdIso.{u} b).hom.natTrans.app (op (WithInitial.of m))) y).down) :=
        ucoyTensorIso_hom_η_apply.{u} (op (inclusion.obj ⦋a⦌)) (op (inclusion.obj ⦋b⦌)) (𝟙_ AC) (op (WithInitial.of m))
          (ConcreteCategory.hom ((augmentedDayStdIso.{u} a).hom.natTrans.app (𝟙_ AC))
            (ConcreteCategory.hom ((augmentedDayUnitTo (Δ[a]:SSet.{u})).natTrans.app (𝟙_ AC))
              (ConcreteCategory.hom (DayFunctor.ν AC (Type u)) PUnit.unit)),
           ConcreteCategory.hom ((augmentedDayStdIso.{u} b).hom.natTrans.app (op (WithInitial.of m))) y)
      rw [e3]
      exact congrArg ULift.up (starr_core a b (op (WithInitial.of m)) _ _)

/-! ### Geometry: `inr' ⦋0⦌ ⦋M+1⦌` is the coface `δ₀`. -/

theorem inr_zero_eq_cast_delta (M : ℕ) :
    inr' ⦋0⦌ ⦋M+1⦌
      = eqToHom (by rw [Nat.zero_add] : (⦋M+1⦌ : SimplexCategory) = ⦋0+(M+1)⦌)
          ≫ SimplexCategory.δ (0 : Fin (0+(M+1)+1+1)) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  have he := inr'_eval ⦋0⦌ ⦋M+1⦌ k
  simp only [SimplexCategory.len_mk] at he
  rw [SimplexCategory.comp_toOrderHom]
  simp only [OrderHom.comp_coe, Function.comp_apply]
  apply Fin.ext
  rw [he]
  simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.eqToHom_toOrderHom, Fin.val_cast,
    OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.val_natAdd, Fin.succAboveOrderEmb_apply, Fin.succAbove_zero, Fin.val_succ, Fin.val_cast]
  omega

theorem range_inr_zero_eq_face (M : ℕ) :
    Subcomplex.range (stdSimplex.{u}.map (inr' ⦋0⦌ ⦋M+1⦌))
      = stdSimplex.face {(0 : Fin (0 + (M+1) + 1 + 1))}ᶜ := by
  rw [inr_zero_eq_cast_delta, Functor.map_comp]
  rw [Subcomplex.range_comp, Subcomplex.range_eq_top, Subcomplex.image_top]
  show Subcomplex.range (stdSimplex.{u}.δ (0 : Fin (0+(M+1)+1+1))) = _
  rw [stdSimplex.range_δ]

/-! ### The empty boundary is the join unit. -/

lemma joinMap_id_right' {X X' Y : SSet.{u}} (f : X ⟶ X') :
    joinMap f (𝟙 Y) = (joinFunctor.map f).app Y := by
  rw [joinMap_id_right]; rfl

lemma joinInr_nat (M : ℕ) :
    joinInr ((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) : SSet) (Δ[M+1] : SSet.{u})
        ≫ joinMap (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι (𝟙 (Δ[M+1] : SSet.{u}))
      = joinInr (Δ[0] : SSet.{u}) (Δ[M+1] : SSet.{u}) := by
  rw [joinMap_id_right']; exact joinInr_naturality_left _ _

lemma joinInr_isIso_of_iso {X : SSet.{u}} (e : X ≅ (⊥_ SSet.{u})) (K : SSet.{u}) :
    IsIso (joinInr X K) := by
  let giso := ((evaluation SSet.{u} SSet.{u}).obj K).mapIso (joinFunctor.mapIso e)
  have key : joinInr X K ≫ giso.hom = joinInr (⊥_ SSet.{u}) K :=
    joinInr_naturality_left e.hom K
  have h2 : joinInr X K = (giso ≪≫ joinBotIso K).inv := by
    rw [Iso.trans_inv, show (joinBotIso K).inv = joinInr (⊥_ SSet.{u}) K from rfl]
    exact (Iso.eq_comp_inv giso).mpr key
  rw [h2]; infer_instance

instance boundaryZero_join_isIso (M : ℕ) :
    IsIso (joinInr ((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) : SSet) (Δ[M+1] : SSet.{u})) :=
  joinInr_isIso_of_iso
    ((boundary_zero ▸ Subcomplex.isInitialBot :
        IsInitial ((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})).uniqueUpToIso
      initialIsInitial) _

/-! ### Reduction chain. -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The same unit coherence in `joinMiddleIso` form, used to compute `joinInr_joinStdSimplex`. -/
theorem star (a b : ℕ) :
    ((λ_ (augmentedDay.obj (Δ[b] : SSet.{u}))).inv
        ≫ (augmentedDayUnitTo (Δ[a] : SSet.{u})) ▷ (augmentedDay.obj (Δ[b] : SSet.{u})))
      ≫ (joinMiddleIso.{u} a b).hom
      = augmentedDay.map (stdSimplex.{u}.map (inr' ⦋a⦌ ⦋b⦌)) := by
  have hRHS : augmentedDay.map (stdSimplex.{u}.map (inr' ⦋a⦌ ⦋b⦌))
      = ((augmentedDayStdIso.{u} b).hom ≫ ucoyMapOf.{u} (inr' ⦋a⦌ ⦋b⦌))
          ≫ (augmentedDayStdIso.{u} (a+b+1)).inv :=
    (Iso.eq_comp_inv _).mpr (augmentedDayStdIso_naturality (inr' ⦋a⦌ ⦋b⦌)).symm
  rw [hRHS]
  unfold joinMiddleIso
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% starr a b]

theorem joinInr_joinStdSimplex (a b : ℕ) :
    joinInr (Δ[a] : SSet.{u}) (Δ[b] : SSet.{u}) ≫ (joinStdSimplex.{u} a b).hom
      = stdSimplex.{u}.map (inr' ⦋a⦌ ⦋b⦌) := by
  have hlhs : joinInr (Δ[a] : SSet.{u}) (Δ[b] : SSet.{u}) ≫ (joinStdSimplex.{u} a b).hom
      = restrictAugmentedDay.map
          (((λ_ (augmentedDay.obj (Δ[b] : SSet.{u}))).inv
              ≫ (augmentedDayUnitTo (Δ[a] : SSet.{u})) ▷ (augmentedDay.obj (Δ[b] : SSet.{u})))
            ≫ (joinMiddleIso.{u} a b).hom) := by
    unfold joinStdSimplex joinStdSimplexOf joinInr
    simp only [Functor.mapIso_hom, id_eq]
    exact (restrictAugmentedDay.map_comp _ _).symm
  rw [hlhs, star]; rfl

/-- The boundary-cell join `∂Δ[0] ⋆ Δ[M+1]`, transported by `joinStdSimplex`, has image the
union of the front-vertex faces — the face decomposition feeding `baseZero_of_H1`. -/
theorem H1z (M : ℕ) :
    (Subcomplex.range (joinMap (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
          (𝟙 (Δ[M + 1] : SSet.{u})))).image (joinStdSimplex.{u} 0 (M + 1)).hom =
        ⨆ i : Fin (0 + 1), stdSimplex.face {joinLeftVertex 0 (M + 1) i}ᶜ := by
  haveI : Unique (Fin (0+1)) := inferInstanceAs (Unique (Fin 1))
  rw [iSup_unique (fun i : Fin (0+1) => stdSimplex.face {joinLeftVertex 0 (M + 1) i}ᶜ)]
  have hA : Subcomplex.range (joinMap (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
      (𝟙 (Δ[M+1] : SSet.{u})))
      = Subcomplex.range (joinInr (Δ[0] : SSet.{u}) (Δ[M+1] : SSet.{u})) := by
    rw [← joinInr_nat M, Subcomplex.range_comp,
        Subcomplex.range_eq_top
          (f := joinInr ((∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) : SSet) (Δ[M+1] : SSet.{u})),
        Subcomplex.image_top]
  rw [hA, ← Subcomplex.range_comp, joinInr_joinStdSimplex, range_inr_zero_eq_face]
  congr 3
  apply Fin.ext
  simp [joinLeftVertex]

/-! ### n=0 boundary generator. -/

/-- The dimension-zero base case of `satJ`: given the face decomposition `H1z`, the boundary-cell
join `leibnizJoin (∂Δ[0] ↪ Δ[0]) (𝟙 Δ[M+1])` is inner-anodyne. -/
theorem baseZero_of_H1 (M : ℕ) (k : Fin (M + 1 + 1)) (hk : k < Fin.last (M + 1))
    (H1₀ : (Subcomplex.range (joinMap (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
              (𝟙 (Δ[M + 1] : SSet.{u})))).image (joinStdSimplex.{u} 0 (M + 1)).hom =
            ⨆ i : Fin (0 + 1), stdSimplex.face {joinLeftVertex 0 (M + 1) i}ᶜ) :
    innerAnodyneExtensions.{u}
      (leibnizJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
        (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι) := by
  have hrange :
      Subcomplex.range
          (leibnizJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
              (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι ≫
            (joinStdSimplex.{u} 0 (M + 1)).hom) =
        Λ[0 + (M + 1) + 1, joinRightVertex 0 (M + 1) k] := by
    rw [Subcomplex.range_comp, range_leibnizJoin, sup_comm]
    exact fhorn_identity_of_faceImages 0 (M + 1) k H1₀ (fhorn_H2 0 M k)
  haveI hm : Mono (leibnizJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
      (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι) :=
    leibnizJoin_mono _ _ inferInstance inferInstance
  haveI : Mono (joinStdSimplex.{u} 0 (M + 1)).hom := inferInstance
  haveI : Mono (leibnizJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
      (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι ≫
        (joinStdSimplex.{u} 0 (M + 1)).hom) := inferInstance
  have iso :
      Arrow.mk (leibnizJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
          (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι) ≅
        Arrow.mk (Λ[0 + (M + 1) + 1, joinRightVertex 0 (M + 1) k].ι) := by
    refine (Arrow.isoMk (Iso.refl _) (joinStdSimplex.{u} 0 (M + 1)) (by rfl) :
        Arrow.mk (leibnizJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
            (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι) ≅
          Arrow.mk (leibnizJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι
            (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι ≫
              (joinStdSimplex.{u} 0 (M + 1)).hom)) ≪≫ ?_
    exact arrowMk_iso_of_mono_range _ hrange
  exact (innerAnodyneExtensions.arrow_mk_iso_iff iso).mpr (joyalBase_innerAnodyne 0 (M + 1) k hk)

/-! ### satJ wiring (the four weak-saturation hypotheses discharged from Deps/SingleCell). -/

/-- Given the dimension-zero base case, every monomorphism lies in `leibImgL (Λ[M+1,k].ι)`, via
the single-cell presentation of monomorphisms. -/
theorem satJ_of_baseZero (M : ℕ) (k : Fin (M + 1 + 1)) (hk : k < Fin.last (M + 1))
    (h0 : leibImgL (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι
            (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι) :
    monomorphisms SSet.{u} ≤
      leibImgL (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι := by
  set K := (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι with hK
  haveI hcb : (leibImgL K).IsStableUnderCobaseChange := leibImgL_cobase K
  haveI htc : (leibImgL K).IsStableUnderTransfiniteComposition.{u} :=
    leibImgL_isStableUnderTransfiniteComposition K
  refine singleCell.monomorphisms_le_of_boundary_singleCell (leibImgL K) ?_
  intro n
  cases n with
  | zero => exact h0
  | succ P => exact genCell_innerAnodyne P M k hk

/-! ### The generator base case `satJ`. -/

/-- The generator base case of the Joyal pushout-product (Kerodon 018J, Proposition 4.3.6.4): for
an inner horn `Λ[M+1, k]` (`k < last`), every monomorphism `j` has `leibnizJoin j (Λ[M+1,k].ι)`
inner-anodyne. -/
theorem satJ (M : ℕ) (k : Fin (M + 1 + 1)) (hk : k < Fin.last (M + 1)) :
    monomorphisms SSet.{u} ≤
      leibImgL (Λ[M + 1, k] : (Δ[M + 1] : SSet.{u}).Subcomplex).ι :=
  satJ_of_baseZero M k hk (baseZero_of_H1 M k hk (H1z M))

end
end SSet
