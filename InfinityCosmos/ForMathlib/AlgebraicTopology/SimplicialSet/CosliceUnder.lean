import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Slice
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration

section
/-!
# Coslice of simplicial sets via the join (LEFT-fixed mirror of `Slice.lean`)

The coslice `C_{f/}` and its relative projection, the left-fixed mirror of the slice package in
`Slice.lean`. The elementary coslice presheaf `cosliceUnder p` (`C_{p/}`) is built from the
fixed-left join functor `joinCoUnder K = K ⋆ -`, with its colimit preservation, Kan extension and
adjunction `coAdj₂`, and the coslice universal property `cosliceHomEquiv` (mirroring
`joinUnder`/`adj₂`/`sliceHomEquiv`). The coslice relative projection `cosliceProj` is presented as
a `PullbackObjObj.π` and shown to satisfy the left-lifting and left-fibration facts
`hasLiftingProperty_cosliceProj` and `leftFibrations_cosliceProj`. This coslice is what the
`i = last` special-outer-horn filler runs through.
-/

open CategoryTheory Simplicial Opposite Limits
open CategoryTheory.MonoidalCategory
open scoped Simplicial

universe u w w'

namespace SSet

noncomputable section

/-! ## The elementary coslice presheaf -/

/-- The set of maps `K ⋆ Y ⟶ C` restricting to `p` on the LEFT factor. -/
abbrev CoOverPt {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) : Type u :=
  { q : K ⋆ Y ⟶ C // joinInl' K Y ≫ q = p }

/-- The coslice simplicial set `C_{p/}`.  Its `n`-simplices are maps `K ⋆ Δ[n] ⟶ C`
restricting to `p` on the left factor. -/
def cosliceUnder {K C : SSet.{u}} (p : K ⟶ C) : SSet.{u} where
  obj n := CoOverPt p (stdSimplex.obj n.unop)
  map {n m} f :=
    ↾fun q =>
      (⟨(joinFunctor.obj K).map (stdSimplex.map f.unop) ≫ q.1, by
        rw [← Category.assoc, joinInl'_naturality_right]
        exact q.2⟩ : CoOverPt p (stdSimplex.obj m.unop))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show (joinFunctor.obj K).map (stdSimplex.map (𝟙 n).unop) ≫ q.1 = q.1
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show (joinFunctor.obj K).map (stdSimplex.map (f ≫ g).unop) ≫ q.1 =
      (joinFunctor.obj K).map (stdSimplex.map g.unop) ≫
        (joinFunctor.obj K).map (stdSimplex.map f.unop) ≫ q.1
    simp only [unop_comp, Functor.map_comp, Category.assoc]

/-! ## The fixed-left join functor into the coslice, and its colimit preservation -/

/-- The fixed-left join functor lifted to the coslice under the left factor. -/
def joinCoUnder (K : SSet.{u}) : SSet.{u} ⥤ Under K where
  obj Y := Under.mk (joinInl' K Y)
  map {Y Y'} f := Under.homMk ((joinFunctor.obj K).map f) (joinInl'_naturality_right f K)
  map_id Y := by
    apply Under.UnderMorphism.ext
    show (joinFunctor.obj K).map (𝟙 Y) = 𝟙 _
    rw [(joinFunctor.obj K).map_id]
  map_comp {Y Y' Y''} f g := by
    apply Under.UnderMorphism.ext
    show (joinFunctor.obj K).map (f ≫ g) =
      (joinFunctor.obj K).map f ≫ (joinFunctor.obj K).map g
    rw [(joinFunctor.obj K).map_comp]

@[simp]
theorem joinCoUnder_forget (K : SSet.{u}) :
    joinCoUnder K ⋙ Under.forget K = joinFunctor.obj K :=
  rfl

theorem joinCoUnder_preservesConnectedColimits_of_joinFunctor_obj
    (J : Type w) [Category.{w'} J] [IsConnected J] (K : SSet.{u})
    [PreservesColimitsOfShape J (joinFunctor.obj K)] :
    PreservesColimitsOfShape J (joinCoUnder K) := by
  haveI : PreservesColimitsOfShape J (joinCoUnder K ⋙ Under.forget K) := by
    change PreservesColimitsOfShape J (joinFunctor.obj K)
    infer_instance
  exact Limits.preservesColimitsOfShape_of_reflects_of_preserves (joinCoUnder K) (Under.forget K)

theorem joinCoUnder_preservesConnectedColimits_of_tensorLeft
    (J : Type w) [Category.{w'} J] [IsConnected J] [HasColimitsOfShape J (Type u)]
    (K : SSet.{u})
    [PreservesColimitsOfShape J (tensorLeft (augmentedDay.obj K))] :
    PreservesColimitsOfShape J (joinCoUnder K) := by
  haveI : PreservesColimitsOfShape J (joinFunctor.obj K) :=
    joinFunctor_obj_preservesConnectedColimits_of_tensorLeft J K
  exact joinCoUnder_preservesConnectedColimits_of_joinFunctor_obj J K

/-! ## Initial-object handling (left factor) -/

instance joinInl'_initial_isIso (K : SSet.{u}) : IsIso (joinInl' K (⊥_ SSet.{u})) := by
  unfold joinInl'
  apply Functor.map_isIso

/-- `K ⋆ ⊥ ≅ K`: joining with the initial object on the right gives `K` back. -/
def joinCoBotIso (K : SSet.{u}) : K ⋆ (⊥_ SSet.{u}) ≅ K :=
  (asIso (joinInl' K (⊥_ SSet.{u}))).symm

/-- `(K ⋆ -)` sends the initial object to `Under.mk (𝟙 K)`, the initial coslice object. -/
def joinCoUnderBotIsoInitial (K : SSet.{u}) :
    (joinCoUnder K).obj (⊥_ SSet.{u}) ≅ Under.mk (𝟙 K) :=
  Under.isoMk (asIso (joinInl' K (⊥_ SSet.{u}))).symm (by
    show joinInl' K (⊥_ SSet.{u}) ≫ inv (joinInl' K (⊥_ SSet.{u})) = 𝟙 K
    simp)

/-- `(joinCoUnder K).obj ⊥` is initial in `Under K`. -/
def joinCoUnderBotIsInitial (K : SSet.{u}) : IsInitial ((joinCoUnder K).obj (⊥_ SSet.{u})) :=
  IsInitial.ofIso Under.mkIdInitial (joinCoUnderBotIsoInitial K).symm

instance joinCoUnder_preservesInitial (K : SSet.{u}) :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (joinCoUnder K) := by
  haveI : HasInitial (Under K) := (Under.mkIdInitial (X := K)).hasInitial
  haveI : PreservesColimit (Functor.empty.{0} SSet.{u}) (joinCoUnder K) :=
    preservesInitial_of_iso (joinCoUnder K)
      ((initialIsInitial (C := Under K)).uniqueUpToIso (joinCoUnderBotIsInitial K))
  exact preservesColimitsOfShape_pempty_of_preservesInitial _

instance joinCoUnder_preservesCoequalizers (K : SSet.{u}) :
    PreservesColimitsOfShape WalkingParallelPair (joinCoUnder K) := by
  exact joinCoUnder_preservesConnectedColimits_of_tensorLeft WalkingParallelPair K

/-! ## The factorization through `Under ⊥` (for the size-`u` colimit preservation) -/

/-- Factorization of `joinCoUnder K` through `Under ⊥` and `(K ⋆ -)`. -/
def joinCoUnderFactor (K : SSet.{u}) : SSet.{u} ⥤ Under K :=
  underInitial ⋙ Under.post (X := (⊥_ SSet.{u})) (joinFunctor.obj K) ⋙
    Under.map (joinCoBotIso K).inv

/-- The factorization `joinCoUnderFactor K` agrees with `joinCoUnder K`. -/
def joinCoUnderFactorIso (K : SSet.{u}) : joinCoUnderFactor K ≅ joinCoUnder K :=
  NatIso.ofComponents
    (fun Y => Under.isoMk (Iso.refl _) (by
      change (joinCoBotIso K).inv ≫ (joinFunctor.obj K).map (initial.to Y) = joinInl' K Y
      rw [show (joinCoBotIso K).inv = joinInl' K (⊥_ SSet.{u}) from rfl]
      rw [joinInl'_naturality_right]))
    (by
      intro Y Y' f
      ext n x
      rfl)

theorem joinCoUnder_preservesColimitsOfShape (K : SSet.{u})
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape (WithInitial J) (Type u)] :
    PreservesColimitsOfShape J (joinCoUnder K) := by
  haveI : PreservesColimitsOfShape J (underInitial : SSet.{u} ⥤ Under (⊥_ SSet.{u})) :=
    by
      let h := (Under.equivalenceOfIsInitial (X := (⊥_ SSet.{u})) initialIsInitial).symm.toAdjunction.leftAdjoint_preservesColimits
      exact h.preservesColimitsOfShape
  haveI : PreservesColimitsOfShape (WithInitial J) (joinFunctor.obj K) := by
    haveI : HasInitial (WithInitial J) := WithInitial.starInitial.hasInitial
    haveI : IsConnected (WithInitial J) := isConnected_of_hasInitial (WithInitial J)
    haveI : HasColimitsOfShape (WithInitial J) (Type u) := inferInstance
    exact joinFunctor_obj_preservesConnectedColimits_of_tensorLeft (WithInitial J) K
  haveI : PreservesColimitsOfShape J
      (Under.post (X := (⊥_ SSet.{u})) (joinFunctor.obj K)) :=
    inferInstance
  haveI : PreservesColimitsOfShape J (Under.map (joinCoBotIso K).inv) :=
    by
      let h := (Under.mapIso (joinCoBotIso K).symm).toAdjunction.leftAdjoint_preservesColimits
      exact h.preservesColimitsOfShape
  haveI : PreservesColimitsOfShape J (joinCoUnderFactor K) := by
    change PreservesColimitsOfShape J
      (underInitial ⋙ Under.post (X := (⊥_ SSet.{u})) (joinFunctor.obj K) ⋙
        Under.map (joinCoBotIso K).inv)
    infer_instance
  exact preservesColimitsOfShape_of_natIso (joinCoUnderFactorIso K)

/-! ## The Kan extension + adjunction -/

/-- The restriction of `joinCoUnder K` to representables, `SimplexCategory ⥤ Under K`. -/
abbrev joinCoUnderOnSimplex (K : SSet.{u}) : SimplexCategory ⥤ Under K :=
  uliftYoneda.{u} ⋙ joinCoUnder K

/-- The restricted-yoneda coslice functor `Under K ⥤ SSet`, right adjoint to `K ⋆ -`. -/
abbrev coSliceFunctorRestricted (K : SSet.{u}) : Under K ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (joinCoUnderOnSimplex K)

instance joinCoUnder_preservesColimitsOfSize_zero (K : SSet.{u}) :
    PreservesColimitsOfSize.{0, u} (joinCoUnder K) where
  preservesColimitsOfShape {J} [Category.{0} J] := by
    haveI : HasColimitsOfShape (WithInitial J) (Type u) := inferInstance
    exact joinCoUnder_preservesColimitsOfShape K J

/-- The (identity) unit exhibiting `joinCoUnder K` as a left Kan extension of its restriction. -/
def joinCoUnderExtensionUnit (K : SSet.{u}) :
    joinCoUnderOnSimplex K ⟶ uliftYoneda.{u} ⋙ joinCoUnder K :=
  𝟙 _

instance joinCoUnder_isLeftKanExtension (K : SSet.{u}) :
    (joinCoUnder K).IsLeftKanExtension (joinCoUnderExtensionUnit K) :=
  Presheaf.isLeftKanExtension_of_preservesColimits.{0} (A := joinCoUnderOnSimplex K)
    (L := joinCoUnder K) (Iso.refl _)

/-- The coslice adjunction `joinCoUnder K ⊣ coSliceFunctorRestricted K` (`K ⋆ -` is left adjoint
to the restricted coslice functor), from the left Kan extension. -/
def coAdj₂ (K : SSet.{u}) : joinCoUnder K ⊣ coSliceFunctorRestricted K :=
  Presheaf.uliftYonedaAdjunction.{0} (A := joinCoUnderOnSimplex K) (L := joinCoUnder K)
    (joinCoUnderExtensionUnit K)

/-! ## The coslice universal property -/

/-- Maps out of `joinCoUnder K` are exactly maps `K ⋆ Y ⟶ C` restricting to `p` on `K`. -/
def coOverPtEquivUnderHom {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) :
    CoOverPt p Y ≃ ((joinCoUnder K).obj Y ⟶ Under.mk p) where
  toFun q := Under.homMk q.1 q.2
  invFun g := ⟨g.right, Under.w g⟩
  left_inv q := by
    cases q
    rfl
  right_inv g := by
    ext
    rfl

/-- The restricted slice functor evaluated at `p` is the coslice presheaf `C_{p/}`. -/
def restrictedCoSliceIso {K C : SSet.{u}} (p : K ⟶ C) :
    (coSliceFunctorRestricted K).obj (Under.mk p) ≅ cosliceUnder p :=
  NatIso.ofComponents
    (fun n => Equiv.toIso
      (Equiv.ulift.trans ((coOverPtEquivUnderHom p (stdSimplex.obj n.unop)).symm)))
    (by
      intro n m f
      ext g
      cases g
      rfl)

/-- The relative coslice universal property: maps `K ⋆ Y ⟶ C` restricting to `p` on `K`
are the same as maps `Y ⟶ C_{p/}`. -/
def cosliceHomEquiv {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) :
    CoOverPt p Y ≃ (Y ⟶ cosliceUnder p) :=
  (coOverPtEquivUnderHom p Y).trans (((coAdj₂ K).homEquiv Y (Under.mk p)).trans
    (restrictedCoSliceIso p).homToEquiv)

end

end SSet
end

section
/-!
# Coslice relative slice projection (LEFT-fixed mirror of the slice projection)

Mirrors the proven `sliceProj`/`hasLiftingProperty_sliceProj`/`leftFibrations_sliceProj`
(`Slice.lean`) transposed for the coslice (free factor = the edge on the RIGHT).
-/

universe u
open CategoryTheory MonoidalCategory Simplicial Opposite Limits MorphismProperty

namespace SSet
noncomputable section

/-! ## Join inclusion naturality in the LEFT (cone-point) variable -/

@[reassoc]
theorem joinInl'_naturality_left {X X' : SSet.{u}} (f : X ⟶ X') (Y : SSet.{u}) :
    joinInl' X Y ≫ (joinFunctor.map f).app Y = f ≫ joinInl' X' Y := by
  change
    restrictAugmentedDay.map
          ((ρ_ (augmentedDay.obj X)).inv ≫ (augmentedDay.obj X) ◁ (augmentedDayUnitTo Y)) ≫
        restrictAugmentedDay.map ((augmentedDay.map f) ▷ (augmentedDay.obj Y)) =
      restrictAugmentedDay.map (augmentedDay.map f) ≫
        restrictAugmentedDay.map
          ((ρ_ (augmentedDay.obj X')).inv ≫ (augmentedDay.obj X') ◁ (augmentedDayUnitTo Y))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Category.assoc, whisker_exchange, ← Category.assoc, ← rightUnitor_inv_naturality,
    Category.assoc]

/-! ## Coslice maps: base-contravariance (cone point) and target-covariance -/

/-- `cosliceMapBase jST : cosliceUnder pT ⟶ cosliceUnder pS`, `pS = jST ≫ pT`. -/
def cosliceMapBase {S T C : SSet.{u}} (jST : S ⟶ T) {pT : T ⟶ C} {pS : S ⟶ C}
    (hp : pS = jST ≫ pT) : cosliceUnder pT ⟶ cosliceUnder pS where
  app n := ↾fun q =>
    (⟨(joinFunctor.map jST).app (stdSimplex.obj n.unop) ≫ q.1, by
        calc joinInl' S (stdSimplex.obj n.unop) ≫
              ((joinFunctor.map jST).app (stdSimplex.obj n.unop) ≫ q.1)
            = (joinInl' S (stdSimplex.obj n.unop) ≫
                (joinFunctor.map jST).app (stdSimplex.obj n.unop)) ≫ q.1 :=
              (Category.assoc _ _ _).symm
          _ = (jST ≫ joinInl' T (stdSimplex.obj n.unop)) ≫ q.1 :=
              congrArg (· ≫ q.1) (joinInl'_naturality_left jST (stdSimplex.obj n.unop))
          _ = jST ≫ (joinInl' T (stdSimplex.obj n.unop) ≫ q.1) := Category.assoc _ _ _
          _ = jST ≫ pT := congrArg (jST ≫ ·) q.2
          _ = pS := hp.symm⟩ :
      CoOverPt pS (stdSimplex.obj n.unop))
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show (joinFunctor.map jST).app (stdSimplex.obj m.unop) ≫
        (joinFunctor.obj T).map (stdSimplex.map f.unop) ≫ q.1 =
      (joinFunctor.obj S).map (stdSimplex.map f.unop) ≫
        (joinFunctor.map jST).app (stdSimplex.obj n.unop) ≫ q.1
    rw [← Category.assoc, ← Category.assoc,
      ((joinFunctor.map jST).naturality (stdSimplex.map f.unop)).symm]

/-- `cosliceMapTarget f : cosliceUnder p ⟶ cosliceUnder (p ≫ f)`. -/
def cosliceMapTarget {K C C' : SSet.{u}} {p : K ⟶ C} (f : C ⟶ C') :
    cosliceUnder p ⟶ cosliceUnder (p ≫ f) where
  app n := ↾fun q =>
    (⟨q.1 ≫ f, by
        calc joinInl' K (stdSimplex.obj n.unop) ≫ (q.1 ≫ f)
            = (joinInl' K (stdSimplex.obj n.unop) ≫ q.1) ≫ f := (Category.assoc _ _ _).symm
          _ = p ≫ f := congrArg (· ≫ f) q.2⟩ :
      CoOverPt (p ≫ f) (stdSimplex.obj n.unop))
  naturality {n m} f' := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show ((joinFunctor.obj K).map (stdSimplex.map f'.unop) ≫ q.1) ≫ f =
      (joinFunctor.obj K).map (stdSimplex.map f'.unop) ≫ (q.1 ≫ f)
    exact Category.assoc _ _ _

/-! ## `CoOverPt` transposition-domain maps -/

/-- Reindexes a coslice point along `jST`: `CoOverPt pT Y → CoOverPt (jST ≫ pT) Y`. -/
def coOverPtMapBase {S T C : SSet.{u}} (jST : S ⟶ T) {pT : T ⟶ C} (Y : SSet.{u})
    (q : CoOverPt pT Y) : CoOverPt (jST ≫ pT) Y :=
  ⟨(joinFunctor.map jST).app Y ≫ q.1, by
    calc joinInl' S Y ≫ ((joinFunctor.map jST).app Y ≫ q.1)
        = (joinInl' S Y ≫ (joinFunctor.map jST).app Y) ≫ q.1 := (Category.assoc _ _ _).symm
      _ = (jST ≫ joinInl' T Y) ≫ q.1 := congrArg (· ≫ q.1) (joinInl'_naturality_left jST Y)
      _ = jST ≫ (joinInl' T Y ≫ q.1) := Category.assoc _ _ _
      _ = jST ≫ pT := congrArg (jST ≫ ·) q.2⟩

/-- Postcomposes a coslice point by `f`: `CoOverPt p Y → CoOverPt (p ≫ f) Y`. -/
def coOverPtPost {K C C' : SSet.{u}} {p : K ⟶ C} (f : C ⟶ C') {Y : SSet.{u}}
    (q : CoOverPt p Y) : CoOverPt (p ≫ f) Y :=
  ⟨q.1 ≫ f, by
    calc joinInl' K Y ≫ (q.1 ≫ f)
        = (joinInl' K Y ≫ q.1) ≫ f := (Category.assoc _ _ _).symm
      _ = p ≫ f := congrArg (· ≫ f) q.2⟩

/-- Restricts a coslice point along `φ : Z ⟶ Y`: `CoOverPt p Y → CoOverPt p Z`. -/
def coOverPtRestrict {K C : SSet.{u}} {p : K ⟶ C} {Z Y : SSet.{u}} (φ : Z ⟶ Y)
    (q : CoOverPt p Y) : CoOverPt p Z :=
  ⟨(joinFunctor.obj K).map φ ≫ q.1, by
    rw [← Category.assoc, joinInl'_naturality_right]; exact q.2⟩

/-! ## The relative coslice projection -/

/-- `cosliceMapBase` and `cosliceMapTarget` commute (the pullback square). -/
theorem cosliceMapBase_target_comm {S T X Y : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ X) (p : X ⟶ Y) :
    (cosliceMapBase jST (rfl : jST ≫ σ = jST ≫ σ)) ≫ cosliceMapTarget p =
      (cosliceMapTarget p) ≫ cosliceMapBase jST (rfl : jST ≫ (σ ≫ p) = jST ≫ (σ ≫ p)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  show ((joinFunctor.map jST).app (stdSimplex.obj n.unop) ≫ q.1) ≫ p =
    (joinFunctor.map jST).app (stdSimplex.obj n.unop) ≫ (q.1 ≫ p)
  exact Category.assoc _ _ _

/-- The RELATIVE coslice projection over a fixed simplex `σ : T ⟶ X`. -/
def cosliceProj {S T X Y : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ X) (p : X ⟶ Y) :
    cosliceUnder σ ⟶
      pullback (cosliceMapTarget (p := jST ≫ σ) p)
        (cosliceMapBase jST (rfl : jST ≫ (σ ≫ p) = jST ≫ (σ ≫ p))) :=
  pullback.lift (cosliceMapBase jST rfl) (cosliceMapTarget p)
    (cosliceMapBase_target_comm jST σ p)

@[simp] lemma cosliceProj_fst {S T X Y : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ X) (p : X ⟶ Y) :
    cosliceProj jST σ p ≫ pullback.fst _ _ = cosliceMapBase jST rfl :=
  pullback.lift_fst _ _ _

@[simp] lemma cosliceProj_snd {S T X Y : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ X) (p : X ⟶ Y) :
    cosliceProj jST σ p ≫ pullback.snd _ _ = cosliceMapTarget p :=
  pullback.lift_snd _ _ _


/-! ## The gateway: concrete simplex formula for `cosliceHomEquiv` -/

theorem cosliceHomEquiv_app_coe {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) (q : CoOverPt p Y)
    (Z : SimplexCategoryᵒᵖ) (z : Y.obj Z) :
    ((cosliceHomEquiv p Y q).app Z z).1 =
      (joinFunctor.obj K).map (uliftYonedaEquiv.symm z) ≫ q.1 := by
  simp only [cosliceHomEquiv, Equiv.trans_apply, Iso.homToEquiv_apply, coAdj₂,
    NatTrans.comp_app_apply, Presheaf.uliftYonedaAdjunction_homEquiv_app,
    restrictedCoSliceIso, NatIso.ofComponents_hom_app,
    coOverPtEquivUnderHom, Equiv.coe_fn_mk,
    joinCoUnderExtensionUnit, NatTrans.id_app, Category.id_comp]
  rfl

/-! ## The three hom-equiv naturalities -/

theorem cosliceHomEquiv_naturality_left {K C : SSet.{u}} (p : K ⟶ C) {Z Y : SSet.{u}}
    (φ : Z ⟶ Y) (q : CoOverPt p Y) :
    φ ≫ cosliceHomEquiv p Y q = cosliceHomEquiv p Z (coOverPtRestrict φ q) := by
  simp only [cosliceHomEquiv, Equiv.trans_apply, Iso.homToEquiv_apply]
  rw [← Category.assoc]
  congr 1
  rw [← (coAdj₂ K).homEquiv_naturality_left]
  congr 1

theorem cosliceHomEquiv_naturality_base {S T C : SSet.{u}} (jST : S ⟶ T) {pT : T ⟶ C}
    (Y : SSet.{u}) (q : CoOverPt pT Y) :
    cosliceHomEquiv (jST ≫ pT) Y (coOverPtMapBase jST Y q)
      = cosliceHomEquiv pT Y q ≫ cosliceMapBase jST rfl := by
  apply NatTrans.ext
  funext Z
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  rw [NatTrans.comp_app_apply]
  rw [cosliceHomEquiv_app_coe (jST ≫ pT) Y (coOverPtMapBase jST Y q) Z z]
  show (joinFunctor.obj S).map (uliftYonedaEquiv.symm z) ≫ (coOverPtMapBase jST Y q).1
      = (joinFunctor.map jST).app (stdSimplex.obj Z.unop) ≫
          ((cosliceHomEquiv pT Y q).app Z z).1
  rw [cosliceHomEquiv_app_coe pT Y q Z z]
  show (joinFunctor.obj S).map (uliftYonedaEquiv.symm z) ≫
        ((joinFunctor.map jST).app Y ≫ q.1)
      = (joinFunctor.map jST).app (stdSimplex.obj Z.unop) ≫
          ((joinFunctor.obj T).map (uliftYonedaEquiv.symm z) ≫ q.1)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ q.1) ((joinFunctor.map jST).naturality (uliftYonedaEquiv.symm z))

theorem cosliceHomEquiv_naturality_target {K C C' : SSet.{u}} {p : K ⟶ C} (f : C ⟶ C')
    (Y : SSet.{u}) (q : CoOverPt p Y) :
    cosliceHomEquiv (p ≫ f) Y (coOverPtPost f q)
      = cosliceHomEquiv p Y q ≫ cosliceMapTarget f := by
  apply NatTrans.ext
  funext Z
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  rw [NatTrans.comp_app_apply]
  rw [cosliceHomEquiv_app_coe (p ≫ f) Y (coOverPtPost f q) Z z]
  show (joinFunctor.obj K).map (uliftYonedaEquiv.symm z) ≫ (q.1 ≫ f)
      = ((cosliceHomEquiv p Y q).app Z z).1 ≫ f
  rw [cosliceHomEquiv_app_coe p Y q Z z]
  exact (Category.assoc _ _ _).symm


/-! ## The Leibniz join (non-flip: cone point on the LEFT, free factor on the RIGHT) -/

/-- The coslice Leibniz-join pushout-product square `jST ⋆̂ g` (cone point on the left). -/
abbrev sqLeibCo {S T A B : SSet.{u}} (jST : S ⟶ T) (g : A ⟶ B) :
    joinFunctor.PushoutObjObj jST g :=
  Functor.PushoutObjObj.ofHasPushout joinFunctor jST g

/-! ## The L4 transpose for the coslice -/

/-- The coslice projection `cosliceProj jST σ p` has the right lifting property against `g`
whenever `p` lifts against the Leibniz join `(sqLeibCo jST g).ι` (the adjoint transpose). -/
theorem hasLiftingProperty_cosliceProj
    {S T X Y A B : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ X) (p : X ⟶ Y) (g : A ⟶ B)
    (hlift : HasLiftingProperty (sqLeibCo jST g).ι p) :
    HasLiftingProperty g (cosliceProj jST σ p) := by
  refine ⟨fun {u} {w} sq => ?_⟩
  set ũ : CoOverPt σ A := (cosliceHomEquiv σ A).symm u with hũ
  set vv1 : CoOverPt (jST ≫ σ) B :=
    (cosliceHomEquiv (jST ≫ σ) B).symm (w ≫ pullback.fst _ _) with hvv1
  set vv2 : CoOverPt (σ ≫ p) B :=
    (cosliceHomEquiv (σ ≫ p) B).symm (w ≫ pullback.snd _ _) with hvv2
  have hu : cosliceHomEquiv σ A ũ = u := by rw [hũ, Equiv.apply_symm_apply]
  have hw₁ : cosliceHomEquiv (jST ≫ σ) B vv1 = w ≫ pullback.fst _ _ := by
    rw [hvv1, Equiv.apply_symm_apply]
  have hw₂ : cosliceHomEquiv (σ ≫ p) B vv2 = w ≫ pullback.snd _ _ := by
    rw [hvv2, Equiv.apply_symm_apply]
  have sqfst : u ≫ cosliceMapBase jST rfl = g ≫ w ≫ pullback.fst _ _ := by
    have h := sq.w =≫ pullback.fst (cosliceMapTarget (p := jST ≫ σ) p) (cosliceMapBase jST rfl)
    simpa only [Category.assoc, cosliceProj_fst] using h
  have sqsnd : u ≫ cosliceMapTarget p = g ≫ w ≫ pullback.snd _ _ := by
    have h := sq.w =≫ pullback.snd (cosliceMapTarget (p := jST ≫ σ) p) (cosliceMapBase jST rfl)
    simpa only [Category.assoc, cosliceProj_snd] using h
  have agreeTop : (joinFunctor.map jST).app A ≫ ũ.1 = (joinFunctor.obj S).map g ≫ vv1.1 := by
    have key : coOverPtMapBase jST A ũ = coOverPtRestrict g vv1 := by
      apply (cosliceHomEquiv (jST ≫ σ) A).injective
      rw [cosliceHomEquiv_naturality_base, ← cosliceHomEquiv_naturality_left, hu, hw₁]
      exact sqfst
    exact congrArg Subtype.val key
  have agreeInl : ũ.1 ≫ p = (joinFunctor.obj T).map g ≫ vv2.1 := by
    have key : coOverPtPost p ũ = coOverPtRestrict g vv2 := by
      apply (cosliceHomEquiv (σ ≫ p) A).injective
      rw [cosliceHomEquiv_naturality_target, ← cosliceHomEquiv_naturality_left, hu, hw₂]
      exact sqsnd
    exact congrArg Subtype.val key
  have agreeInr : vv1.1 ≫ p = (joinFunctor.map jST).app B ≫ vv2.1 := by
    have key : (coOverPtPost p vv1 : CoOverPt ((jST ≫ σ) ≫ p) B) = coOverPtMapBase jST B vv2 := by
      apply (cosliceHomEquiv ((jST ≫ σ) ≫ p) B).injective
      have a : cosliceHomEquiv ((jST ≫ σ) ≫ p) B (coOverPtPost p vv1)
          = cosliceHomEquiv (jST ≫ σ) B vv1 ≫ cosliceMapTarget p :=
        cosliceHomEquiv_naturality_target p B vv1
      have b : cosliceHomEquiv ((jST ≫ σ) ≫ p) B (coOverPtMapBase jST B vv2)
          = cosliceHomEquiv (σ ≫ p) B vv2 ≫ cosliceMapBase jST rfl :=
        cosliceHomEquiv_naturality_base jST B vv2
      rw [a, b]
      simp only [hw₁, hw₂, Category.assoc]
      exact congrArg (w ≫ ·) pullback.condition
    exact congrArg Subtype.val key
  have leibcomm :
      (sqLeibCo jST g).isPushout.desc ũ.1 vv1.1 agreeTop ≫ p = (sqLeibCo jST g).ι ≫ vv2.1 := by
    apply (sqLeibCo jST g).isPushout.hom_ext
    · rw [(sqLeibCo jST g).isPushout.inl_desc_assoc, ← Category.assoc, (sqLeibCo jST g).inl_ι]
      exact agreeInl
    · rw [(sqLeibCo jST g).isPushout.inr_desc_assoc, ← Category.assoc, (sqLeibCo jST g).inr_ι]
      exact agreeInr
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ := (hlift.sq_hasLift ⟨leibcomm⟩).exists_lift.some
  have inlι : (joinFunctor.obj T).map g = (sqLeibCo jST g).inl ≫ (sqLeibCo jST g).ι :=
    (sqLeibCo jST g).inl_ι.symm
  have inrι : (joinFunctor.map jST).app B = (sqLeibCo jST g).inr ≫ (sqLeibCo jST g).ι :=
    (sqLeibCo jST g).inr_ι.symm
  have hgℓ : (joinFunctor.obj T).map g ≫ ℓ = ũ.1 := by
    rw [inlι]
    show (sqLeibCo jST g).inl ≫ ((sqLeibCo jST g).ι ≫ ℓ) = ũ.1
    rw [hℓ₁]
    exact (sqLeibCo jST g).isPushout.inl_desc ũ.1 vv1.1 agreeTop
  have hℓr : (joinFunctor.map jST).app B ≫ ℓ = vv1.1 := by
    rw [inrι]
    show (sqLeibCo jST g).inr ≫ ((sqLeibCo jST g).ι ≫ ℓ) = vv1.1
    rw [hℓ₁]
    exact (sqLeibCo jST g).isPushout.inr_desc ũ.1 vv1.1 agreeTop
  have hbase : joinInl' T B ≫ ℓ = σ := by
    rw [← joinInl'_naturality_right g T]
    exact (congrArg (joinInl' T A ≫ ·) hgℓ).trans ũ.2
  refine ⟨⟨cosliceHomEquiv σ B ⟨ℓ, hbase⟩, ?_, ?_⟩⟩
  · rw [cosliceHomEquiv_naturality_left,
      show coOverPtRestrict g (⟨ℓ, hbase⟩ : CoOverPt σ B) = ũ from Subtype.ext hgℓ, hu]
  · apply pullback.hom_ext
    · rw [Category.assoc, cosliceProj_fst, ← cosliceHomEquiv_naturality_base,
        show coOverPtMapBase jST B (⟨ℓ, hbase⟩ : CoOverPt σ B) = vv1 from Subtype.ext hℓr, hw₁]
    · rw [Category.assoc, cosliceProj_snd, ← cosliceHomEquiv_naturality_target,
        show coOverPtPost p (⟨ℓ, hbase⟩ : CoOverPt σ B) = vv2 from Subtype.ext hℓ₂, hw₂]


/-! ## The coslice relative projection is a LEFT fibration -/

/-- The coslice relative projection `cosliceProj jST σ p` is a left fibration, given the Joyal
pushout-product hypothesis `joyal`. -/
theorem leftFibrations_cosliceProj
    {S T X Y : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ X) (p : X ⟶ Y) [hp : InnerFibration p]
    (joyal : ∀ ⦃A B : SSet.{u}⦄ (g : A ⟶ B), leftAnodyneExtensions g →
        innerAnodyneExtensions (sqLeibCo jST g).ι) :
    leftFibrations (cosliceProj jST σ p) := by
  intro A B g hg
  obtain ⟨i, hn⟩ := hg
  have hla : leftAnodyneExtensions Λ[_ + 1, i].ι := leftAnodyneExtensions.horn_ι hn
  have hinner : innerAnodyneExtensions (sqLeibCo jST Λ[_ + 1, i].ι).ι := joyal _ hla
  exact hasLiftingProperty_cosliceProj jST σ p _ (hinner p hp.mem)

end
end SSet
end
