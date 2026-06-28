import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Slice
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinCore

/-!
# Leibniz-join saturation: stability under coproducts (right slot)

Proves `leibImgR_coproducts`, the coproduct-stability instance for a fixed monomorphism `j` and
the last of the four second-slot saturation facts feeding the Joyal pushout-product. A coproduct
is a wide pushout over the initial object, the join functor preserves it as a connected colimit,
and the reusable cube lemma `isPushout_cobase_of_widePushout` repackages a wide pushout of arrows
over an isomorphism centre as the cobase change of the coproduct of the leaves, reducing the
instance to a single per-family cobase square (`leibImgR_coproducts_of_cobaseSquare`). Also proves
the right unit law `joinBotIso' : K ⋆ ⊥ ≅ K`. Part of the Joyal pushout-product.
-/

open CategoryTheory Simplicial Limits MorphismProperty SmallObject
open CategoryTheory.Limits.WidePushoutShape

/-! ## PIECE 2(f) — ABSTRACT CUBE / cobase-collapse lemmas (join-free, reusable).
These close the residual `sqHyp` once instantiated: a wide-pushout colimit of arrows over an
ISO-center arrow is the cobase change of the coproduct of the leaf arrows. -/

universe u v

namespace CubeLemma
variable {C : Type v} [Category.{u} C] {I : Type u}

/-- `Sigma.map` of a constant family of isos is an iso. -/
instance sigmaMap_const_iso {Xc Yc : C} (mc : Xc ⟶ Yc) [IsIso mc]
    [HasCoproduct (fun _ : I => Xc)] [HasCoproduct (fun _ : I => Yc)] :
    IsIso (Limits.Sigma.map (fun _ : I => mc)) := by
  refine ⟨Limits.Sigma.map (fun _ : I => inv mc), ?_, ?_⟩ <;>
    · apply Limits.Sigma.hom_ext; intro a; simp

/-- The wide-pushout `∃!` universal property read off any `IsColimit` of a
`WidePushoutShape`-diagram (legs `c.ι.app (some a)`, center `c.ι.app none`). -/
theorem widePushout_universal_of_isColimit
    {D : CategoryTheory.Limits.WidePushoutShape I ⥤ C}
    {c : Cocone D} (hc : IsColimit c) {Z : C}
    (u : ∀ a, D.obj (Option.some a) ⟶ Z) (w : D.obj Option.none ⟶ Z)
    (hw : ∀ a, D.map (WidePushoutShape.Hom.init a) ≫ u a = w) :
    ∃! m : c.pt ⟶ Z, (∀ a, c.ι.app (Option.some a) ≫ m = u a) ∧ c.ι.app Option.none ≫ m = w := by
  refine ⟨hc.desc (WidePushoutShape.mkCocone w u (fun a => hw a)), ⟨fun a => ?_, ?_⟩, ?_⟩
  · exact hc.fac (WidePushoutShape.mkCocone w u (fun a => hw a)) (Option.some a)
  · exact hc.fac (WidePushoutShape.mkCocone w u (fun a => hw a)) Option.none
  · rintro m ⟨hl, hr⟩
    apply hc.hom_ext
    intro j
    cases j with
    | none =>
      rw [hr]
      exact (hc.fac (WidePushoutShape.mkCocone w u (fun a => hw a)) Option.none).symm
    | some a =>
      rw [hl a]
      exact (hc.fac (WidePushoutShape.mkCocone w u (fun a => hw a)) (Option.some a)).symm

/-- **Fold-form pushout from the wide-pushout universal property** (no `WidePushoutShape`):
`Sigma.desc ℓ` is the cobase change of `Sigma.desc (𝟙 Xc)` along `Sigma.map dx`. -/
theorem isPushout_fold_of_universal
    {Xc : C} {Xa : I → C} (dx : ∀ a, Xc ⟶ Xa a)
    [HasCoproduct (fun _ : I => Xc)] [HasCoproduct Xa]
    {P : C} (g : Xc ⟶ P) (ℓ : ∀ a, Xa a ⟶ P)
    (hcond : ∀ a, dx a ≫ ℓ a = g)
    (huniv : ∀ {Z : C} (u : ∀ a, Xa a ⟶ Z) (w : Xc ⟶ Z), (∀ a, dx a ≫ u a = w) →
       ∃! m : P ⟶ Z, (∀ a, ℓ a ≫ m = u a) ∧ g ≫ m = w) :
    IsPushout (Limits.Sigma.map dx) (Limits.Sigma.desc (fun _ : I => 𝟙 Xc))
      (Limits.Sigma.desc ℓ) g := by
  have Wcond : ∀ (s : PushoutCocone (Limits.Sigma.map dx) (Limits.Sigma.desc (fun _ : I => 𝟙 Xc))),
      ∀ a, dx a ≫ (Limits.Sigma.ι Xa a ≫ s.inl) = s.inr := by
    intro s a
    have h := congrArg (fun t => Limits.Sigma.ι (fun _ : I => Xc) a ≫ t) s.condition
    simp only [← Category.assoc, Limits.Sigma.ι_map, Limits.Sigma.ι_desc] at h
    simpa [Category.assoc] using h
  refine IsPushout.of_isColimit (c := PushoutCocone.mk (Limits.Sigma.desc ℓ) g ?_) ?_
  · apply Limits.Sigma.hom_ext; intro a
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
      ← Category.assoc, Limits.Sigma.ι_desc, Category.id_comp]
    exact hcond a
  · refine PushoutCocone.IsColimit.mk _
      (fun s => (huniv _ _ (Wcond s)).choose) (fun s => ?_) (fun s => ?_) (fun s m hl hr => ?_)
    · apply Limits.Sigma.hom_ext; intro a
      rw [Limits.Sigma.ι_desc_assoc]
      exact (huniv _ _ (Wcond s)).choose_spec.1.1 a
    · exact (huniv _ _ (Wcond s)).choose_spec.1.2
    · refine (huniv _ _ (Wcond s)).choose_spec.2 m ⟨fun a => ?_, hr⟩
      rw [← Limits.Sigma.ι_desc ℓ a, Category.assoc, hl]

/-- **Abstract cube / cobase-collapse lemma.** Given the domain (`hD`) and codomain (`hC`)
wide-pushouts in fold form, leaf arrows `ma`, an **iso** center `mc`, per-leg naturality `hnat`,
and an induced `L` (characterized by `hLg`, `hLα`), the square `IsPushout α (Sigma.map ma) L β`
holds — i.e. `L` is the cobase change of `⨿ ma`. -/
theorem isPushout_cobase_of_widePushout
    {Xc Yc : C} (mc : Xc ⟶ Yc) [IsIso mc]
    {Xa Ya : I → C} (ma : ∀ a, Xa a ⟶ Ya a)
    (dx : ∀ a, Xc ⟶ Xa a) (dy : ∀ a, Yc ⟶ Ya a)
    (hnat : ∀ a, dx a ≫ ma a = mc ≫ dy a)
    [HasCoproduct (fun _ : I => Xc)] [HasCoproduct (fun _ : I => Yc)]
    [HasCoproduct Xa] [HasCoproduct Ya]
    {P Q : C} {gX : Xc ⟶ P} {α : (∐ Xa) ⟶ P} {gY : Yc ⟶ Q} {β : (∐ Ya) ⟶ Q}
    (hD : IsPushout (Limits.Sigma.map dx) (Limits.Sigma.desc (fun _ : I => 𝟙 Xc)) α gX)
    (hC : IsPushout (Limits.Sigma.map dy) (Limits.Sigma.desc (fun _ : I => 𝟙 Yc)) β gY)
    {L : P ⟶ Q} (hLg : gX ≫ L = mc ≫ gY) (hLα : α ≫ L = Limits.Sigma.map ma ≫ β) :
    IsPushout α (Limits.Sigma.map ma) L β := by
  have hfoldNat :
      Limits.Sigma.map (fun _ : I => mc) ≫ Limits.Sigma.desc (fun _ : I => 𝟙 Yc)
        = Limits.Sigma.desc (fun _ : I => 𝟙 Xc) ≫ mc := by
    apply Limits.Sigma.hom_ext; intro a
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
      Category.comp_id, Limits.Sigma.ι_desc_assoc, Category.id_comp]
  have hleftIso : IsPushout (Limits.Sigma.map (fun _ : I => mc))
      (Limits.Sigma.desc (fun _ : I => 𝟙 Xc)) (Limits.Sigma.desc (fun _ : I => 𝟙 Yc)) mc :=
    IsPushout.of_horiz_isIso ⟨hfoldNat⟩
  have hpaste := hleftIso.paste_horiz hC
  have hTop : Limits.Sigma.map (fun _ : I => mc) ≫ Limits.Sigma.map dy
      = Limits.Sigma.map dx ≫ Limits.Sigma.map ma := by
    apply Limits.Sigma.hom_ext; intro a; simp [reassoc_of% (hnat a)]
  have hBot : mc ≫ gY = gX ≫ L := hLg.symm
  rw [hTop, hBot] at hpaste
  exact (hpaste.of_left hLα.symm hD).flip

end CubeLemma

namespace SSet
noncomputable section

namespace Coprod

/-! ## PIECE 1 — the right unit law `K ⋆ ⊥ ≅ K`. -/

/-- `joinInl' K ⊥` is an iso, mirroring `joinInr_initial_isIso`. -/
instance joinInl'_initial_isIso (K : SSet.{u}) : IsIso (joinInl' K (⊥_ SSet.{u})) := by
  unfold joinInl'
  apply Functor.map_isIso

/-- The RIGHT unit law `K ⋆ ⊥ ≅ K` (dual of `joinBotIso : ⊥ ⋆ K ≅ K`).
Note `K ⋆ ⊥ = (joinFunctor.obj K).obj ⊥`. -/
def joinBotIso' (K : SSet.{u}) : K ⋆ (⊥_ SSet.{u}) ≅ K :=
  (asIso (joinInl' K (⊥_ SSet.{u}))).symm

/-! ## `leibImgR` and the corner bridge — imported from `SatiCore`
(`leibImgR`, `joinSq`, `joinSq_ι`, `pushoutObjObj_ι_arrowIso`, `Lj`, `cornerIso` are the
identical definitions shared with the core; removed here to avoid duplicate declarations). -/

lemma Lj_obj_arrow {S T A B : SSet.{u}} (j : S ⟶ T) (i : A ⟶ B) :
    (Lj j).obj (Arrow.mk i) = Arrow.mk ((Functor.PushoutObjObj.ofHasPushout joinFunctor j i).ι) :=
  rfl

/-! ## PIECE 2(a) — RespectsIso for `leibImgR j`. -/

/-- Transports an arrow-iso `i ≅ i'` to an arrow-iso of Leibniz joins `j ⋆̂ i ≅ j ⋆̂ i'`. -/
def leibImgR_arrowIso {S T A B A' B' : SSet.{u}} (j : S ⟶ T) (i : A ⟶ B) (i' : A' ⟶ B')
    (e : Arrow.mk i ≅ Arrow.mk i') :
    Arrow.mk (leibnizJoin j i) ≅ Arrow.mk (leibnizJoin j i') :=
  cornerIso j i ≪≫ (eqToIso (Lj_obj_arrow j i)).symm ≪≫ (Lj j).mapIso e ≪≫
    eqToIso (Lj_obj_arrow j i') ≪≫ (cornerIso j i').symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance leibImgR_respectsIso {S T : SSet.{u}} (j : S ⟶ T) : (leibImgR j).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    have e' : Arrow.mk (e.hom ≫ f) ≅ Arrow.mk f := Arrow.isoMk e (Iso.refl _) (by simp)
    exact (innerAnodyneExtensions.arrow_mk_iso_iff (leibImgR_arrowIso j (e.hom ≫ f) f e')).2 hf
  · intro X Y Z e f hf
    have e' : Arrow.mk (f ≫ e.hom) ≅ Arrow.mk f := Arrow.isoMk (Iso.refl _) e.symm (by simp)
    exact (innerAnodyneExtensions.arrow_mk_iso_iff (leibImgR_arrowIso j (f ≫ e.hom) f e')).2 hf

/-! ## PIECE 2(b) — center collapse: `leibnizJoin f (𝟙 C)` is an iso. -/

lemma leibnizJoin_id_right_isIso {A B C : SSet.{u}} (f : A ⟶ B) :
    IsIso (leibnizJoin f (𝟙 C)) := by
  have hg : joinMap (𝟙 A) (𝟙 C) = 𝟙 (A ⋆ C) := by
    rw [joinMap_id_left]; exact (joinFunctor.obj A).map_id C
  haveI : IsIso (joinMap (𝟙 A) (𝟙 C)) := by rw [hg]; infer_instance
  haveI : IsIso (pushout.inl (joinMap f (𝟙 C)) (joinMap (𝟙 A) (𝟙 C))) :=
    pushout_inl_iso_of_right_iso _ _
  have hcomp : pushout.inl (joinMap f (𝟙 C)) (joinMap (𝟙 A) (𝟙 C)) ≫ leibnizJoin f (𝟙 C)
      = 𝟙 (B ⋆ C) := by
    rw [leibnizJoin, pushout.inl_desc, joinMap_id_left]; exact (joinFunctor.obj B).map_id C
  haveI : IsIso (pushout.inl (joinMap f (𝟙 C)) (joinMap (𝟙 A) (𝟙 C)) ≫ leibnizJoin f (𝟙 C)) := by
    rw [hcomp]; infer_instance
  exact IsIso.of_isIso_comp_left
    (pushout.inl (joinMap f (𝟙 C)) (joinMap (𝟙 A) (𝟙 C))) (leibnizJoin f (𝟙 C))

/-! ## PIECE 2(c) — coproduct of corners is inner-anodyne. -/

lemma sigmaMap_leibnizJoin_innerAnodyne {S T : SSet.{u}} (j : S ⟶ T) {I : Type u}
    (A B : I → SSet.{u}) (fam : ∀ a, A a ⟶ B a)
    (hfam : ∀ a, innerAnodyneExtensions (leibnizJoin j (fam a))) :
    innerAnodyneExtensions (Limits.Sigma.map (fun a => leibnizJoin j (fam a))) :=
  MorphismProperty.colimMap _ (fun ⟨a⟩ => hfam a)

/-! ## PIECE 2(d) — REDUCTION: Coproducts instance from the per-family cobase-collapse square.
Mirrors the repo's `satI_of_two_instances`: the entire instance now depends only on `sqHyp`. -/

theorem leibImgR_coproducts_of_cobaseSquare {S T : SSet.{u}} (j : S ⟶ T)
    (sqHyp : ∀ (I : Type u) (A B : I → SSet.{u}) (fam : ∀ a, A a ⟶ B a),
      ∃ (α : (∐ fun a => pushout (joinMap j (𝟙 (A a))) (joinMap (𝟙 S) (fam a))) ⟶
          pushout (joinMap j (𝟙 (∐ A))) (joinMap (𝟙 S) (Limits.Sigma.map fam)))
        (β : (∐ fun a => T ⋆ B a) ⟶ T ⋆ (∐ B)),
        IsPushout α (Limits.Sigma.map (fun a => leibnizJoin j (fam a)))
          (leibnizJoin j (Limits.Sigma.map fam)) β) :
    IsStableUnderCoproducts.{u} (leibImgR j) := by
  constructor
  intro I
  apply IsStableUnderCoproductsOfShape.mk
  intro A B hA hB fam hfam
  show innerAnodyneExtensions (leibnizJoin j (Limits.Sigma.map fam))
  obtain ⟨α, β, sq⟩ := sqHyp I A B fam
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := innerAnodyneExtensions) sq
    (sigmaMap_leibnizJoin_innerAnodyne j A B fam hfam)

/-! ## PIECE 2(e) — CORNERSTONE for the open square: coproduct = wide pushout over ⊥. -/

/-- The coproduct cocone viewed as a cocone over the wide span with initial center. -/
noncomputable def coproductCocone {J : Type u} (B : J → SSet.{u}) (I0 : SSet.{u})
    (hI0 : IsInitial I0) :
    Cocone (wideSpan I0 B (fun a => hI0.to (B a))) :=
  WidePushoutShape.mkCocone (hI0.to (∐ B)) (fun a => Sigma.ι B a) (fun _ => hI0.hom_ext _ _)

/-- A wide pushout over the **initial** object is the coproduct. -/
noncomputable def coproductIsWidePushoutOverInitial {J : Type u} (B : J → SSet.{u})
    (I0 : SSet.{u}) (hI0 : IsInitial I0) :
    IsColimit (coproductCocone B I0 hI0) where
  desc s := Sigma.desc (fun a => s.ι.app (Option.some a))
  fac s j := by
    cases j with
    | none => exact hI0.hom_ext _ _
    | some a => exact Sigma.ι_desc _ a
  uniq s m hm := by
    apply Limits.Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    exact hm (Option.some a)

/-- The `(T ⋆ -)` connected-colimit transport the square construction runs on:
`T ⋆ (∐ B)` is the wide pushout of `T ⋆ B a` over `T ⋆ ⊥`. -/
noncomputable def join_coproduct_isWidePushout (T : SSet.{u}) {I : Type u} (B : I → SSet.{u}) :
    IsColimit ((joinFunctor.obj T).mapCocone
      (coproductCocone B (⊥_ SSet.{u}) initialIsInitial)) := by
  haveI : PreservesColimitsOfShape (WidePushoutShape I) (joinFunctor.obj T) :=
    joinFunctor_obj_preservesConnectedColimits_of_tensorLeft (WidePushoutShape I) T
  exact isColimitOfPreserves (joinFunctor.obj T)
    (coproductIsWidePushoutOverInitial B (⊥_ SSet.{u}) initialIsInitial)

/-- The cocone `(T ⋆ -)` of the coproduct presentation, named for the corner construction. -/
noncomputable abbrev joinCoprodCocone (T : SSet.{u}) {I : Type u} (B : I → SSet.{u}) :
    Cocone (WidePushoutShape.wideSpan (⊥_ SSet.{u}) B (fun a => initial.to (B a)) ⋙
      joinFunctor.obj T) :=
  (joinFunctor.obj T).mapCocone (coproductCocone B (⊥_ SSet.{u}) initialIsInitial)

/-- END-TO-END CODOMAIN CORNER: `T ⋆ (∐ B)` in **fold form** — the cobase change of
`Sigma.desc 𝟙` along `Sigma.map (T ⋆ (⊥ → B a))`, i.e. the `hC` input to the cube lemma.
This demonstrates the abstract pipeline (transport → universal property → fold) connects on
the join. -/
theorem joinCoproduct_fold (T : SSet.{u}) {I : Type u} (B : I → SSet.{u}) :
    IsPushout
      (Limits.Sigma.map (fun a => (joinFunctor.obj T).map (initial.to (B a))))
      (Limits.Sigma.desc (fun _ : I => 𝟙 ((joinFunctor.obj T).obj (⊥_ SSet.{u}))))
      (Limits.Sigma.desc (fun a => (joinCoprodCocone T B).ι.app (Option.some a)))
      ((joinCoprodCocone T B).ι.app Option.none) :=
  CubeLemma.isPushout_fold_of_universal
    (fun a => (joinFunctor.obj T).map (initial.to (B a)))
    ((joinCoprodCocone T B).ι.app Option.none)
    (fun a => (joinCoprodCocone T B).ι.app (Option.some a))
    (fun a => (joinCoprodCocone T B).w (WidePushoutShape.Hom.init a))
    (fun {_Z} u w hw =>
      CubeLemma.widePushout_universal_of_isColimit (join_coproduct_isWidePushout T B) u w hw)

/-! ## PIECE 2(g) — the cube lemma's leg-map `dx` and naturality `hnat`, on the join.
`cornerLeg j i` is the leibniz-corner functoriality
`dom(leibnizJoin j (𝟙 ⊥)) ⟶ dom(leibnizJoin j i)`;
`cornerLeg_naturality` is exactly the cube lemma's `hnat` (with `dy = joinMap (𝟙 T) (init Y)`,
which equals `joinCoproduct_fold`'s leg map by `joinMap_id_left`). -/

variable {S T : SSet.{u}}

/-- The domain leg-map `dom(leibnizJoin j (𝟙 ⊥)) ⟶ dom(leibnizJoin j i)`. -/
def cornerLeg (j : S ⟶ T) {X Y : SSet.{u}} (i : X ⟶ Y) :
    pushout (joinMap j (𝟙 (⊥_ SSet.{u}))) (joinMap (𝟙 S) (𝟙 (⊥_ SSet.{u}))) ⟶
      pushout (joinMap j (𝟙 X)) (joinMap (𝟙 S) i) :=
  pushout.map _ _ _ _
    (joinMap (𝟙 T) (initial.to X)) (joinMap (𝟙 S) (initial.to Y)) (joinMap (𝟙 S) (initial.to X))
    (joinMap_comm j (initial.to X))
    (by rw [← joinMap_comp_right, ← joinMap_comp_right, Category.id_comp,
        initialIsInitial.hom_ext (initial.to X ≫ i) (initial.to Y)])

/-- The cube lemma's `hnat`: naturality of `leibnizJoin j (-)` along `(𝟙 ⊥) ⟶ i`. -/
lemma cornerLeg_naturality (j : S ⟶ T) {X Y : SSet.{u}} (i : X ⟶ Y) :
    cornerLeg j i ≫ leibnizJoin j i
      = leibnizJoin j (𝟙 (⊥_ SSet.{u})) ≫ joinMap (𝟙 T) (initial.to Y) := by
  apply pushout.hom_ext
  · rw [cornerLeg, ← Category.assoc, pushout.inl_desc, Category.assoc, leibnizJoin,
      pushout.inl_desc, ← joinMap_comp_right,
      initialIsInitial.hom_ext (initial.to X ≫ i) (initial.to Y),
      ← Category.assoc, leibnizJoin, pushout.inl_desc, ← joinMap_comp_right, Category.id_comp]
  · rw [cornerLeg, ← Category.assoc, pushout.inr_desc, Category.assoc, leibnizJoin,
      pushout.inr_desc, ← Category.assoc, leibnizJoin, pushout.inr_desc,
      joinMap_comm j (initial.to Y)]

/-- General leibniz-corner functoriality along an arrow map `(p, q) : i ⟶ i'`. -/
def cornerMap (j : S ⟶ T) {X Y X' Y' : SSet.{u}} (i : X ⟶ Y) (i' : X' ⟶ Y')
    (p : X ⟶ X') (q : Y ⟶ Y') (hpq : p ≫ i' = i ≫ q) :
    pushout (joinMap j (𝟙 X)) (joinMap (𝟙 S) i) ⟶
      pushout (joinMap j (𝟙 X')) (joinMap (𝟙 S) i') :=
  pushout.map _ _ _ _ (joinMap (𝟙 T) p) (joinMap (𝟙 S) q) (joinMap (𝟙 S) p)
    (joinMap_comm j p) (by rw [← joinMap_comp_right, ← joinMap_comp_right, hpq])

@[reassoc] lemma cornerMap_inl (j : S ⟶ T) {X Y X' Y' : SSet.{u}} (i : X ⟶ Y) (i' : X' ⟶ Y')
    (p : X ⟶ X') (q : Y ⟶ Y') (hpq : p ≫ i' = i ≫ q) :
    pushout.inl _ _ ≫ cornerMap j i i' p q hpq = joinMap (𝟙 T) p ≫ pushout.inl _ _ := by
  rw [cornerMap, pushout.inl_desc]

@[reassoc] lemma cornerMap_inr (j : S ⟶ T) {X Y X' Y' : SSet.{u}} (i : X ⟶ Y) (i' : X' ⟶ Y')
    (p : X ⟶ X') (q : Y ⟶ Y') (hpq : p ≫ i' = i ≫ q) :
    pushout.inr _ _ ≫ cornerMap j i i' p q hpq = joinMap (𝟙 S) q ≫ pushout.inr _ _ := by
  rw [cornerMap, pushout.inr_desc]

@[reassoc] lemma cornerLeg_inl (j : S ⟶ T) {X Y : SSet.{u}} (i : X ⟶ Y) :
    pushout.inl _ _ ≫ cornerLeg j i = joinMap (𝟙 T) (initial.to X) ≫ pushout.inl _ _ := by
  rw [cornerLeg, pushout.inl_desc]

@[reassoc] lemma cornerLeg_inr (j : S ⟶ T) {X Y : SSet.{u}} (i : X ⟶ Y) :
    pushout.inr _ _ ≫ cornerLeg j i = joinMap (𝟙 S) (initial.to Y) ≫ pushout.inr _ _ := by
  rw [cornerLeg, pushout.inr_desc]

/-- Naturality of `leibnizJoin j (-)` along a general arrow map `(p, q)`. -/
lemma cornerMap_naturality (j : S ⟶ T) {X Y X' Y' : SSet.{u}} (i : X ⟶ Y) (i' : X' ⟶ Y')
    (p : X ⟶ X') (q : Y ⟶ Y') (hpq : p ≫ i' = i ≫ q) :
    cornerMap j i i' p q hpq ≫ leibnizJoin j i' = leibnizJoin j i ≫ joinMap (𝟙 T) q := by
  apply pushout.hom_ext
  · rw [cornerMap_inl_assoc, leibnizJoin, pushout.inl_desc, ← joinMap_comp_right, hpq,
      ← Category.assoc, leibnizJoin, pushout.inl_desc, ← joinMap_comp_right]
  · rw [cornerMap_inr_assoc, leibnizJoin, pushout.inr_desc, ← Category.assoc, leibnizJoin,
      pushout.inr_desc, joinMap_comm j q]

/-! ## PIECE 2(h) — the domain corner `hD` and the closed instance. -/

variable {I : Type u}

/-- Center inclusion `Pc ⟶ P` of the domain corner (`gX`). -/
abbrev domCenterIncl (j : S ⟶ T) (A B : I → SSet.{u}) (fam : ∀ a, A a ⟶ B a) :
    pushout (joinMap j (𝟙 (⊥_ SSet.{u}))) (joinMap (𝟙 S) (𝟙 (⊥_ SSet.{u}))) ⟶
      pushout (joinMap j (𝟙 (∐ A))) (joinMap (𝟙 S) (Limits.Sigma.map fam)) :=
  cornerLeg j (Limits.Sigma.map fam)

/-- Leg inclusion `Pa a ⟶ P` of the domain corner (`ℓ a`). -/
abbrev domLegIncl (j : S ⟶ T) (A B : I → SSet.{u}) (fam : ∀ a, A a ⟶ B a) (a : I) :
    pushout (joinMap j (𝟙 (A a))) (joinMap (𝟙 S) (fam a)) ⟶
      pushout (joinMap j (𝟙 (∐ A))) (joinMap (𝟙 S) (Limits.Sigma.map fam)) :=
  cornerMap j (fam a) (Limits.Sigma.map fam) (Limits.Sigma.ι A a) (Limits.Sigma.ι B a)
    (Limits.Sigma.ι_map fam a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The wide-pushout universal property of the domain corner `P`, assembled from the three
sub-corner wide pushouts `T ⋆ ∐A`, `S ⋆ ∐B`, `S ⋆ ∐A` glued through `P`'s binary pushout. -/
theorem domCorner_huniv (j : S ⟶ T) (A B : I → SSet.{u}) (fam : ∀ a, A a ⟶ B a)
    {Z : SSet.{u}}
    (u : ∀ a, pushout (joinMap j (𝟙 (A a))) (joinMap (𝟙 S) (fam a)) ⟶ Z)
    (w : pushout (joinMap j (𝟙 (⊥_ SSet.{u}))) (joinMap (𝟙 S) (𝟙 (⊥_ SSet.{u}))) ⟶ Z)
    (hw : ∀ a, cornerLeg j (fam a) ≫ u a = w) :
    ∃! m : pushout (joinMap j (𝟙 (∐ A))) (joinMap (𝟙 S) (Limits.Sigma.map fam)) ⟶ Z,
      (∀ a, domLegIncl j A B fam a ≫ m = u a) ∧ domCenterIncl j A B fam ≫ m = w := by
  -- the three sub-corner universal properties
  have UPT := fun (uT : ∀ a, (joinFunctor.obj T).obj (A a) ⟶ Z)
      (wT : (joinFunctor.obj T).obj (⊥_ SSet.{u}) ⟶ Z) hwT =>
    CubeLemma.widePushout_universal_of_isColimit (join_coproduct_isWidePushout T A) uT wT hwT
  have UPSB := fun (uS : ∀ a, (joinFunctor.obj S).obj (B a) ⟶ Z)
      (wS : (joinFunctor.obj S).obj (⊥_ SSet.{u}) ⟶ Z) hwS =>
    CubeLemma.widePushout_universal_of_isColimit (join_coproduct_isWidePushout S B) uS wS hwS
  -- restrictions of `u`, `w`
  set uT : ∀ a, (joinFunctor.obj T).obj (A a) ⟶ Z :=
    fun a => pushout.inl _ _ ≫ u a with huT
  set uS : ∀ a, (joinFunctor.obj S).obj (B a) ⟶ Z :=
    fun a => pushout.inr _ _ ≫ u a with huS
  set wT : (joinFunctor.obj T).obj (⊥_ SSet.{u}) ⟶ Z := pushout.inl _ _ ≫ w with hwTdef
  set wS : (joinFunctor.obj S).obj (⊥_ SSet.{u}) ⟶ Z := pushout.inr _ _ ≫ w with hwSdef
  have hwT : ∀ a, (joinFunctor.obj T).map (initial.to (A a)) ≫ uT a = wT := by
    intro a
    rw [huT, hwTdef, ← hw a, ← Category.assoc, ← joinMap_id_left]
    rw [show joinMap (𝟙 T) (initial.to (A a)) ≫ pushout.inl (joinMap j (𝟙 (A a)))
          (joinMap (𝟙 S) (fam a)) = pushout.inl _ _ ≫ cornerLeg j (fam a) from ?_]
    · rw [Category.assoc]
    · rw [cornerLeg, pushout.inl_desc]
  have hwS : ∀ a, (joinFunctor.obj S).map (initial.to (B a)) ≫ uS a = wS := by
    intro a
    rw [huS, hwSdef, ← hw a, ← Category.assoc, ← joinMap_id_left]
    rw [show joinMap (𝟙 S) (initial.to (B a)) ≫ pushout.inr (joinMap j (𝟙 (A a)))
          (joinMap (𝟙 S) (fam a)) = pushout.inr _ _ ≫ cornerLeg j (fam a) from ?_]
    · rw [Category.assoc]
    · rw [cornerLeg, pushout.inr_desc]
  set mT := (UPT uT wT hwT).choose with hmT
  set mS := (UPSB uS wS hwS).choose with hmS
  -- leg conditions of `mT`, `mS`, rewritten through the explicit join legs
  have hclegT : ∀ a, ((joinFunctor.obj T).mapCocone
      (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app (Option.some a)
        = joinMap (𝟙 T) (Limits.Sigma.ι A a) := fun a => by
    show (joinFunctor.obj T).map (Limits.Sigma.ι A a) = _; rw [joinMap_id_left]
  have hclegS : ∀ a, ((joinFunctor.obj S).mapCocone
      (coproductCocone B (⊥_ SSet.{u}) initialIsInitial)).ι.app (Option.some a)
        = joinMap (𝟙 S) (Limits.Sigma.ι B a) := fun a => by
    show (joinFunctor.obj S).map (Limits.Sigma.ι B a) = _; rw [joinMap_id_left]
  have hmT1 : ∀ a, joinMap (𝟙 T) (Limits.Sigma.ι A a) ≫ mT = uT a := fun a => by
    rw [← hclegT a]; exact (UPT uT wT hwT).choose_spec.1.1 a
  have hmS1 : ∀ a, joinMap (𝟙 S) (Limits.Sigma.ι B a) ≫ mS = uS a := fun a => by
    rw [← hclegS a]; exact (UPSB uS wS hwS).choose_spec.1.1 a
  have hcenterT : ((joinFunctor.obj T).mapCocone
      (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app Option.none
        = joinMap (𝟙 T) (initial.to (∐ A)) := by
    show (joinFunctor.obj T).map (initial.to (∐ A)) = _; rw [joinMap_id_left]
  have hcenterS : ((joinFunctor.obj S).mapCocone
      (coproductCocone B (⊥_ SSet.{u}) initialIsInitial)).ι.app Option.none
        = joinMap (𝟙 S) (initial.to (∐ B)) := by
    show (joinFunctor.obj S).map (initial.to (∐ B)) = _; rw [joinMap_id_left]
  have hmT2 : joinMap (𝟙 T) (initial.to (∐ A)) ≫ mT = wT := by
    rw [← hcenterT]; exact (UPT uT wT hwT).choose_spec.1.2
  have hmS2 : joinMap (𝟙 S) (initial.to (∐ B)) ≫ mS = wS := by
    rw [← hcenterS]; exact (UPSB uS wS hwS).choose_spec.1.2
  -- legs/center of the `S ⋆ ∐A` cocone (for the agreement step)
  have hclegSA : ∀ a, ((joinFunctor.obj S).mapCocone
      (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app (Option.some a)
        = joinMap (𝟙 S) (Limits.Sigma.ι A a) := fun a => by
    show (joinFunctor.obj S).map (Limits.Sigma.ι A a) = _; rw [joinMap_id_left]
  have hcenterSA : ((joinFunctor.obj S).mapCocone
      (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app Option.none
        = joinMap (𝟙 S) (initial.to (∐ A)) := by
    show (joinFunctor.obj S).map (initial.to (∐ A)) = _; rw [joinMap_id_left]
  -- `Pa a` and `Pc` pushout conditions, transported to `Z`
  have hPa : ∀ a, joinMap j (𝟙 (A a)) ≫ uT a = joinMap (𝟙 S) (fam a) ≫ uS a := fun a => by
    show joinMap j (𝟙 (A a)) ≫ pushout.inl _ _ ≫ u a
      = joinMap (𝟙 S) (fam a) ≫ pushout.inr _ _ ≫ u a
    rw [← Category.assoc, ← Category.assoc, pushout.condition]
  have hPc : joinMap j (𝟙 (⊥_ SSet.{u})) ≫ wT = joinMap (𝟙 S) (𝟙 (⊥_ SSet.{u})) ≫ wS := by
    show joinMap j (𝟙 _) ≫ pushout.inl _ _ ≫ w = joinMap (𝟙 S) (𝟙 _) ≫ pushout.inr _ _ ≫ w
    rw [← Category.assoc, ← Category.assoc, pushout.condition]
  have hid : joinMap (𝟙 S) (𝟙 (⊥_ SSet.{u})) = 𝟙 _ := by
    rw [joinMap_id_left]; exact (joinFunctor.obj S).map_id _
  -- the two legs of `P`'s binary pushout agree after `mT`, `mS`
  have hagree : joinMap j (𝟙 (∐ A)) ≫ mT = joinMap (𝟙 S) (Limits.Sigma.map fam) ≫ mS := by
    apply (join_coproduct_isWidePushout S A).hom_ext
    intro jj
    cases jj with
    | none =>
      have hL : ((joinFunctor.obj S).mapCocone
          (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app Option.none
            ≫ joinMap j (𝟙 (∐ A)) ≫ mT = joinMap j (𝟙 (⊥_ SSet.{u})) ≫ wT := by
        rw [hcenterSA, ← Category.assoc, ← joinMap_comm j (initial.to (∐ A)), Category.assoc, hmT2]
      have hR : ((joinFunctor.obj S).mapCocone
          (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app Option.none
            ≫ joinMap (𝟙 S) (Limits.Sigma.map fam) ≫ mS = wS := by
        rw [hcenterSA, ← Category.assoc, ← joinMap_comp_right,
          initialIsInitial.hom_ext (initial.to (∐ A) ≫ Limits.Sigma.map fam) (initial.to (∐ B)),
          hmS2]
      rw [hL, hR, hPc, hid]; exact Category.id_comp wS
    | some a =>
      have hL : ((joinFunctor.obj S).mapCocone
          (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app (Option.some a)
            ≫ joinMap j (𝟙 (∐ A)) ≫ mT = joinMap j (𝟙 (A a)) ≫ uT a := by
        rw [hclegSA a, ← Category.assoc, ← joinMap_comm j (Limits.Sigma.ι A a), Category.assoc,
          hmT1 a]
      have hR : ((joinFunctor.obj S).mapCocone
          (coproductCocone A (⊥_ SSet.{u}) initialIsInitial)).ι.app (Option.some a)
            ≫ joinMap (𝟙 S) (Limits.Sigma.map fam) ≫ mS = joinMap (𝟙 S) (fam a) ≫ uS a := by
        rw [hclegSA a, ← Category.assoc, ← joinMap_comp_right, Limits.Sigma.ι_map fam a,
          joinMap_comp_right, Category.assoc, hmS1 a]
      rw [hL, hR, hPa a]
  set m := pushout.desc mT mS hagree with hmdef
  refine ⟨m, ⟨fun a => ?_, ?_⟩, ?_⟩
  · -- `domLegIncl a ≫ m = u a`
    apply pushout.hom_ext
    · rw [domLegIncl, cornerMap_inl_assoc, hmdef, pushout.inl_desc]; exact hmT1 a
    · rw [domLegIncl, cornerMap_inr_assoc, hmdef, pushout.inr_desc]; exact hmS1 a
  · -- `domCenterIncl ≫ m = w`
    apply pushout.hom_ext
    · rw [domCenterIncl, cornerLeg, pushout.inl_desc_assoc, Category.assoc, hmdef,
        pushout.inl_desc, hmT2, hwTdef]
    · rw [domCenterIncl, cornerLeg, pushout.inr_desc_assoc, Category.assoc, hmdef,
        pushout.inr_desc, hmS2, hwSdef]
  · -- uniqueness
    rintro m' ⟨hl', hr'⟩
    have hinl : pushout.inl _ _ ≫ m' = mT := by
      rw [hmT]
      refine (UPT uT wT hwT).choose_spec.2 _ ⟨fun a => ?_, ?_⟩
      · rw [hclegT a]
        show joinMap (𝟙 T) (Limits.Sigma.ι A a) ≫ pushout.inl _ _ ≫ m' = pushout.inl _ _ ≫ u a
        rw [← hl' a, domLegIncl, cornerMap_inl_assoc]
      · rw [hcenterT]
        show joinMap (𝟙 T) (initial.to (∐ A)) ≫ pushout.inl _ _ ≫ m' = pushout.inl _ _ ≫ w
        rw [← hr', domCenterIncl, cornerLeg_inl_assoc]
    have hinr : pushout.inr _ _ ≫ m' = mS := by
      rw [hmS]
      refine (UPSB uS wS hwS).choose_spec.2 _ ⟨fun a => ?_, ?_⟩
      · rw [hclegS a]
        show joinMap (𝟙 S) (Limits.Sigma.ι B a) ≫ pushout.inr _ _ ≫ m' = pushout.inr _ _ ≫ u a
        rw [← hl' a, domLegIncl, cornerMap_inr_assoc]
      · rw [hcenterS]
        show joinMap (𝟙 S) (initial.to (∐ B)) ≫ pushout.inr _ _ ≫ m' = pushout.inr _ _ ≫ w
        rw [← hr', domCenterIncl, cornerLeg_inr_assoc]
    rw [hmdef]
    apply pushout.hom_ext
    · rw [pushout.inl_desc, hinl]
    · rw [pushout.inr_desc, hinr]

/-- The domain corner `hD` in fold form. -/
theorem domCorner_fold (j : S ⟶ T) (A B : I → SSet.{u}) (fam : ∀ a, A a ⟶ B a) :
    IsPushout (Limits.Sigma.map (fun a => cornerLeg j (fam a)))
      (Limits.Sigma.desc (fun _ : I => 𝟙 (pushout (joinMap j (𝟙 (⊥_ SSet.{u})))
        (joinMap (𝟙 S) (𝟙 (⊥_ SSet.{u}))))))
      (Limits.Sigma.desc (fun a => domLegIncl j A B fam a)) (domCenterIncl j A B fam) := by
  refine CubeLemma.isPushout_fold_of_universal (fun a => cornerLeg j (fam a))
    (domCenterIncl j A B fam) (fun a => domLegIncl j A B fam a) (fun a => ?_)
    (fun {Z} u w hw => domCorner_huniv j A B fam u w hw)
  -- `hcond`: `cornerLeg j (fam a) ≫ domLegIncl a = domCenterIncl`
  apply pushout.hom_ext
  · rw [cornerLeg_inl_assoc, domLegIncl, cornerMap_inl, ← Category.assoc, ← joinMap_comp_right,
      initialIsInitial.hom_ext (initial.to (A a) ≫ Limits.Sigma.ι A a) (initial.to (∐ A)),
      domCenterIncl, cornerLeg_inl]
  · rw [cornerLeg_inr_assoc, domLegIncl, cornerMap_inr, ← Category.assoc, ← joinMap_comp_right,
      initialIsInitial.hom_ext (initial.to (B a) ≫ Limits.Sigma.ι B a) (initial.to (∐ B)),
      domCenterIncl, cornerLeg_inr]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **satI's 4th instance**: `leibImgR j` is stable under coproducts. -/
theorem leibImgR_coproducts (j : S ⟶ T) : IsStableUnderCoproducts.{u} (leibImgR j) := by
  apply leibImgR_coproducts_of_cobaseSquare
  intro I A B fam
  haveI := leibnizJoin_id_right_isIso j (C := (⊥_ SSet.{u}))
  refine ⟨_, _, CubeLemma.isPushout_cobase_of_widePushout
    (leibnizJoin j (𝟙 (⊥_ SSet.{u}))) (fun a => leibnizJoin j (fam a))
    (fun a => cornerLeg j (fam a)) (fun a => (joinFunctor.obj T).map (initial.to (B a)))
    (fun a => ?hnat) (domCorner_fold j A B fam) (joinCoproduct_fold T B) ?hLg ?hLα⟩
  case hnat =>
    rw [cornerLeg_naturality j (fam a)]; simp only [joinMap_id_left]
  case hLg =>
    rw [domCenterIncl, cornerLeg_naturality j (Limits.Sigma.map fam)]
    simp only [joinMap_id_left, Functor.mapCocone_ι_app]
    exact congrArg (fun f => leibnizJoin j (𝟙 (⊥_ SSet.{u})) ≫ (joinFunctor.obj T).map f)
      (initialIsInitial.hom_ext _ _)
  case hLα =>
    apply Limits.Sigma.hom_ext
    intro a
    rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc,
      domLegIncl,
      cornerMap_naturality j (fam a) (Limits.Sigma.map fam) _ _ (Limits.Sigma.ι_map fam a)]
    simp only [joinMap_id_left]; rfl

end Coprod
end
end SSet
