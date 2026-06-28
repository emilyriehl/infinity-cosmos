import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.JoyalSpecialOuterHorn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinCore

/-!
# Leibniz-join telescope: stability under transfinite composition (right slot)

The right-slot mirror of `LeibnizJoinTelescopeLeft`: for a fixed monomorphism `j`, the image
`leibImgR j` (the maps `i` with `leibnizJoin j i` inner-anodyne) is stable under transfinite
composition (`TwoC.leibImgR_isStableUnderTransfiniteComposition`,
`TwoC.leibImgR_transfiniteOfShape`). The same transfinite-tower construction as the left slot,
with the join taken in the right variable (`joinFunctor.obj` in place of `joinFunctor.flip.obj`).
Supplies the transfinite-composition instance for the Joyal pushout-product, Kerodon 018J
(Proposition 4.3.6.4, Joyal).
-/

open CategoryTheory Simplicial Limits MorphismProperty HomotopicalAlgebra
namespace SSet
universe u
noncomputable section

namespace TwoC

@[simp] lemma joinMap_id (X Y : SSet.{u}) : joinMap (𝟙 X) (𝟙 Y) = 𝟙 (X ⋆ Y) := by
  rw [joinMap_id_right]; exact (joinFunctor.flip.obj Y).map_id X

-- `leibImgR` is imported from `SatiCore` (identical definition).

variable {S T : SSet.{u}} (j : S ⟶ T)

section corner
variable {A A' B B' : SSet.{u}} {f : A ⟶ A'} {f' : B ⟶ B'} (u : A ⟶ B) (v : A' ⟶ B')
  (w : f ≫ v = u ≫ f')

def cornerMap : pushout (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) ⟶
    pushout (joinMap j (𝟙 B)) (joinMap (𝟙 S) f') :=
  pushout.map (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) (joinMap j (𝟙 B)) (joinMap (𝟙 S) f')
    (joinMap (𝟙 T) u) (joinMap (𝟙 S) v) (joinMap (𝟙 S) u)
    (joinMap_comm j u) (by rw [← joinMap_comp_right, ← joinMap_comp_right, w])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma cornerMap_inl :
    pushout.inl (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) ≫ cornerMap j u v w
      = joinMap (𝟙 T) u ≫ pushout.inl (joinMap j (𝟙 B)) (joinMap (𝟙 S) f') := by
  simp [cornerMap, pushout.map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma cornerMap_inr :
    pushout.inr (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) ≫ cornerMap j u v w
      = joinMap (𝟙 S) v ≫ pushout.inr (joinMap j (𝟙 B)) (joinMap (𝟙 S) f') := by
  simp [cornerMap, pushout.map]

lemma cornerMap_naturality :
    cornerMap j u v w ≫ leibnizJoin j f' = leibnizJoin j f ≫ joinMap (𝟙 T) v := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, cornerMap_inl]
    simp only [Category.assoc, leibnizJoin, pushout.inl_desc]
    rw [← joinMap_comp_right, ← joinMap_comp_right, ← w]
  · simp only [← Category.assoc, cornerMap_inr]
    simp only [Category.assoc, leibnizJoin, pushout.inr_desc]
    rw [← joinMap_comm j v]
end corner

/-! ## leibnizJoin access lemmas (legs swapped: inl = fixed-j, inr = vary). -/

@[reassoc] lemma leibnizJoin_inl {A B : SSet.{u}} (f : A ⟶ B) :
    pushout.inl (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) ≫ leibnizJoin j f = joinMap (𝟙 T) f := by
  simp only [leibnizJoin, pushout.inl_desc]

@[reassoc] lemma leibnizJoin_inr {A B : SSet.{u}} (f : A ⟶ B) :
    pushout.inr (joinMap j (𝟙 A)) (joinMap (𝟙 S) f) ≫ leibnizJoin j f = joinMap j (𝟙 B) := by
  simp only [leibnizJoin, pushout.inr_desc]

instance leibnizJoin_id_isIso (X : SSet.{u}) : IsIso (leibnizJoin j (𝟙 X)) := by
  haveI : IsIso (joinMap (𝟙 S) (𝟙 X)) := by rw [joinMap_id]; infer_instance
  have h : pushout.inl (joinMap j (𝟙 X)) (joinMap (𝟙 S) (𝟙 X)) ≫ leibnizJoin j (𝟙 X) = 𝟙 _ := by
    simp only [leibnizJoin, pushout.inl_desc, joinMap_id]
  haveI : IsIso (pushout.inl (joinMap j (𝟙 X)) (joinMap (𝟙 S) (𝟙 X)) ≫ leibnizJoin j (𝟙 X)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (pushout.inl (joinMap j (𝟙 X)) (joinMap (𝟙 S) (𝟙 X)))
    (leibnizJoin j (𝟙 X))

instance presJoinObjGen {Js : Type u} [SmallCategory Js] [IsConnected Js]
    [HasColimitsOfShape Js (Type u)] (E : SSet.{u}) :
    PreservesColimitsOfShape Js (joinFunctor.obj E) :=
  joinFunctor_obj_preservesConnectedColimits_of_tensorLeft Js E

/-! ## Join keystones (second slot): `E ⋆ -`. -/

section JoinKeystones
variable {Js : Type u} [SmallCategory Js] (F : Js ⥤ SSet.{u})

@[simps]
def joinDiag (E : SSet.{u}) : Js ⥤ SSet.{u} where
  obj n := E ⋆ F.obj n
  map {n m} φ := joinMap (𝟙 E) (F.map φ)
  map_id n := by rw [F.map_id, joinMap_id]
  map_comp {n m p} φ ψ := by rw [F.map_comp, joinMap_comp_right]

def joinDiagIso (E : SSet.{u}) : joinDiag F E ≅ F ⋙ joinFunctor.obj E :=
  NatIso.ofComponents (fun n => Iso.refl _) (by
    intro n m φ
    show joinMap (𝟙 E) (F.map φ) ≫ 𝟙 _ = 𝟙 _ ≫ (F ⋙ joinFunctor.obj E).map φ
    rw [Category.comp_id, Category.id_comp, joinMap_id_left, Functor.comp_map])

variable {Y : SSet.{u}} (incl : F ⟶ (Functor.const Js).obj Y)
  (hcolim : IsColimit (Cocone.mk Y incl))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
def joinCocone (E : SSet.{u}) : Cocone (joinDiag F E) where
  pt := E ⋆ Y
  ι :=
    { app n := joinMap (𝟙 E) (incl.app n)
      naturality := by
        intro n m φ
        dsimp [joinDiag]
        rw [Category.comp_id, ← joinMap_comp_right]
        congr 1
        have := incl.naturality φ
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        rw [this] }

def joinColimit (E : SSet.{u}) [PreservesColimitsOfShape Js (joinFunctor.obj E)] :
    IsColimit (joinCocone F incl E) := by
  have hpres : IsColimit ((joinFunctor.obj E).mapCocone (Cocone.mk Y incl)) :=
    isColimitOfPreserves (joinFunctor.obj E) hcolim
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (joinDiagIso F E) _).symm hpres) (Cocone.ext (Iso.refl _) ?_)
  intro n
  simp only [joinCocone, Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app,
    joinDiagIso, NatIso.ofComponents_hom_app, Iso.refl_hom]
  rw [joinMap_id_left]
  cat_disch

end JoinKeystones

/-! ## Corner telescope + corner cocone over a well-order `J`. -/

section Assembly
variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet.{u})

abbrev aTel (n : J) : F.obj ⊥ ⟶ F.obj n := F.map (homOfLE bot_le)

lemma aTel_comp {n m : J} (φ : n ⟶ m) : aTel F n ≫ F.map φ = aTel F m := by
  rw [← F.map_comp, Subsingleton.elim (homOfLE bot_le ≫ φ) (homOfLE (bot_le : (⊥ : J) ≤ m))]

@[simps]
def domDiag : J ⥤ SSet.{u} where
  obj n := pushout (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (aTel F n))
  map {n m} φ := cornerMap j (𝟙 (F.obj ⊥)) (F.map φ)
    (by rw [Category.id_comp, aTel_comp])
  map_id n := by
    apply pushout.hom_ext <;>
      simp only [cornerMap_inl, cornerMap_inr, F.map_id, joinMap_id, Category.id_comp,
        Category.comp_id]
  map_comp {n m p} φ ψ := by
    apply pushout.hom_ext <;>
      simp only [cornerMap_inl, cornerMap_inr, cornerMap_inl_assoc, cornerMap_inr_assoc,
        F.map_comp, joinMap_comp_right, joinMap_id, Category.id_comp, Category.assoc]

variable {Y : SSet.{u}} (incl : F ⟶ (Functor.const J).obj Y)
  (hcolim : IsColimit (Cocone.mk Y incl))

abbrev gTel : F.obj ⊥ ⟶ Y := incl.app ⊥

abbrev Pof (h : F.obj ⊥ ⟶ Y) : SSet.{u} := pushout (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
def domCocone : Cocone (domDiag j F) where
  pt := Pof j F (gTel F incl)
  ι :=
    { app n := cornerMap j (𝟙 (F.obj ⊥)) (incl.app n)
        (by rw [Category.id_comp]; exact (by
          have := incl.naturality (homOfLE (bot_le : (⊥ : J) ≤ n))
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
          exact this))
      naturality := by
        intro n m φ
        dsimp [domDiag]
        rw [Category.comp_id]
        apply pushout.hom_ext
        · rw [cornerMap_inl_assoc, cornerMap_inl, cornerMap_inl]
          simp [joinMap_id]
        · rw [cornerMap_inr_assoc, cornerMap_inr, cornerMap_inr, ← Category.assoc,
            ← joinMap_comp_right]
          congr 2
          have := incl.naturality φ
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
          rw [this] }

lemma aTel_bot : aTel F ⊥ = 𝟙 (F.obj ⊥) := by
  rw [aTel, Subsingleton.elim (homOfLE (bot_le : (⊥ : J) ≤ ⊥)) (𝟙 (⊥ : J)), F.map_id]

abbrev dinr (n : J) : T ⋆ F.obj ⊥ ⟶ (domDiag j F).obj n :=
  pushout.inl (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (aTel F n))

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma domCocone_inr (n : J) :
    pushout.inr (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (aTel F n)) ≫ (domCocone j F incl).ι.app n
      = joinMap (𝟙 S) (incl.app n)
        ≫ pushout.inr (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (gTel F incl)) := by
  rw [domCocone_ι_app, cornerMap_inr]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma domCocone_inl (n : J) :
    dinr j F n ≫ (domCocone j F incl).ι.app n
      = pushout.inl (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (gTel F incl)) := by
  show pushout.inl _ _ ≫ _ = _
  rw [domCocone_ι_app, cornerMap_inl]; simp [joinMap_id]

/-! ## Target filtration functor `G`. -/

def iCorner (n : J) :
    pushout (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (aTel F n)) ⟶ Pof j F (gTel F incl) :=
  (domCocone j F incl).ι.app n

abbrev gY (n : J) : F.obj n ⟶ Y := incl.app n

@[reassoc] lemma iCorner_inr (n : J) :
    pushout.inr (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (aTel F n)) ≫ iCorner j F incl n
      = joinMap (𝟙 S) (gY F incl n)
        ≫ pushout.inr (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (gTel F incl)) :=
  domCocone_inr j F incl n

@[reassoc] lemma iCorner_inl (n : J) :
    pushout.inl (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (aTel F n)) ≫ iCorner j F incl n
      = pushout.inl (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (gTel F incl)) :=
  domCocone_inl j F incl n

@[reassoc] lemma iCorner_w {n m : J} (φ : n ⟶ m) :
    cornerMap j (𝟙 (F.obj ⊥)) (F.map φ) (by rw [Category.id_comp, aTel_comp])
        ≫ iCorner j F incl m = iCorner j F incl n :=
  (domCocone j F incl).w φ

def Gfun : J ⥤ SSet.{u} where
  obj n := pushout (iCorner j F incl n) (leibnizJoin j (aTel F n))
  map {n m} φ := pushout.desc
    (pushout.inl (iCorner j F incl m) (leibnizJoin j (aTel F m)))
    (joinMap (𝟙 T) (F.map φ) ≫ pushout.inr (iCorner j F incl m) (leibnizJoin j (aTel F m)))
    (by
      rw [← iCorner_w j F incl φ, Category.assoc, pushout.condition, ← Category.assoc,
        cornerMap_naturality, Category.assoc])
  map_id n := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, Category.comp_id]
    · simp only [pushout.inr_desc, F.map_id, joinMap_id, Category.id_comp, Category.comp_id]
  map_comp {n m p} φ ψ := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc, Category.assoc]
      rw [F.map_comp, joinMap_comp_right, Category.assoc]

@[reassoc] lemma Gfun_inl {n m : J} (φ : n ⟶ m) :
    pushout.inl (iCorner j F incl n) (leibnizJoin j (aTel F n)) ≫ (Gfun j F incl).map φ
      = pushout.inl (iCorner j F incl m) (leibnizJoin j (aTel F m)) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

@[reassoc] lemma Gfun_inr {n m : J} (φ : n ⟶ m) :
    pushout.inr (iCorner j F incl n) (leibnizJoin j (aTel F n)) ≫ (Gfun j F incl).map φ
      = joinMap (𝟙 T) (F.map φ)
        ≫ pushout.inr (iCorner j F incl m) (leibnizJoin j (aTel F m)) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma inclStep (n : J) :
    F.map (homOfLE (Order.le_succ n)) ≫ gY F incl (Order.succ n) = gY F incl n := by
  have := incl.naturality (homOfLE (Order.le_succ n))
  simpa using this

def GjStep (n : J) :
    pushout (joinMap j (𝟙 (F.obj n))) (joinMap (𝟙 S) (F.map (homOfLE (Order.le_succ n))))
      ⟶ pushout (iCorner j F incl n) (leibnizJoin j (aTel F n)) :=
  pushout.desc
    (pushout.inr (iCorner j F incl n) (leibnizJoin j (aTel F n)))
    (joinMap (𝟙 S) (gY F incl (Order.succ n))
      ≫ pushout.inr (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (gTel F incl))
      ≫ pushout.inl (iCorner j F incl n) (leibnizJoin j (aTel F n)))
    (by
      rw [← Category.assoc, ← joinMap_comp_right, inclStep, ← iCorner_inr_assoc,
        pushout.condition, leibnizJoin_inr_assoc])

@[reassoc] lemma GjStep_inl (n : J) :
    pushout.inl (joinMap j (𝟙 (F.obj n))) (joinMap (𝟙 S) (F.map (homOfLE (Order.le_succ n))))
        ≫ GjStep j F incl n
      = pushout.inr (iCorner j F incl n) (leibnizJoin j (aTel F n)) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

@[reassoc] lemma GjStep_inr (n : J) :
    pushout.inr (joinMap j (𝟙 (F.obj n))) (joinMap (𝟙 S) (F.map (homOfLE (Order.le_succ n))))
        ≫ GjStep j F incl n
      = joinMap (𝟙 S) (gY F incl (Order.succ n))
        ≫ pushout.inr (joinMap j (𝟙 (F.obj ⊥))) (joinMap (𝟙 S) (gTel F incl))
        ≫ pushout.inl (iCorner j F incl n) (leibnizJoin j (aTel F n)) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

def GincMap (n : J) :
    pushout (iCorner j F incl n) (leibnizJoin j (aTel F n))
      ⟶ pushout (iCorner j F incl (Order.succ n)) (leibnizJoin j (aTel F (Order.succ n))) :=
  pushout.desc
    (pushout.inl (iCorner j F incl (Order.succ n)) (leibnizJoin j (aTel F (Order.succ n))))
    (joinMap (𝟙 T) (F.map (homOfLE (Order.le_succ n)))
      ≫ pushout.inr (iCorner j F incl (Order.succ n)) (leibnizJoin j (aTel F (Order.succ n))))
    (by
      rw [← iCorner_w (φ := homOfLE (Order.le_succ n)), Category.assoc, pushout.condition,
        ← Category.assoc, cornerMap_naturality, Category.assoc])

lemma GincMap_eq (n : J) :
    (Gfun j F incl).map (homOfLE (Order.le_succ n)) = GincMap j F incl n := rfl

@[reassoc] lemma GincMap_inl (n : J) :
    pushout.inl (iCorner j F incl n) (leibnizJoin j (aTel F n)) ≫ GincMap j F incl n
      = pushout.inl (iCorner j F incl (Order.succ n)) (leibnizJoin j (aTel F (Order.succ n))) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

@[reassoc] lemma GincMap_inr (n : J) :
    pushout.inr (iCorner j F incl n) (leibnizJoin j (aTel F n)) ≫ GincMap j F incl n
      = joinMap (𝟙 T) (F.map (homOfLE (Order.le_succ n)))
        ≫ pushout.inr (iCorner j F incl (Order.succ n)) (leibnizJoin j (aTel F (Order.succ n))) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

theorem Gincrement_isPushout (n : J) :
    IsPushout (leibnizJoin j (F.map (homOfLE (Order.le_succ n)))) (GjStep j F incl n)
      (pushout.inr (iCorner j F incl (Order.succ n)) (leibnizJoin j (aTel F (Order.succ n))))
      (GincMap j F incl n) := by
  have hcomm : leibnizJoin j (F.map (homOfLE (Order.le_succ n)))
        ≫ pushout.inr (iCorner j F incl (Order.succ n)) (leibnizJoin j (aTel F (Order.succ n)))
      = GjStep j F incl n ≫ GincMap j F incl n := by
    apply pushout.hom_ext
    · rw [leibnizJoin_inl_assoc, GjStep_inl_assoc, GincMap_inr]
    · rw [leibnizJoin_inr_assoc, GjStep_inr_assoc, GincMap_inl,
        ← iCorner_inr_assoc (n := Order.succ n), pushout.condition, leibnizJoin_inr_assoc]
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hcomm
    (fun t => pushout.desc
      (pushout.inl (iCorner j F incl n) (leibnizJoin j (aTel F n)) ≫ t.inr) t.inl ?_) ?_ ?_ ?_)
  · apply pushout.hom_ext
    · have key' : pushout.inr (iCorner j F incl n) (leibnizJoin j (aTel F n)) ≫ t.inr
          = joinMap (𝟙 T) (F.map (homOfLE (Order.le_succ n))) ≫ t.inl := by
        rw [← GjStep_inl_assoc, ← t.condition, leibnizJoin_inl_assoc]
      rw [iCorner_inl_assoc (n := Order.succ n), leibnizJoin_inl_assoc, ← iCorner_inl_assoc (n := n),
        pushout.condition_assoc, leibnizJoin_inl_assoc, key', ← Category.assoc,
        ← joinMap_comp_right, aTel_comp]
    · rw [iCorner_inr_assoc (n := Order.succ n), leibnizJoin_inr_assoc, ← GjStep_inr_assoc,
        ← t.condition, leibnizJoin_inr_assoc]
  · intro t; rw [pushout.inr_desc]
  · intro t
    have key' : pushout.inr (iCorner j F incl n) (leibnizJoin j (aTel F n)) ≫ t.inr
        = joinMap (𝟙 T) (F.map (homOfLE (Order.le_succ n))) ≫ t.inl := by
      rw [← GjStep_inl_assoc, ← t.condition, leibnizJoin_inl_assoc]
    apply pushout.hom_ext
    · rw [GincMap_inl_assoc, pushout.inl_desc]
    · rw [GincMap_inr_assoc, pushout.inr_desc, key']
  · intro t m hm1 hm2
    apply pushout.hom_ext
    · rw [pushout.inl_desc, ← hm2, GincMap_inl_assoc]
    · rw [pushout.inr_desc, ← hm1]

/-! ## colim G ≅ T ⋆ Y. -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma aTel_gY (n : J) : aTel F n ≫ gY F incl n = gTel F incl := by
  have := incl.naturality (homOfLE (bot_le : (⊥ : J) ≤ n)); simpa using this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma gY_naturality {n m : J} (φ : n ⟶ m) : F.map φ ≫ gY F incl m = gY F incl n := by
  have := incl.naturality φ; simpa using this

abbrev Ginl (n : J) : Pof j F (gTel F incl) ⟶ (Gfun j F incl).obj n :=
  pushout.inl (iCorner j F incl n) (leibnizJoin j (aTel F n))

abbrev Ginr (n : J) : T ⋆ F.obj n ⟶ (Gfun j F incl).obj n :=
  pushout.inr (iCorner j F incl n) (leibnizJoin j (aTel F n))

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma Gcond (n : J) :
    iCorner j F incl n ≫ Ginl j F incl n
      = leibnizJoin j (aTel F n) ≫ Ginr j F incl n := pushout.condition

set_option backward.isDefEq.respectTransparency false in
lemma Ghom_ext {n : J} {Z : SSet.{u}} {f g : (Gfun j F incl).obj n ⟶ Z}
    (h0 : Ginl j F incl n ≫ f = Ginl j F incl n ≫ g)
    (h1 : Ginr j F incl n ≫ f = Ginr j F incl n ≫ g) : f = g :=
  pushout.hom_ext h0 h1

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma Gmap_Ginl {n m : J} (φ : n ⟶ m) :
    Ginl j F incl n ≫ (Gfun j F incl).map φ = Ginl j F incl m := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _; rw [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma Gmap_Ginr {n m : J} (φ : n ⟶ m) :
    Ginr j F incl n ≫ (Gfun j F incl).map φ
      = joinMap (𝟙 T) (F.map φ) ≫ Ginr j F incl m := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _; rw [pushout.inr_desc]

def GcoconeLeg (n : J) : (Gfun j F incl).obj n ⟶ T ⋆ Y :=
  pushout.desc (leibnizJoin j (gTel F incl)) (joinMap (𝟙 T) (gY F incl n))
    (cornerMap_naturality j (𝟙 (F.obj ⊥)) (gY F incl n)
      (by rw [Category.id_comp]; exact aTel_gY F incl n))

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GcoconeLeg_inl (n : J) :
    Ginl j F incl n ≫ GcoconeLeg j F incl n = leibnizJoin j (gTel F incl) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GcoconeLeg_inr (n : J) :
    Ginr j F incl n ≫ GcoconeLeg j F incl n = joinMap (𝟙 T) (gY F incl n) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def Gcocone : Cocone (Gfun j F incl) where
  pt := T ⋆ Y
  ι :=
    { app n := GcoconeLeg j F incl n
      naturality := by
        intro n m φ
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id]
        apply Ghom_ext
        · rw [Gmap_Ginl_assoc, GcoconeLeg_inl, GcoconeLeg_inl]
        · rw [Gmap_Ginr_assoc, GcoconeLeg_inr, GcoconeLeg_inr, ← joinMap_comp_right,
            gY_naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def GdescCocone (t : Cocone (Gfun j F incl)) : Cocone (joinDiag F T) where
  pt := t.pt
  ι :=
    { app n := Ginr j F incl n ≫ t.ι.app n
      naturality := by
        intro n m φ
        dsimp only [joinDiag, Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Gmap_Ginr_assoc, t.w] }

lemma GdescCocone_app (t : Cocone (Gfun j F incl)) (n : J) :
    (GdescCocone j F incl t).ι.app n = Ginr j F incl n ≫ t.ι.app n := rfl

set_option backward.isDefEq.respectTransparency false in
lemma Ginl_const (t : Cocone (Gfun j F incl)) (n : J) :
    Ginl j F incl n ≫ t.ι.app n = Ginl j F incl ⊥ ≫ t.ι.app ⊥ := by
  rw [← Gmap_Ginl (φ := homOfLE (bot_le : (⊥ : J) ≤ n)), Category.assoc, t.w]

set_option backward.isDefEq.respectTransparency false in
lemma Gfac_inl (t : Cocone (Gfun j F incl)) (n : J) :
    leibnizJoin j (gTel F incl) ≫ (joinColimit F incl hcolim T).desc (GdescCocone j F incl t)
      = Ginl j F incl n ≫ t.ι.app n := by
  apply pushout.hom_ext
  · have hfacD := (joinColimit F incl hcolim T).fac (GdescCocone j F incl t) ⊥
    simp only [joinCocone_ι_app] at hfacD
    rw [GdescCocone_app] at hfacD
    have hz : joinMap (𝟙 T) (aTel F ⊥) = 𝟙 (T ⋆ F.obj ⊥) := by rw [aTel_bot, joinMap_id]
    rw [leibnizJoin_inl_assoc, hfacD, Ginl_const j F incl t n, ← iCorner_inl_assoc (n := ⊥),
      Gcond_assoc, leibnizJoin_inl_assoc, hz, Category.id_comp]
  · apply (joinColimit F incl hcolim S).hom_ext
    intro m
    simp only [joinCocone_ι_app]
    have hfacD := (joinColimit F incl hcolim T).fac (GdescCocone j F incl t) m
    simp only [joinCocone_ι_app] at hfacD
    rw [GdescCocone_app] at hfacD
    rw [leibnizJoin_inr_assoc, ← Category.assoc, ← joinMap_comm j (gY F incl m), Category.assoc,
      hfacD, Ginl_const j F incl t n, ← Ginl_const j F incl t m, ← iCorner_inr_assoc (n := m),
      Gcond_assoc, leibnizJoin_inr_assoc]

set_option backward.isDefEq.respectTransparency false in
def GisColimit : IsColimit (Gcocone j F incl) where
  desc t := (joinColimit F incl hcolim T).desc (GdescCocone j F incl t)
  fac t n := by
    apply Ghom_ext
    · show Ginl j F incl n ≫ GcoconeLeg j F incl n ≫ _ = _
      rw [GcoconeLeg_inl_assoc, Gfac_inl]
    · show Ginr j F incl n ≫ GcoconeLeg j F incl n ≫ _ = _
      rw [GcoconeLeg_inr_assoc]
      have hfacD := (joinColimit F incl hcolim T).fac (GdescCocone j F incl t) n
      simp only [joinCocone_ι_app] at hfacD
      rw [GdescCocone_app] at hfacD
      rw [hfacD]
  uniq t m hm := by
    apply (joinColimit F incl hcolim T).hom_ext
    intro n
    rw [(joinColimit F incl hcolim T).fac, GdescCocone_app]
    simp only [joinCocone_ι_app]
    rw [← GcoconeLeg_inr_assoc (j := j)]
    congr 1
    exact hm n

lemma Gstep_innerAnodyne (n : J)
    (hs : innerAnodyneExtensions (leibnizJoin j (F.map (homOfLE (Order.le_succ n))))) :
    innerAnodyneExtensions ((Gfun j F incl).map (homOfLE (Order.le_succ n))) := by
  rw [GincMap_eq]
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := innerAnodyneExtensions)
    (Gincrement_isPushout j F incl n).flip hs

instance Gbot_inl_isIso :
    IsIso (pushout.inl (iCorner j F incl ⊥) (leibnizJoin j (aTel F ⊥))) := by
  haveI : IsIso (leibnizJoin j (aTel F ⊥)) := by rw [aTel_bot]; infer_instance
  infer_instance

/-! ## Step 3: well-order-continuity of `Gfun`. -/

def iioOrderBot (m : J) (hm : Order.IsSuccLimit m) : OrderBot (Set.Iio m) where
  bot := ⟨⊥, hm.bot_lt⟩
  bot_le := fun _ => bot_le

theorem iioConnected (m : J) (hm : Order.IsSuccLimit m) : IsConnected (Set.Iio m) := by
  haveI : OrderBot (Set.Iio m) := iioOrderBot m hm
  haveI : Nonempty (Set.Iio m) := ⟨⊥⟩
  refine zigzag_isConnected (fun a b => ?_)
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (Or.inr ⟨homOfLE bot_le⟩))
    (Relation.ReflTransGen.single (Or.inl ⟨homOfLE bot_le⟩))

abbrev iioBot (m : J) (hm : Order.IsSuccLimit m) : Set.Iio m := ⟨⊥, hm.bot_lt⟩

lemma iioBot_le (m : J) (hm : Order.IsSuccLimit m) (k : Set.Iio m) :
    iioBot m hm ≤ k := by
  show (⊥ : J) ≤ k.1
  exact bot_le

variable [F.IsWellOrderContinuous]

def iioColim (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit (Cocone.mk (F.obj m) (((Set.principalSegIio m).cocone F).ι)) :=
  F.isColimitOfIsWellOrderContinuous' (Set.principalSegIio m) (by simpa using hm)

lemma psObj (m : J) (k : Set.Iio m) :
    (Set.principalSegIio m).monotone.functor.obj k = (k : J) := rfl

lemma GinlEq (m : J) (k : Set.Iio m) :
    Ginl j F incl ((Set.principalSegIio m).monotone.functor.obj k) = Ginl j F incl k.1 := rfl

lemma GinrEq (m : J) (k : Set.Iio m) :
    Ginr j F incl ((Set.principalSegIio m).monotone.functor.obj k) = Ginr j F incl k.1 := rfl

lemma GinlTopEq (m : J) :
    Ginl j F incl ((Set.principalSegIio m).top) = Ginl j F incl m := rfl

lemma GinrTopEq (m : J) :
    Ginr j F incl ((Set.principalSegIio m).top) = Ginr j F incl m := rfl

def iioJoinColim (m : J) (hm : Order.IsSuccLimit m) (E : SSet.{u})
    [IsConnected (Set.Iio m)] :
    IsColimit (joinCocone ((Set.principalSegIio m).monotone.functor ⋙ F)
      (((Set.principalSegIio m).cocone F).ι) E) :=
  joinColimit ((Set.principalSegIio m).monotone.functor ⋙ F)
    (((Set.principalSegIio m).cocone F).ι) (iioColim F m hm) E

lemma Gcocone_leg_eq (m : J) (k : Set.Iio m) :
    ((Set.principalSegIio m).cocone (Gfun j F incl)).ι.app k
      = (Gfun j F incl).map (homOfLE ((Set.principalSegIio m).lt_top k).le) := rfl

lemma iioIncl_gY (m : J) (k : Set.Iio m) :
    ((Set.principalSegIio m).cocone F).ι.app k ≫ gY F incl m = gY F incl k.1 :=
  gY_naturality F incl _

@[reassoc] lemma iioJoinGY (m : J) (k : Set.Iio m) :
    joinMap (𝟙 T) (((Set.principalSegIio m).cocone F).ι.app k) ≫ joinMap (𝟙 T) (gY F incl m)
      = joinMap (𝟙 T) (gY F incl k.1) := by
  rw [← joinMap_comp_right]
  exact congrArg (fun φ => joinMap (𝟙 T) φ) (iioIncl_gY F incl m k)

@[reassoc] lemma iioJoin_comm (m : J) (k : Set.Iio m) :
    joinMap (𝟙 S) (((Set.principalSegIio m).cocone F).ι.app k) ≫ joinMap (𝟙 S) (gY F incl m)
      = joinMap (𝟙 S) (gY F incl k.1) := by
  rw [← joinMap_comp_right]
  exact congrArg (fun φ => joinMap (𝟙 S) φ) (iioIncl_gY F incl m k)

set_option maxHeartbeats 4000000 in
/-- Cross-slot commutation for the restricted leg (index-pinned to `F.obj m` / `F.obj k.1`). -/
lemma iioJoinCross (m : J) (k : Set.Iio m) :
    joinMap (𝟙 S) (((Set.principalSegIio m).cocone F).ι.app k) ≫ joinMap j (𝟙 (F.obj m))
      = joinMap j (𝟙 (F.obj k.1))
        ≫ joinMap (𝟙 T) (((Set.principalSegIio m).cocone F).ι.app k) :=
  (joinMap_comm j (((Set.principalSegIio m).cocone F).ι.app k)).symm

@[reassoc] lemma Gmap_Ginr_iio (m : J) (k : Set.Iio m) :
    joinMap (𝟙 T) (((Set.principalSegIio m).cocone F).ι.app k) ≫ Ginr j F incl m
      = Ginr j F incl k.1 ≫ ((Set.principalSegIio m).cocone (Gfun j F incl)).ι.app k := by
  rw [Gcocone_leg_eq]
  exact (Gmap_Ginr j F incl (homOfLE ((Set.principalSegIio m).lt_top k).le)).symm

@[reassoc] lemma Gmap_Ginl_iio (m : J) (k : Set.Iio m) :
    Ginl j F incl k.1 ≫ ((Set.principalSegIio m).cocone (Gfun j F incl)).ι.app k
      = Ginl j F incl m :=
  Gmap_Ginl j F incl (homOfLE ((Set.principalSegIio m).lt_top k).le)

@[reassoc] lemma Ginl_bot_psLeg (m : J) (hm : Order.IsSuccLimit m) :
    Ginl j F incl ⊥ ≫ ((Set.principalSegIio m).cocone (Gfun j F incl)).ι.app (iioBot m hm)
      = Ginl j F incl m :=
  Gmap_Ginl j F incl (homOfLE ((Set.principalSegIio m).lt_top (iioBot m hm)).le)

set_option backward.isDefEq.respectTransparency false in
lemma Gwoc_inl_const (m : J) (hm : Order.IsSuccLimit m)
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun j F incl))
    (k : Set.Iio m) :
    Ginl j F incl k.1 ≫ t.ι.app k = Ginl j F incl ⊥ ≫ t.ι.app (iioBot m hm) := by
  have hw := t.w (homOfLE (iioBot_le m hm k))
  rw [Functor.comp_map] at hw
  rw [← hw, ← Category.assoc, Gmap_Ginl, GinlEq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def GwocDescCocone (m : J)
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun j F incl)) :
    Cocone (joinDiag ((Set.principalSegIio m).monotone.functor ⋙ F) T) where
  pt := t.pt
  ι :=
    { app k := Ginr j F incl k.1 ≫ t.ι.app k
      naturality := by
        intro k k' φ
        have hw := t.w φ
        rw [Functor.comp_map] at hw
        dsimp only [joinDiag_map, Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, Functor.comp_map, ← hw, Gmap_Ginr_assoc, GinrEq] }

lemma GwocDescCocone_app (m : J)
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun j F incl)) (k : Set.Iio m) :
    (GwocDescCocone j F incl m t).ι.app k = Ginr j F incl k.1 ≫ t.ι.app k := rfl

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
lemma Gwoc_compat (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun j F incl)) :
    iCorner j F incl m ≫ (Ginl j F incl ⊥ ≫ t.ι.app (iioBot m hm))
      = leibnizJoin j (aTel F m)
        ≫ (iioJoinColim F m hm T).desc (GwocDescCocone j F incl m t) := by
  have hbot : joinMap (𝟙 T) (aTel F m) ≫ (iioJoinColim F m hm T).desc (GwocDescCocone j F incl m t)
      = Ginr j F incl ⊥ ≫ t.ι.app (iioBot m hm) := by
    have h := (iioJoinColim F m hm T).fac (GwocDescCocone j F incl m t) (iioBot m hm)
    simp only [joinCocone_ι_app, GwocDescCocone_app, Functor.const_obj_obj] at h
    exact h
  apply pushout.hom_ext
  · -- inl leg over T ⋆ F⊥
    have hz : joinMap (𝟙 T) (aTel F ⊥) = 𝟙 (T ⋆ F.obj ⊥) := by rw [aTel_bot, joinMap_id]
    rw [iCorner_inl_assoc, leibnizJoin_inl_assoc, hbot, ← iCorner_inl_assoc (n := (⊥ : J)),
      Gcond_assoc, leibnizJoin_inl_assoc, hz, Category.id_comp]
  · -- inr leg over Fₘ ⋆ S  (i.e. S ⋆ Fₘ — the varying side)
    rw [iCorner_inr_assoc, leibnizJoin_inr_assoc]
    apply (iioJoinColim F m hm S).hom_ext
    intro k
    have hfacD := (iioJoinColim F m hm T).fac (GwocDescCocone j F incl m t) k
    simp only [joinCocone_ι_app, GwocDescCocone_app] at hfacD ⊢
    rw [iioJoin_comm_assoc]
    conv_rhs => rw [← Category.assoc, iioJoinCross, Category.assoc, hfacD]
    rw [← Gwoc_inl_const j F incl m hm t k, ← iCorner_inr_assoc, Gcond_assoc, leibnizJoin_inr_assoc]

set_option backward.isDefEq.respectTransparency false in
def GwocDesc (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun j F incl)) :
    (Gfun j F incl).obj m ⟶ t.pt :=
  pushout.desc (Ginl j F incl ⊥ ≫ t.ι.app (iioBot m hm))
    ((iioJoinColim F m hm T).desc (GwocDescCocone j F incl m t))
    (Gwoc_compat j F incl m hm t)

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GwocDesc_inl (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun j F incl)) :
    Ginl j F incl m ≫ GwocDesc j F incl m hm t = Ginl j F incl ⊥ ≫ t.ι.app (iioBot m hm) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GwocDesc_inr (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun j F incl)) :
    Ginr j F incl m ≫ GwocDesc j F incl m hm t
      = (iioJoinColim F m hm T).desc (GwocDescCocone j F incl m t) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

set_option maxHeartbeats 4000000 in
def GwocIsColimit (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)] :
    IsColimit ((Set.principalSegIio m).cocone (Gfun j F incl)) where
  desc t := GwocDesc j F incl m hm t
  fac t k := by
    refine Ghom_ext j F incl (n := k.1) ?_ ?_
    · exact (Gmap_Ginl_iio_assoc j F incl m k (GwocDesc j F incl m hm t)).trans
        ((GwocDesc_inl j F incl m hm t).trans (Gwoc_inl_const j F incl m hm t k).symm)
    · exact ((Gmap_Ginr_iio_assoc j F incl m k (GwocDesc j F incl m hm t)).symm.trans
          (congrArg (fun x => joinMap (𝟙 T) (((Set.principalSegIio m).cocone F).ι.app k) ≫ x)
            (GwocDesc_inr j F incl m hm t))).trans
        ((iioJoinColim F m hm T).fac (GwocDescCocone j F incl m t) k)
  uniq t φ hφ := by
    refine Ghom_ext j F incl (n := m) ?_ ?_
    · exact ((Ginl_bot_psLeg_assoc j F incl m hm φ).symm.trans
          (congrArg (fun x => Ginl j F incl ⊥ ≫ x) (hφ (iioBot m hm)))).trans
        (GwocDesc_inl j F incl m hm t).symm
    · exact ((iioJoinColim F m hm T).uniq (GwocDescCocone j F incl m t)
          (Ginr j F incl m ≫ φ)
          (fun k => (Gmap_Ginr_iio_assoc j F incl m k φ).trans
            (congrArg (fun x => Ginr j F incl k.1 ≫ x) (hφ k)))).trans
        (GwocDesc_inr j F incl m hm t).symm

instance Gfun_isWellOrderContinuous : (Gfun j F incl).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    haveI : IsConnected (Set.Iio m) := iioConnected m hm
    exact ⟨GwocIsColimit j F incl m hm⟩

set_option maxHeartbeats 4000000 in
def Gtcs (hmem : ∀ (k : J), ¬ IsMax k →
      innerAnodyneExtensions (leibnizJoin j (F.map (homOfLE (Order.le_succ k))))) :
    (innerAnodyneExtensions.{u}).TransfiniteCompositionOfShape J (leibnizJoin j (gTel F incl)) where
  F := Gfun j F incl
  isoBot := (asIso (pushout.inl (iCorner j F incl ⊥) (leibnizJoin j (aTel F ⊥)))).symm
  incl := (Gcocone j F incl).ι
  isColimit := GisColimit j F incl hcolim
  fac := GcoconeLeg_inl j F incl ⊥
  map_mem k hk := Gstep_innerAnodyne j F incl k (hmem k hk)

end Assembly

section Conclusion
variable {S T : SSet.{u}} (j : S ⟶ T)

set_option maxHeartbeats 4000000 in
/-- For a fixed monomorphism `j`, the image `leibImgR j` is stable under transfinite composition
of any well-ordered shape `J`. -/
theorem leibImgR_transfiniteOfShape (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] : (leibImgR j).IsStableUnderTransfiniteCompositionOfShape J := by
  rw [isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨h⟩
  show innerAnodyneExtensions (leibnizJoin j f)
  haveI := h.isWellOrderContinuous
  have hmem : ∀ (k : J), ¬ IsMax k →
      innerAnodyneExtensions (leibnizJoin j (h.F.map (homOfLE (Order.le_succ k)))) :=
    fun k hk => h.map_mem k hk
  have hg : innerAnodyneExtensions (leibnizJoin j (gTel h.F h.incl)) :=
    (innerAnodyneExtensions.transfiniteCompositionsOfShape_le J) _
      (Gtcs j h.F h.incl h.isColimit hmem).mem
  have w1 : f ≫ 𝟙 Y = h.isoBot.inv ≫ gTel h.F h.incl := by
    rw [Category.comp_id]; exact h.fac.symm
  haveI : IsIso (joinMap (𝟙 S) (𝟙 Y)) := by rw [joinMap_id]; infer_instance
  haveI : IsIso (joinMap (𝟙 T) h.isoBot.inv) :=
    ⟨joinMap (𝟙 T) h.isoBot.hom, by rw [← joinMap_comp_right, Iso.inv_hom_id, joinMap_id],
      by rw [← joinMap_comp_right, Iso.hom_inv_id, joinMap_id]⟩
  haveI : IsIso (joinMap (𝟙 S) h.isoBot.inv) :=
    ⟨joinMap (𝟙 S) h.isoBot.hom, by rw [← joinMap_comp_right, Iso.inv_hom_id, joinMap_id],
      by rw [← joinMap_comp_right, Iso.hom_inv_id, joinMap_id]⟩
  haveI : IsIso (cornerMap j h.isoBot.inv (𝟙 Y) w1) := by unfold cornerMap; infer_instance
  have hcomp : leibnizJoin j f
      = cornerMap j h.isoBot.inv (𝟙 Y) w1 ≫ leibnizJoin j (gTel h.F h.incl) := by
    have hnat := cornerMap_naturality j h.isoBot.inv (𝟙 Y) w1
    rw [joinMap_id, Category.comp_id] at hnat
    exact hnat.symm
  rw [hcomp]
  exact (MorphismProperty.cancel_left_of_respectsIso innerAnodyneExtensions
    (cornerMap j h.isoBot.inv (𝟙 Y) w1) (leibnizJoin j (gTel h.F h.incl))).mpr hg

/-- `leibImgR j` is stable under transfinite composition. -/
instance leibImgR_isStableUnderTransfiniteComposition :
    (leibImgR j).IsStableUnderTransfiniteComposition.{u} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := leibImgR_transfiniteOfShape j J

end Conclusion
end TwoC
end
end SSet
