import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.JoyalSpecialOuterHorn
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder

/-!
# Leibniz-join telescope: stability under transfinite composition (left slot)

The left-slot Leibniz image `leibImgL i` collects the maps `j` whose Leibniz join
`leibnizJoin j i` is inner-anodyne. This file proves it is stable under transfinite composition
(`leibImgL_isStableUnderTransfiniteComposition`, `leibImgL_transfiniteOfShape`) and cobase change
(`leibImgL_cobase`), by building the transfinite tower of join pushouts (`Gfun` and its colimit
`GwocIsColimit`) and transporting a colimit cocone across the join functor. One of the two
telescope slots feeding the Joyal pushout-product, Kerodon 018J (Proposition 4.3.6.4, Joyal).
-/

open CategoryTheory Simplicial Limits MorphismProperty HomotopicalAlgebra
namespace SSet
universe u
noncomputable section

@[simp] lemma joinMap_id (X Y : SSet.{u}) : joinMap (𝟙 X) (𝟙 Y) = 𝟙 (X ⋆ Y) := by
  rw [joinMap_id_right]; exact (joinFunctor.flip.obj Y).map_id X

/-- The left Leibniz image: `j ↦ innerAnodyne (leibnizJoin j i)` (the satJ predicate). -/
def leibImgL {A B : SSet.{u}} (i : A ⟶ B) : MorphismProperty SSet.{u} :=
  fun _ _ j => innerAnodyneExtensions (leibnizJoin j i)

variable {C D : SSet.{u}} (K : C ⟶ D)

section corner
variable {A A' B B' : SSet.{u}} {f : A ⟶ A'} {f' : B ⟶ B'} (u : A ⟶ B) (v : A' ⟶ B')
  (w : f ≫ v = u ≫ f')

def cornerMap : pushout (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) ⟶
    pushout (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K) :=
  pushout.map (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K)
    (joinMap v (𝟙 C)) (joinMap u (𝟙 D)) (joinMap u (𝟙 C))
    (by rw [← joinMap_comp_left, ← joinMap_comp_left, w]) ((joinMap_comm u K).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma cornerMap_inl :
    pushout.inl (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) ≫ cornerMap K u v w
      = joinMap v (𝟙 C) ≫ pushout.inl (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K) := by
  simp [cornerMap, pushout.map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma cornerMap_inr :
    pushout.inr (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) ≫ cornerMap K u v w
      = joinMap u (𝟙 D) ≫ pushout.inr (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K) := by
  simp [cornerMap, pushout.map]

lemma cornerMap_naturality :
    cornerMap K u v w ≫ leibnizJoin f' K = leibnizJoin f K ≫ joinMap v (𝟙 D) := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, cornerMap_inl]
    simp only [Category.assoc, leibnizJoin, pushout.inl_desc]
    rw [joinMap_comm v K]
  · simp only [← Category.assoc, cornerMap_inr]
    simp only [Category.assoc, leibnizJoin, pushout.inr_desc]
    rw [← joinMap_comp_left, ← joinMap_comp_left, w]
end corner

/-! ## leibnizJoin access lemmas + the `𝟙`-iso + the arrow functor. -/

@[reassoc] lemma leibnizJoin_inl {A B : SSet.{u}} (f : A ⟶ B) :
    pushout.inl (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) ≫ leibnizJoin f K = joinMap (𝟙 B) K := by
  simp only [leibnizJoin, pushout.inl_desc]

@[reassoc] lemma leibnizJoin_inr {A B : SSet.{u}} (f : A ⟶ B) :
    pushout.inr (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) ≫ leibnizJoin f K = joinMap f (𝟙 D) := by
  simp only [leibnizJoin, pushout.inr_desc]

instance leibnizJoin_id_isIso (X : SSet.{u}) : IsIso (leibnizJoin (𝟙 X) K) := by
  haveI : IsIso (joinMap (𝟙 X) (𝟙 C)) := by rw [joinMap_id]; infer_instance
  have h : pushout.inr (joinMap (𝟙 X) (𝟙 C)) (joinMap (𝟙 X) K) ≫ leibnizJoin (𝟙 X) K = 𝟙 _ := by
    simp only [leibnizJoin, pushout.inr_desc, joinMap_id]
  haveI : IsIso (pushout.inr (joinMap (𝟙 X) (𝟙 C)) (joinMap (𝟙 X) K) ≫ leibnizJoin (𝟙 X) K) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (pushout.inr (joinMap (𝟙 X) (𝟙 C)) (joinMap (𝟙 X) K))
    (leibnizJoin (𝟙 X) K)

/-- General connected-shape preservation: the flipped join functor preserves
`Js`-colimits for any connected `Js` with `Type u` colimits. -/
instance presJoinFlipGen {Js : Type u} [SmallCategory Js] [IsConnected Js]
    [HasColimitsOfShape Js (Type u)] (E : SSet.{u}) :
    PreservesColimitsOfShape Js (joinFunctor.flip.obj E) :=
  joinFunctor_flip_preservesConnectedColimits_of_tensorRight Js E

/-! ## Join keystones, generalized to an arbitrary (small) connected shape `Js`. -/

section JoinKeystones
variable {Js : Type u} [SmallCategory Js] (F : Js ⥤ SSet.{u})

@[simps]
def joinDiag (E : SSet.{u}) : Js ⥤ SSet.{u} where
  obj n := F.obj n ⋆ E
  map {n m} φ := joinMap (F.map φ) (𝟙 E)
  map_id n := by rw [F.map_id, joinMap_id]
  map_comp {n m p} φ ψ := by rw [F.map_comp, joinMap_comp_left]

def joinDiagIso (E : SSet.{u}) : joinDiag F E ≅ F ⋙ joinFunctor.flip.obj E :=
  NatIso.ofComponents (fun n => Iso.refl _) (by
    intro n m φ
    show joinMap (F.map φ) (𝟙 E) ≫ 𝟙 _ = 𝟙 _ ≫ (F ⋙ joinFunctor.flip.obj E).map φ
    rw [Category.comp_id, Category.id_comp, joinMap_id_right, Functor.comp_map])

variable {Y : SSet.{u}} (incl : F ⟶ (Functor.const Js).obj Y)
  (hcolim : IsColimit (Cocone.mk Y incl))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
def joinCocone (E : SSet.{u}) : Cocone (joinDiag F E) where
  pt := Y ⋆ E
  ι :=
    { app n := joinMap (incl.app n) (𝟙 E)
      naturality := by
        intro n m φ
        dsimp [joinDiag]
        rw [Category.comp_id, ← joinMap_comp_left]
        congr 1
        have := incl.naturality φ
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        rw [this] }

def joinColimit (E : SSet.{u}) [PreservesColimitsOfShape Js (joinFunctor.flip.obj E)] :
    IsColimit (joinCocone F incl E) := by
  have hpres : IsColimit ((joinFunctor.flip.obj E).mapCocone (Cocone.mk Y incl)) :=
    isColimitOfPreserves (joinFunctor.flip.obj E) hcolim
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (joinDiagIso F E) _).symm hpres) (Cocone.ext (Iso.refl _) ?_)
  intro n
  simp only [joinCocone, Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app,
    joinDiagIso, NatIso.ofComponents_hom_app, Iso.refl_hom]
  rw [joinMap_id_right]
  cat_disch

end JoinKeystones

/-! ## The corner-pushout telescope and the corner cocone (over a well-order `J`). -/

section Assembly
variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet.{u})

abbrev aTel (n : J) : F.obj ⊥ ⟶ F.obj n := F.map (homOfLE bot_le)

lemma aTel_comp {n m : J} (φ : n ⟶ m) : aTel F n ≫ F.map φ = aTel F m := by
  rw [← F.map_comp, Subsingleton.elim (homOfLE bot_le ≫ φ) (homOfLE (bot_le : (⊥ : J) ≤ m))]

@[simps]
def domDiag : J ⥤ SSet.{u} where
  obj n := pushout (joinMap (aTel F n) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K)
  map {n m} φ := cornerMap K (𝟙 (F.obj ⊥)) (F.map φ)
    (by rw [Category.id_comp, aTel_comp])
  map_id n := by
    apply pushout.hom_ext <;>
      simp only [cornerMap_inl, cornerMap_inr, F.map_id, joinMap_id, Category.id_comp,
        Category.comp_id]
  map_comp {n m p} φ ψ := by
    apply pushout.hom_ext <;>
      simp only [cornerMap_inl, cornerMap_inr, cornerMap_inl_assoc, cornerMap_inr_assoc,
        F.map_comp, joinMap_comp_left, joinMap_id, Category.id_comp, Category.assoc]

variable {Y : SSet.{u}} (incl : F ⟶ (Functor.const J).obj Y)
  (hcolim : IsColimit (Cocone.mk Y incl))

/-- `g := incl ⊥ : F⊥ ⟶ Y`. -/
abbrev gTel : F.obj ⊥ ⟶ Y := incl.app ⊥

/-- `P(g)`, the Leibniz corner pushout of `g` with `K`. -/
abbrev Pof (h : F.obj ⊥ ⟶ Y) : SSet.{u} := pushout (joinMap h (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The corner cocone on `domDiag` with point `P(g)`, legs `ιₙ = cornerMap (incl n)`. -/
@[simps]
def domCocone : Cocone (domDiag K F) where
  pt := Pof K F (gTel F incl)
  ι :=
    { app n := cornerMap K (𝟙 (F.obj ⊥)) (incl.app n)
        (by rw [Category.id_comp]; exact (by
          have := incl.naturality (homOfLE (bot_le : (⊥ : J) ≤ n))
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
          exact this))
      naturality := by
        intro n m φ
        dsimp [domDiag]
        rw [Category.comp_id]
        apply pushout.hom_ext
        · rw [cornerMap_inl_assoc, cornerMap_inl, cornerMap_inl, ← Category.assoc,
            ← joinMap_comp_left]
          congr 2
          have := incl.naturality φ
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
          rw [this]
        · rw [cornerMap_inr_assoc, cornerMap_inr, cornerMap_inr]
          simp [joinMap_id] }

lemma aTel_bot : aTel F ⊥ = 𝟙 (F.obj ⊥) := by
  rw [aTel, Subsingleton.elim (homOfLE (bot_le : (⊥ : J) ≤ ⊥)) (𝟙 (⊥ : J)), F.map_id]

/-- `inr` leg into `domDiag.obj n` (codomain typed for clean composition with cocone legs). -/
abbrev dinr (n : J) : F.obj ⊥ ⋆ D ⟶ (domDiag K F).obj n :=
  pushout.inr (joinMap (aTel F n) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K)

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma domCocone_inl (n : J) :
    pushout.inl (joinMap (aTel F n) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) ≫ (domCocone K F incl).ι.app n
      = joinMap (incl.app n) (𝟙 C)
        ≫ pushout.inl (joinMap (gTel F incl) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) := by
  rw [domCocone_ι_app, cornerMap_inl]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma domCocone_inr (n : J) :
    dinr K F n ≫ (domCocone K F incl).ι.app n
      = pushout.inr (joinMap (gTel F incl) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) := by
  show pushout.inr _ _ ≫ _ = _
  rw [domCocone_ι_app, cornerMap_inr]; simp [joinMap_id]

/-! ## The target filtration functor `G` and its assembly (satJ #117). -/

/-- `ιₙ : P(aₙ) ⟶ P(g)`, the corner-telescope cocone leg, retyped with explicit
pushout domain so that the Leibniz-join access lemmas apply syntactically. -/
def iCorner (n : J) :
    pushout (joinMap (aTel F n) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) ⟶ Pof K F (gTel F incl) :=
  (domCocone K F incl).ι.app n

/-- The cocone leg `incl.app n` retyped with target `Y` (no `const`-functor index). -/
abbrev gY (n : J) : F.obj n ⟶ Y := incl.app n

@[reassoc] lemma iCorner_inl (n : J) :
    pushout.inl (joinMap (aTel F n) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) ≫ iCorner K F incl n
      = joinMap (gY F incl n) (𝟙 C)
        ≫ pushout.inl (joinMap (gTel F incl) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) :=
  domCocone_inl K F incl n

@[reassoc] lemma iCorner_inr (n : J) :
    pushout.inr (joinMap (aTel F n) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) ≫ iCorner K F incl n
      = pushout.inr (joinMap (gTel F incl) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K) :=
  domCocone_inr K F incl n

/-- The corner cocone relation `cₙ ≫ ιₘ = ιₙ` over a step `φ : n ⟶ m`. -/
@[reassoc] lemma iCorner_w {n m : J} (φ : n ⟶ m) :
    cornerMap K (𝟙 (F.obj ⊥)) (F.map φ) (by rw [Category.id_comp, aTel_comp])
        ≫ iCorner K F incl m = iCorner K F incl n :=
  (domCocone K F incl).w φ

/-- `G : J ⥤ SSet`, `G n = pushout (ιₙ) (leibnizJoin aₙ K)`. -/
def Gfun : J ⥤ SSet.{u} where
  obj n := pushout (iCorner K F incl n) (leibnizJoin (aTel F n) K)
  map {n m} φ := pushout.desc
    (pushout.inl (iCorner K F incl m) (leibnizJoin (aTel F m) K))
    (joinMap (F.map φ) (𝟙 D) ≫ pushout.inr (iCorner K F incl m) (leibnizJoin (aTel F m) K))
    (by
      rw [← iCorner_w K F incl φ, Category.assoc, pushout.condition, ← Category.assoc,
        cornerMap_naturality, Category.assoc])
  map_id n := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, Category.comp_id]
    · simp only [pushout.inr_desc, F.map_id, joinMap_id, Category.id_comp, Category.comp_id]
  map_comp {n m p} φ ψ := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc, Category.assoc]
      rw [F.map_comp, joinMap_comp_left, Category.assoc]

@[reassoc] lemma Gfun_inl {n m : J} (φ : n ⟶ m) :
    pushout.inl (iCorner K F incl n) (leibnizJoin (aTel F n) K) ≫ (Gfun K F incl).map φ
      = pushout.inl (iCorner K F incl m) (leibnizJoin (aTel F m) K) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

@[reassoc] lemma Gfun_inr {n m : J} (φ : n ⟶ m) :
    pushout.inr (iCorner K F incl n) (leibnizJoin (aTel F n) K) ≫ (Gfun K F incl).map φ
      = joinMap (F.map φ) (𝟙 D)
        ≫ pushout.inr (iCorner K F incl m) (leibnizJoin (aTel F m) K) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `stepₙ ≫ incl(succ n) = incl n` (cocone naturality on the successor step). -/
lemma inclStep (n : J) :
    F.map (homOfLE (Order.le_succ n)) ≫ gY F incl (Order.succ n) = gY F incl n := by
  have := incl.naturality (homOfLE (Order.le_succ n))
  simpa using this

/-- The structure map `jₙ : P(stepₙ) ⟶ Gₙ` (analogue of the cube's `jStep`). -/
def GjStep (n : J) :
    pushout (joinMap (F.map (homOfLE (Order.le_succ n))) (𝟙 C)) (joinMap (𝟙 (F.obj n)) K)
      ⟶ pushout (iCorner K F incl n) (leibnizJoin (aTel F n) K) :=
  pushout.desc
    (joinMap (gY F incl (Order.succ n)) (𝟙 C)
      ≫ pushout.inl (joinMap (gTel F incl) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K)
      ≫ pushout.inl (iCorner K F incl n) (leibnizJoin (aTel F n) K))
    (pushout.inr (iCorner K F incl n) (leibnizJoin (aTel F n) K))
    (by
      rw [← Category.assoc, ← joinMap_comp_left, inclStep, ← iCorner_inl_assoc,
        pushout.condition, leibnizJoin_inl_assoc])

@[reassoc] lemma GjStep_inl (n : J) :
    pushout.inl (joinMap (F.map (homOfLE (Order.le_succ n))) (𝟙 C)) (joinMap (𝟙 (F.obj n)) K)
        ≫ GjStep K F incl n
      = joinMap (gY F incl (Order.succ n)) (𝟙 C)
        ≫ pushout.inl (joinMap (gTel F incl) (𝟙 C)) (joinMap (𝟙 (F.obj ⊥)) K)
        ≫ pushout.inl (iCorner K F incl n) (leibnizJoin (aTel F n) K) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

@[reassoc] lemma GjStep_inr (n : J) :
    pushout.inr (joinMap (F.map (homOfLE (Order.le_succ n))) (𝟙 C)) (joinMap (𝟙 (F.obj n)) K)
        ≫ GjStep K F incl n
      = pushout.inr (iCorner K F incl n) (leibnizJoin (aTel F n) K) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

/-- The raw filtration step `Gₙ ⟶ G(succ n)` (definitionally `Gfun.map (homOfLE _)`). -/
def GincMap (n : J) :
    pushout (iCorner K F incl n) (leibnizJoin (aTel F n) K)
      ⟶ pushout (iCorner K F incl (Order.succ n)) (leibnizJoin (aTel F (Order.succ n)) K) :=
  pushout.desc
    (pushout.inl (iCorner K F incl (Order.succ n)) (leibnizJoin (aTel F (Order.succ n)) K))
    (joinMap (F.map (homOfLE (Order.le_succ n))) (𝟙 D)
      ≫ pushout.inr (iCorner K F incl (Order.succ n)) (leibnizJoin (aTel F (Order.succ n)) K))
    (by
      rw [← iCorner_w (φ := homOfLE (Order.le_succ n)), Category.assoc, pushout.condition,
        ← Category.assoc, cornerMap_naturality, Category.assoc])

lemma GincMap_eq (n : J) :
    (Gfun K F incl).map (homOfLE (Order.le_succ n)) = GincMap K F incl n := rfl

@[reassoc] lemma GincMap_inl (n : J) :
    pushout.inl (iCorner K F incl n) (leibnizJoin (aTel F n) K) ≫ GincMap K F incl n
      = pushout.inl (iCorner K F incl (Order.succ n)) (leibnizJoin (aTel F (Order.succ n)) K) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

@[reassoc] lemma GincMap_inr (n : J) :
    pushout.inr (iCorner K F incl n) (leibnizJoin (aTel F n) K) ≫ GincMap K F incl n
      = joinMap (F.map (homOfLE (Order.le_succ n))) (𝟙 D)
        ≫ pushout.inr (iCorner K F incl (Order.succ n)) (leibnizJoin (aTel F (Order.succ n)) K) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

/-- THE CUBE (re-derived for `G` with uniform corner `P(g)`): `Gₙ ⟶ G(succ n)` is a
cobase change of `leibnizJoin stepₙ K`. -/
theorem Gincrement_isPushout (n : J) :
    IsPushout (leibnizJoin (F.map (homOfLE (Order.le_succ n))) K) (GjStep K F incl n)
      (pushout.inr (iCorner K F incl (Order.succ n)) (leibnizJoin (aTel F (Order.succ n)) K))
      (GincMap K F incl n) := by
  have hcomm : leibnizJoin (F.map (homOfLE (Order.le_succ n))) K
        ≫ pushout.inr (iCorner K F incl (Order.succ n)) (leibnizJoin (aTel F (Order.succ n)) K)
      = GjStep K F incl n ≫ GincMap K F incl n := by
    apply pushout.hom_ext
    · rw [leibnizJoin_inl_assoc, GjStep_inl_assoc, GincMap_inl,
        ← iCorner_inl_assoc (n := Order.succ n), pushout.condition, leibnizJoin_inl_assoc]
    · rw [leibnizJoin_inr_assoc, GjStep_inr_assoc, GincMap_inr]
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hcomm
    (fun t => pushout.desc
      (pushout.inl (iCorner K F incl n) (leibnizJoin (aTel F n) K) ≫ t.inr) t.inl ?_) ?_ ?_ ?_)
  · apply pushout.hom_ext
    · rw [iCorner_inl_assoc (n := Order.succ n), leibnizJoin_inl_assoc, ← GjStep_inl_assoc,
        ← t.condition, leibnizJoin_inl_assoc]
    · have key' : pushout.inr (iCorner K F incl n) (leibnizJoin (aTel F n) K) ≫ t.inr
          = joinMap (F.map (homOfLE (Order.le_succ n))) (𝟙 D) ≫ t.inl := by
        rw [← GjStep_inr_assoc, ← t.condition, leibnizJoin_inr_assoc]
      rw [iCorner_inr_assoc (n := Order.succ n), leibnizJoin_inr_assoc, ← iCorner_inr_assoc (n := n),
        pushout.condition_assoc, leibnizJoin_inr_assoc, key', ← Category.assoc,
        ← joinMap_comp_left, aTel_comp]
  · intro t; rw [pushout.inr_desc]
  · intro t
    have key' : pushout.inr (iCorner K F incl n) (leibnizJoin (aTel F n) K) ≫ t.inr
        = joinMap (F.map (homOfLE (Order.le_succ n))) (𝟙 D) ≫ t.inl := by
      rw [← GjStep_inr_assoc, ← t.condition, leibnizJoin_inr_assoc]
    apply pushout.hom_ext
    · rw [GincMap_inl_assoc, pushout.inl_desc]
    · rw [GincMap_inr_assoc, pushout.inr_desc, key']
  · intro t m hm1 hm2
    apply pushout.hom_ext
    · rw [pushout.inl_desc, ← hm2, GincMap_inl_assoc]
    · rw [pushout.inr_desc, ← hm1]

/-! ## The colimit identification `colim G ≅ Y ⋆ D`. -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma aTel_gY (n : J) : aTel F n ≫ gY F incl n = gTel F incl := by
  have := incl.naturality (homOfLE (bot_le : (⊥ : J) ≤ n)); simpa using this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma gY_naturality {n m : J} (φ : n ⟶ m) : F.map φ ≫ gY F incl m = gY F incl n := by
  have := incl.naturality φ; simpa using this

/-- Outer pushout `inl`, typed into `Gfun.obj n`. -/
abbrev Ginl (n : J) : Pof K F (gTel F incl) ⟶ (Gfun K F incl).obj n :=
  pushout.inl (iCorner K F incl n) (leibnizJoin (aTel F n) K)

/-- Outer pushout `inr`, typed into `Gfun.obj n`. -/
abbrev Ginr (n : J) : F.obj n ⋆ D ⟶ (Gfun K F incl).obj n :=
  pushout.inr (iCorner K F incl n) (leibnizJoin (aTel F n) K)

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma Gcond (n : J) :
    iCorner K F incl n ≫ Ginl K F incl n
      = leibnizJoin (aTel F n) K ≫ Ginr K F incl n := pushout.condition

set_option backward.isDefEq.respectTransparency false in
lemma Ghom_ext {n : J} {Z : SSet.{u}} {f g : (Gfun K F incl).obj n ⟶ Z}
    (h0 : Ginl K F incl n ≫ f = Ginl K F incl n ≫ g)
    (h1 : Ginr K F incl n ≫ f = Ginr K F incl n ≫ g) : f = g :=
  pushout.hom_ext h0 h1

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma Gmap_Ginl {n m : J} (φ : n ⟶ m) :
    Ginl K F incl n ≫ (Gfun K F incl).map φ = Ginl K F incl m := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _; rw [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma Gmap_Ginr {n m : J} (φ : n ⟶ m) :
    Ginr K F incl n ≫ (Gfun K F incl).map φ
      = joinMap (F.map φ) (𝟙 D) ≫ Ginr K F incl m := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _; rw [pushout.inr_desc]

/-- The cocone leg `Gₙ ⟶ Y ⋆ D`. -/
def GcoconeLeg (n : J) : (Gfun K F incl).obj n ⟶ Y ⋆ D :=
  pushout.desc (leibnizJoin (gTel F incl) K) (joinMap (gY F incl n) (𝟙 D))
    (cornerMap_naturality K (𝟙 (F.obj ⊥)) (gY F incl n)
      (by rw [Category.id_comp]; exact aTel_gY F incl n))

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GcoconeLeg_inl (n : J) :
    Ginl K F incl n ≫ GcoconeLeg K F incl n = leibnizJoin (gTel F incl) K := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GcoconeLeg_inr (n : J) :
    Ginr K F incl n ≫ GcoconeLeg K F incl n = joinMap (gY F incl n) (𝟙 D) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone on `G` with point `Y ⋆ D`. -/
def Gcocone : Cocone (Gfun K F incl) where
  pt := Y ⋆ D
  ι :=
    { app n := GcoconeLeg K F incl n
      naturality := by
        intro n m φ
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id]
        apply Ghom_ext
        · rw [Gmap_Ginl_assoc, GcoconeLeg_inl, GcoconeLeg_inl]
        · rw [Gmap_Ginr_assoc, GcoconeLeg_inr, GcoconeLeg_inr, ← joinMap_comp_left,
            gY_naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The descent cocone on `joinDiag F D` induced by a cocone `t` on `G` via the `inr` legs. -/
def GdescCocone (t : Cocone (Gfun K F incl)) : Cocone (joinDiag F D) where
  pt := t.pt
  ι :=
    { app n := Ginr K F incl n ≫ t.ι.app n
      naturality := by
        intro n m φ
        dsimp only [joinDiag, Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Gmap_Ginr_assoc, t.w] }

lemma GdescCocone_app (t : Cocone (Gfun K F incl)) (n : J) :
    (GdescCocone K F incl t).ι.app n = Ginr K F incl n ≫ t.ι.app n := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `inl`-leg constancy: `inlₙ ≫ tₙ` is independent of the stage. -/
lemma Ginl_const (t : Cocone (Gfun K F incl)) (n : J) :
    Ginl K F incl n ≫ t.ι.app n = Ginl K F incl ⊥ ≫ t.ι.app ⊥ := by
  rw [← Gmap_Ginl (φ := homOfLE (bot_le : (⊥ : J) ≤ n)), Category.assoc, t.w]

set_option backward.isDefEq.respectTransparency false in
/-- The hard `inl`-leg of the colimit factorisation. -/
lemma Gfac_inl (t : Cocone (Gfun K F incl)) (n : J) :
    leibnizJoin (gTel F incl) K ≫ (joinColimit F incl hcolim D).desc (GdescCocone K F incl t)
      = Ginl K F incl n ≫ t.ι.app n := by
  apply pushout.hom_ext
  · apply (joinColimit F incl hcolim C).hom_ext
    intro m
    simp only [joinCocone_ι_app]
    have hfacD := (joinColimit F incl hcolim D).fac (GdescCocone K F incl t) m
    simp only [joinCocone_ι_app] at hfacD
    rw [GdescCocone_app] at hfacD
    rw [leibnizJoin_inl_assoc, ← Category.assoc, joinMap_comm (gY F incl m) K, Category.assoc,
      hfacD, Ginl_const K F incl t n, ← Ginl_const K F incl t m, ← iCorner_inl_assoc (n := m),
      Gcond_assoc, leibnizJoin_inl_assoc]
  · have hfacD := (joinColimit F incl hcolim D).fac (GdescCocone K F incl t) ⊥
    simp only [joinCocone_ι_app] at hfacD
    rw [GdescCocone_app] at hfacD
    have hz : joinMap (aTel F ⊥) (𝟙 D) = 𝟙 (F.obj ⊥ ⋆ D) := by rw [aTel_bot, joinMap_id]
    rw [leibnizJoin_inr_assoc, hfacD, Ginl_const K F incl t n, ← iCorner_inr_assoc (n := ⊥),
      Gcond_assoc, leibnizJoin_inr_assoc, hz, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- `Y ⋆ D` is the colimit of `G`. -/
def GisColimit : IsColimit (Gcocone K F incl) where
  desc t := (joinColimit F incl hcolim D).desc (GdescCocone K F incl t)
  fac t n := by
    apply Ghom_ext
    · show Ginl K F incl n ≫ GcoconeLeg K F incl n ≫ _ = _
      rw [GcoconeLeg_inl_assoc, Gfac_inl]
    · show Ginr K F incl n ≫ GcoconeLeg K F incl n ≫ _ = _
      rw [GcoconeLeg_inr_assoc]
      have hfacD := (joinColimit F incl hcolim D).fac (GdescCocone K F incl t) n
      simp only [joinCocone_ι_app] at hfacD
      rw [GdescCocone_app] at hfacD
      rw [hfacD]
  uniq t m hm := by
    apply (joinColimit F incl hcolim D).hom_ext
    intro n
    rw [(joinColimit F incl hcolim D).fac, GdescCocone_app]
    simp only [joinCocone_ι_app]
    rw [← GcoconeLeg_inr_assoc (K := K)]
    congr 1
    exact hm n

/-- Each successor step `Gₙ ⟶ G(succ n)` is inner anodyne (the cobase change of `stepₙ`). -/
lemma Gstep_innerAnodyne (n : J)
    (hs : innerAnodyneExtensions (leibnizJoin (F.map (homOfLE (Order.le_succ n))) K)) :
    innerAnodyneExtensions ((Gfun K F incl).map (homOfLE (Order.le_succ n))) := by
  rw [GincMap_eq]
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := innerAnodyneExtensions)
    (Gincrement_isPushout K F incl n).flip hs

/-- `Gfun.obj ⊥ ≅ P(g)`: the bottom object is `P(g)` since `leibnizJoin (𝟙 F⊥) K` is iso. -/
instance Gbot_inl_isIso :
    IsIso (pushout.inl (iCorner K F incl ⊥) (leibnizJoin (aTel F ⊥) K)) := by
  haveI : IsIso (leibnizJoin (aTel F ⊥) K) := by rw [aTel_bot]; infer_instance
  infer_instance


/-! ## Step 3: `Gfun` is well-order-continuous (the genuinely-new obligation). -/

/-- `Set.Iio m` has a bottom element when `m` is a successor-limit. -/
def iioOrderBot (m : J) (hm : Order.IsSuccLimit m) : OrderBot (Set.Iio m) where
  bot := ⟨⊥, hm.bot_lt⟩
  bot_le := fun _ => bot_le

/-- `Set.Iio m` is connected when `m` is a successor-limit (zigzag through `⊥`). -/
theorem iioConnected (m : J) (hm : Order.IsSuccLimit m) : IsConnected (Set.Iio m) := by
  haveI : OrderBot (Set.Iio m) := iioOrderBot m hm
  haveI : Nonempty (Set.Iio m) := ⟨⊥⟩
  refine zigzag_isConnected (fun a b => ?_)
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (Or.inr ⟨homOfLE bot_le⟩))
    (Relation.ReflTransGen.single (Or.inl ⟨homOfLE bot_le⟩))

/-- The bottom element of `Set.Iio m`, as a concrete subtype value (so `.1` reduces to `⊥`). -/
abbrev iioBot (m : J) (hm : Order.IsSuccLimit m) : Set.Iio m := ⟨⊥, hm.bot_lt⟩

lemma iioBot_le (m : J) (hm : Order.IsSuccLimit m) (j : Set.Iio m) :
    iioBot m hm ≤ j := by
  show (⊥ : J) ≤ j.1
  exact bot_le

variable [F.IsWellOrderContinuous]

/-- `F⊥ ⟶ Fₘ` is the colimit of `F` restricted to `Set.Iio m` (well-order continuity). -/
def iioColim (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit (Cocone.mk (F.obj m) (((Set.principalSegIio m).cocone F).ι)) :=
  F.isColimitOfIsWellOrderContinuous' (Set.principalSegIio m) (by simpa using hm)


/-- Reduce the restricted-functor object back to the subtype coercion. -/
lemma psObj (m : J) (j : Set.Iio m) :
    (Set.principalSegIio m).monotone.functor.obj j = (j : J) := rfl

/-- Index-reduction for `Ginl` (default transparency closes `functor.obj j = ↑j`). -/
lemma GinlEq (m : J) (j : Set.Iio m) :
    Ginl K F incl ((Set.principalSegIio m).monotone.functor.obj j) = Ginl K F incl j.1 := rfl

/-- Index-reduction for `Ginr`. -/
lemma GinrEq (m : J) (j : Set.Iio m) :
    Ginr K F incl ((Set.principalSegIio m).monotone.functor.obj j) = Ginr K F incl j.1 := rfl

/-- Top-index reduction for `Ginl`. -/
lemma GinlTopEq (m : J) :
    Ginl K F incl ((Set.principalSegIio m).top) = Ginl K F incl m := rfl

/-- Top-index reduction for `Ginr`. -/
lemma GinrTopEq (m : J) :
    Ginr K F incl ((Set.principalSegIio m).top) = Ginr K F incl m := rfl

/-- The `Set.Iio m`-restricted join colimit: `Fₘ ⋆ E = colim_{j<m} (F_j ⋆ E)`. -/
def iioJoinColim (m : J) (hm : Order.IsSuccLimit m) (E : SSet.{u})
    [IsConnected (Set.Iio m)] :
    IsColimit (joinCocone ((Set.principalSegIio m).monotone.functor ⋙ F)
      (((Set.principalSegIio m).cocone F).ι) E) :=
  joinColimit ((Set.principalSegIio m).monotone.functor ⋙ F)
    (((Set.principalSegIio m).cocone F).ι) (iioColim F m hm) E

/-- The restricted-cocone leg of `Gfun`, in clean `Gfun.map` form. -/
lemma Gcocone_leg_eq (m : J) (j : Set.Iio m) :
    ((Set.principalSegIio m).cocone (Gfun K F incl)).ι.app j
      = (Gfun K F incl).map (homOfLE ((Set.principalSegIio m).lt_top j).le) := rfl

/-- Naturality of the restricted cocone against the global cocone legs. -/
lemma iioIncl_gY (m : J) (j : Set.Iio m) :
    ((Set.principalSegIio m).cocone F).ι.app j ≫ gY F incl m = gY F incl j.1 :=
  gY_naturality F incl _

/-- The restricted join leg composed with the `C`-component of the global cocone leg. -/
@[reassoc] lemma iioJoinGY (m : J) (j : Set.Iio m) :
    joinMap (((Set.principalSegIio m).cocone F).ι.app j) (𝟙 C) ≫ joinMap (gY F incl m) (𝟙 C)
      = joinMap (gY F incl j.1) (𝟙 C) := by
  rw [← joinMap_comp_left]
  exact congrArg (fun φ => joinMap φ (𝟙 C)) (iioIncl_gY F incl m j)

/-- Join bifunctoriality square for the restricted leg. -/
lemma iioJoin_comm (m : J) (j : Set.Iio m) :
    joinMap (((Set.principalSegIio m).cocone F).ι.app j) (𝟙 C) ≫ joinMap (𝟙 (F.obj m)) K
      = joinMap (𝟙 (F.obj j.1)) K ≫ joinMap (((Set.principalSegIio m).cocone F).ι.app j) (𝟙 D) :=
  joinMap_comm _ K

/-- The `Gfun` transport of a restricted join leg matches the `Gfun` cocone leg. -/
@[reassoc] lemma Gmap_Ginr_iio (m : J) (j : Set.Iio m) :
    joinMap (((Set.principalSegIio m).cocone F).ι.app j) (𝟙 D) ≫ Ginr K F incl m
      = Ginr K F incl j.1 ≫ ((Set.principalSegIio m).cocone (Gfun K F incl)).ι.app j := by
  rw [Gcocone_leg_eq]
  exact (Gmap_Ginr K F incl (homOfLE ((Set.principalSegIio m).lt_top j).le)).symm

/-- The `inl` leg composed with a restricted `Gfun` cocone leg is the top `inl` leg.
Proved in term mode so that all `principalSegIio` index-defeqs (`↑j` vs `toRelEmbedding j`,
`top` vs `m`) are discharged once at full transparency, avoiding `rw`-motive failures.
The `@[reassoc]` companion `Gmap_Ginl_iio_assoc` matches the 3-term composition directly,
so the heavy-index defeq stays inside the abstracted hole (never an `(a ≫ b)` intermediate). -/
@[reassoc] lemma Gmap_Ginl_iio (m : J) (j : Set.Iio m) :
    Ginl K F incl j.1 ≫ ((Set.principalSegIio m).cocone (Gfun K F incl)).ι.app j
      = Ginl K F incl m :=
  Gmap_Ginl K F incl (homOfLE ((Set.principalSegIio m).lt_top j).le)

/-- The bottom case of `Gmap_Ginl_iio`, stated with a literal `⊥` so the `inl`-uniqueness
leg closes by `rfl` (no `↑(iioBot m hm)` vs `⊥` residue). -/
@[reassoc] lemma Ginl_bot_psLeg (m : J) (hm : Order.IsSuccLimit m) :
    Ginl K F incl ⊥ ≫ ((Set.principalSegIio m).cocone (Gfun K F incl)).ι.app (iioBot m hm)
      = Ginl K F incl m :=
  Gmap_Ginl K F incl (homOfLE ((Set.principalSegIio m).lt_top (iioBot m hm)).le)

set_option backward.isDefEq.respectTransparency false in
/-- `inl`-leg constancy over `Set.Iio m`. -/
lemma Gwoc_inl_const (m : J) (hm : Order.IsSuccLimit m)
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun K F incl))
    (j : Set.Iio m) :
    Ginl K F incl j.1 ≫ t.ι.app j = Ginl K F incl ⊥ ≫ t.ι.app (iioBot m hm) := by
  have hw := t.w (homOfLE (iioBot_le m hm j))
  rw [Functor.comp_map] at hw
  rw [← hw, ← Category.assoc, Gmap_Ginl, GinlEq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The descent cocone on `joinDiag (F|Iio m) D` induced by a cocone `t` on `G|Iio m`. -/
def GwocDescCocone (m : J)
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun K F incl)) :
    Cocone (joinDiag ((Set.principalSegIio m).monotone.functor ⋙ F) D) where
  pt := t.pt
  ι :=
    { app j := Ginr K F incl j.1 ≫ t.ι.app j
      naturality := by
        intro j j' φ
        have hw := t.w φ
        rw [Functor.comp_map] at hw
        dsimp only [joinDiag_map, Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, Functor.comp_map, ← hw, Gmap_Ginr_assoc, GinrEq] }

lemma GwocDescCocone_app (m : J)
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun K F incl)) (j : Set.Iio m) :
    (GwocDescCocone K F incl m t).ι.app j = Ginr K F incl j.1 ≫ t.ι.app j := rfl

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The compatibility condition for the well-order-continuity descent map. -/
lemma Gwoc_compat (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun K F incl)) :
    iCorner K F incl m ≫ (Ginl K F incl ⊥ ≫ t.ι.app (iioBot m hm))
      = leibnizJoin (aTel F m) K
        ≫ (iioJoinColim F m hm D).desc (GwocDescCocone K F incl m t) := by
  have hbot : joinMap (aTel F m) (𝟙 D) ≫ (iioJoinColim F m hm D).desc (GwocDescCocone K F incl m t)
      = Ginr K F incl ⊥ ≫ t.ι.app (iioBot m hm) := by
    have h := (iioJoinColim F m hm D).fac (GwocDescCocone K F incl m t) (iioBot m hm)
    simp only [joinCocone_ι_app, GwocDescCocone_app, Functor.const_obj_obj] at h
    exact h
  apply pushout.hom_ext
  · -- inl leg over Fₘ ⋆ C
    rw [iCorner_inl_assoc, leibnizJoin_inl_assoc]
    apply (iioJoinColim F m hm C).hom_ext
    intro j
    have hfacD := (iioJoinColim F m hm D).fac (GwocDescCocone K F incl m t) j
    simp only [joinCocone_ι_app, GwocDescCocone_app] at hfacD ⊢
    rw [iioJoinGY_assoc]
    conv_rhs => rw [← Category.assoc, iioJoin_comm, Category.assoc, hfacD]
    rw [← Gwoc_inl_const K F incl m hm t j, ← iCorner_inl_assoc, Gcond_assoc, leibnizJoin_inl_assoc]
  · -- inr leg over F⊥ ⋆ D
    have hz : joinMap (aTel F ⊥) (𝟙 D) = 𝟙 (F.obj ⊥ ⋆ D) := by rw [aTel_bot, joinMap_id]
    rw [iCorner_inr_assoc, leibnizJoin_inr_assoc, hbot, ← iCorner_inr_assoc (n := (⊥ : J)),
      Gcond_assoc, leibnizJoin_inr_assoc, hz, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The descent map `Gₘ ⟶ t.pt` for the well-order-continuity colimit. -/
def GwocDesc (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun K F incl)) :
    (Gfun K F incl).obj m ⟶ t.pt :=
  pushout.desc (Ginl K F incl ⊥ ≫ t.ι.app (iioBot m hm))
    ((iioJoinColim F m hm D).desc (GwocDescCocone K F incl m t))
    (Gwoc_compat K F incl m hm t)

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GwocDesc_inl (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun K F incl)) :
    Ginl K F incl m ≫ GwocDesc K F incl m hm t = Ginl K F incl ⊥ ≫ t.ι.app (iioBot m hm) := by
  show pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] lemma GwocDesc_inr (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)]
    (t : Cocone ((Set.principalSegIio m).monotone.functor ⋙ Gfun K F incl)) :
    Ginr K F incl m ≫ GwocDesc K F incl m hm t
      = (iioJoinColim F m hm D).desc (GwocDescCocone K F incl m t) := by
  show pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]

set_option maxHeartbeats 4000000 in
/-- `Gₘ` is the colimit of `G` restricted to `Set.Iio m`: the well-order-continuity colimit. -/
def GwocIsColimit (m : J) (hm : Order.IsSuccLimit m) [IsConnected (Set.Iio m)] :
    IsColimit ((Set.principalSegIio m).cocone (Gfun K F incl)) where
  desc t := GwocDesc K F incl m hm t
  -- Both `fac` and `uniq` legs are closed in term mode. `rw` is unusable here: the
  -- `(Set.principalSegIio m).top`-vs-`m` and `↑j`-vs-`monotone.functor.obj j` defeqs are not
  -- visible at the `instances` transparency `rw` uses for its motive, so every `rw` on a
  -- goal mentioning the restricted cocone point/legs fails as "not type-correct". `exact`
  -- (default transparency) discharges these defeqs without a motive.
  fac t j := by
    refine Ghom_ext K F incl (n := j.1) ?_ ?_
    · exact (Gmap_Ginl_iio_assoc K F incl m j (GwocDesc K F incl m hm t)).trans
        ((GwocDesc_inl K F incl m hm t).trans (Gwoc_inl_const K F incl m hm t j).symm)
    · exact ((Gmap_Ginr_iio_assoc K F incl m j (GwocDesc K F incl m hm t)).symm.trans
          (congrArg (fun x => joinMap (((Set.principalSegIio m).cocone F).ι.app j) (𝟙 D) ≫ x)
            (GwocDesc_inr K F incl m hm t))).trans
        ((iioJoinColim F m hm D).fac (GwocDescCocone K F incl m t) j)
  uniq t φ hφ := by
    refine Ghom_ext K F incl (n := m) ?_ ?_
    · exact ((Ginl_bot_psLeg_assoc K F incl m hm φ).symm.trans
          (congrArg (fun x => Ginl K F incl ⊥ ≫ x) (hφ (iioBot m hm)))).trans
        (GwocDesc_inl K F incl m hm t).symm
    · exact ((iioJoinColim F m hm D).uniq (GwocDescCocone K F incl m t)
          (Ginr K F incl m ≫ φ)
          (fun j => (Gmap_Ginr_iio_assoc K F incl m j φ).trans
            (congrArg (fun x => Ginr K F incl j.1 ≫ x) (hφ j)))).trans
        (GwocDesc_inr K F incl m hm t).symm

/-- `Gfun K F incl` is well-order-continuous (the new obligation for the structure). -/
instance Gfun_isWellOrderContinuous : (Gfun K F incl).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    haveI : IsConnected (Set.Iio m) := iioConnected m hm
    exact ⟨GwocIsColimit K F incl m hm⟩

set_option maxHeartbeats 4000000 in
def Gtcs (hmem : ∀ (j : J), ¬ IsMax j →
      innerAnodyneExtensions (leibnizJoin (F.map (homOfLE (Order.le_succ j))) K)) :
    (innerAnodyneExtensions.{u}).TransfiniteCompositionOfShape J (leibnizJoin (gTel F incl) K) where
  F := Gfun K F incl
  isoBot := (asIso (pushout.inl (iCorner K F incl ⊥) (leibnizJoin (aTel F ⊥) K))).symm
  incl := (Gcocone K F incl).ι
  isColimit := GisColimit K F incl hcolim
  fac := GcoconeLeg_inl K F incl ⊥
  map_mem j hj := Gstep_innerAnodyne K F incl j (hmem j hj)

end Assembly

section Conclusion
variable {C D : SSet.{u}} (K : C ⟶ D)

set_option maxHeartbeats 4000000 in
/-- The left-slot Leibniz image `leibImgL K` is stable under transfinite composition of any
well-ordered shape `J`. -/
theorem leibImgL_transfiniteOfShape (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] : (leibImgL K).IsStableUnderTransfiniteCompositionOfShape J := by
  rw [isStableUnderTransfiniteCompositionOfShape_iff]
  rintro X Y f ⟨h⟩
  show innerAnodyneExtensions (leibnizJoin f K)
  haveI := h.isWellOrderContinuous
  have hmem : ∀ (j : J), ¬ IsMax j →
      innerAnodyneExtensions (leibnizJoin (h.F.map (homOfLE (Order.le_succ j))) K) :=
    fun j hj => h.map_mem j hj
  have hg : innerAnodyneExtensions (leibnizJoin (gTel h.F h.incl) K) :=
    (innerAnodyneExtensions.transfiniteCompositionsOfShape_le J) _
      (Gtcs K h.F h.incl h.isColimit hmem).mem
  have w1 : f ≫ 𝟙 Y = h.isoBot.inv ≫ gTel h.F h.incl := by
    rw [Category.comp_id]; exact h.fac.symm
  haveI : IsIso (joinMap (𝟙 Y) (𝟙 C)) := by rw [joinMap_id]; infer_instance
  haveI : IsIso (joinMap h.isoBot.inv (𝟙 D)) :=
    ⟨joinMap h.isoBot.hom (𝟙 D), by rw [← joinMap_comp_left, Iso.inv_hom_id, joinMap_id],
      by rw [← joinMap_comp_left, Iso.hom_inv_id, joinMap_id]⟩
  haveI : IsIso (joinMap h.isoBot.inv (𝟙 C)) :=
    ⟨joinMap h.isoBot.hom (𝟙 C), by rw [← joinMap_comp_left, Iso.inv_hom_id, joinMap_id],
      by rw [← joinMap_comp_left, Iso.hom_inv_id, joinMap_id]⟩
  haveI : IsIso (cornerMap K h.isoBot.inv (𝟙 Y) w1) := by unfold cornerMap; infer_instance
  have hcomp : leibnizJoin f K
      = cornerMap K h.isoBot.inv (𝟙 Y) w1 ≫ leibnizJoin (gTel h.F h.incl) K := by
    have hnat := cornerMap_naturality K h.isoBot.inv (𝟙 Y) w1
    rw [joinMap_id, Category.comp_id] at hnat
    exact hnat.symm
  rw [hcomp]
  exact (MorphismProperty.cancel_left_of_respectsIso innerAnodyneExtensions
    (cornerMap K h.isoBot.inv (𝟙 Y) w1) (leibnizJoin (gTel h.F h.incl) K)).mpr hg

/-- `leibImgL K` is stable under transfinite composition. -/
instance leibImgL_isStableUnderTransfiniteComposition :
    (leibImgL K).IsStableUnderTransfiniteComposition.{u} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := leibImgL_transfiniteOfShape K J

end Conclusion

/-! ## Cobase-change closure of `leibImgL K` -/

instance presSpanC : PreservesColimitsOfShape WalkingSpan (joinFunctor.flip.obj C) :=
  joinFunctor_flip_preservesConnectedColimits_of_tensorRight WalkingSpan C
instance presSpanD : PreservesColimitsOfShape WalkingSpan (joinFunctor.flip.obj D) :=
  joinFunctor_flip_preservesConnectedColimits_of_tensorRight WalkingSpan D

set_option backward.isDefEq.respectTransparency false in
/-- `leibImgL K` is stable under cobase change. -/
theorem leibImgL_cobase : (leibImgL K).IsStableUnderCobaseChange := by
  constructor
  intro A A' B B' f g f' g' sq hf
  have sqC : IsPushout (joinMap g (𝟙 C)) (joinMap f (𝟙 C)) (joinMap f' (𝟙 C))
      (joinMap g' (𝟙 C)) := by
    have := sq.map (joinFunctor.flip.obj C); simp only [← joinMap_id_right] at this; exact this
  have sqD : IsPushout (joinMap g (𝟙 D)) (joinMap f (𝟙 D)) (joinMap f' (𝟙 D))
      (joinMap g' (𝟙 D)) := by
    have := sq.map (joinFunctor.flip.obj D); simp only [← joinMap_id_right] at this; exact this
  have eq₁ : joinMap f (𝟙 C) ≫ joinMap g' (𝟙 C) = joinMap g (𝟙 C) ≫ joinMap f' (𝟙 C) := by
    rw [← joinMap_comp_left, ← joinMap_comp_left, sq.w]
  have eq₂ : joinMap (𝟙 A) K ≫ joinMap g (𝟙 D) = joinMap g (𝟙 C) ≫ joinMap (𝟙 B) K :=
    (joinMap_comm g K).symm
  set μ : pushout (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) ⟶
      pushout (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K) :=
    pushout.map (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K)
      (joinMap g' (𝟙 C)) (joinMap g (𝟙 D)) (joinMap g (𝟙 C)) eq₁ eq₂ with hμ
  set inlf := pushout.inl (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) with hinlf
  set inrf := pushout.inr (joinMap f (𝟙 C)) (joinMap (𝟙 A) K) with hinrf
  set inlf' := pushout.inl (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K) with hinlf'
  set inrf' := pushout.inr (joinMap f' (𝟙 C)) (joinMap (𝟙 B) K) with hinrf'
  have μ_inl : inlf ≫ μ = joinMap g' (𝟙 C) ≫ inlf' := by simp [hμ, hinlf, hinlf', pushout.map]
  have μ_inr : inrf ≫ μ = joinMap g (𝟙 D) ≫ inrf' := by simp [hμ, hinrf, hinrf', pushout.map]
  have ldil : inlf ≫ leibnizJoin f K = joinMap (𝟙 A') K := by simp [hinlf, leibnizJoin]
  have ldir : inrf ≫ leibnizJoin f K = joinMap f (𝟙 D) := by simp [hinrf, leibnizJoin]
  have ldil' : inlf' ≫ leibnizJoin f' K = joinMap (𝟙 B') K := by simp [hinlf', leibnizJoin]
  have ldir' : inrf' ≫ leibnizJoin f' K = joinMap f' (𝟙 D) := by simp [hinrf', leibnizJoin]
  have hcond' : joinMap f' (𝟙 C) ≫ inlf' = joinMap (𝟙 B) K ≫ inrf' := by
    simp [hinlf', hinrf', pushout.condition]
  have hcomm : μ ≫ leibnizJoin f' K = leibnizJoin f K ≫ joinMap g' (𝟙 D) := by
    apply pushout.hom_ext
    · rw [← hinlf]; simp only [← Category.assoc, μ_inl]
      rw [Category.assoc, ldil', ldil, joinMap_comm g' K]
    · rw [← hinrf]; simp only [← Category.assoc, μ_inr]
      rw [Category.assoc, ldir', ldir, ← joinMap_comp_left, ← joinMap_comp_left, sq.w]
  have colim : IsColimit (PushoutCocone.mk (leibnizJoin f' K) (joinMap g' (𝟙 D)) hcomm) := by
    refine PushoutCocone.IsColimit.mk hcomm
      (fun s => sqD.desc (inrf' ≫ s.inl) s.inr ?_) ?_ ?_ ?_
    · rw [← Category.assoc, ← μ_inr, Category.assoc, s.condition, ← Category.assoc, ldir]
    · intro s
      apply pushout.hom_ext
      · rw [← hinlf', ← Category.assoc, ldil']
        apply sqC.hom_ext
        · rw [← Category.assoc, joinMap_comm f' K, Category.assoc, sqD.inl_desc,
            ← Category.assoc, ← hcond', Category.assoc]
        · rw [← Category.assoc, joinMap_comm g' K, Category.assoc, sqD.inr_desc,
            ← Category.assoc, ← μ_inl, Category.assoc, s.condition, ← Category.assoc, ldil]
      · rw [← hinrf', ← Category.assoc, ldir', sqD.inl_desc]
    · intro s; exact sqD.inr_desc _ _ _
    · intro s m hl hr
      apply sqD.hom_ext
      · rw [sqD.inl_desc, ← ldir', Category.assoc, hl]
      · rw [sqD.inr_desc, hr]
  have cube : IsPushout μ (leibnizJoin f K) (leibnizJoin f' K) (joinMap g' (𝟙 D)) :=
    IsPushout.of_isColimit colim
  show innerAnodyneExtensions (leibnizJoin f' K)
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := innerAnodyneExtensions) cube hf

end
end SSet
