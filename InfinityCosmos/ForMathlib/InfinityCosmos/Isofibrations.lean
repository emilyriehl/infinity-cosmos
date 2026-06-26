/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JHU Category Theory Seminar
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy

open scoped Simplicial

/-!
# Explicit isofibrations in an ∞-cosmos.

This file constructs a few explicit isofibrations in an ∞-cosmos as consequences of the axioms.

Simple examples include:

* `compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C`
* `pullbackIsofibration {E B A : K} (p : E ↠ B) (f : A ⟶ B) : pullbackIsofibrationObj p f ↠ A`
* `toTerminalIsofibration (A : K) : A ↠ (⊤_ K)`

More elaborate examples include:

* `cotensorCovIsofibration (V : SSet.{v}) {A B : K} (f : A ↠ B) : V ⋔ A ↠ V ⋔ B`
* `cotensorContraIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (A : K) : V ⋔ A ↠ U ⋔ A`
* `leibnizCotensorIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :`
    `V ⋔ A ↠ leibnizCotensorCod i f`

All but the first of these involve explicit choices of limits so are noncomputable.
-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos
open HasConicalTerminal
open MonoidalCategory BraidedCategory

variable {K : Type u} [Category.{v} K] [InfinityCosmos K]

/-- The composite of isofibrations. -/
def compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C :=
  ⟨(f.1 ≫ g.1), comp_isIsofibration f g⟩

@[simp]
lemma compIsofibration_map {A B C : K} (f : A ↠ B) (g : B ↠ C) :
    (compIsofibration f g).1 = f.1 ≫ g.1 := rfl

/-- The object defined by pulling back an isofibration. -/
noncomputable def pullbackIsofibrationObj {E B A : K} (p : E ↠ B) (f : A ⟶ B) : K :=
  pullback p.1 f

/-- The object defined by pulling back an isofibration. -/
noncomputable def pullbackIsofibration {E B A : K} (p : E ↠ B) (f : A ⟶ B) :
    pullbackIsofibrationObj p f ↠ A :=
  ⟨pullback.snd p.1 f, pullback_isIsofibration _ _ _ _ (IsPullback.of_hasPullback p.1 f)⟩

@[simp]
lemma pullbackIsofibration_map {E B A : K} (p : E ↠ B) (f : A ⟶ B) :
    (pullbackIsofibration p f).1 = pullback.snd p.1 f := rfl

theorem toTerminal_fibrant (A : K) : IsIsofibration (terminal.from A) :=
  all_objects_fibrant terminalIsConicalTerminal _

/-- The explicit map `terminal.from A` is an isofibration in an ∞-cosmos. -/
noncomputable def toTerminalIsofibration (A : K) : A ↠ (⊤_ K) :=
  ⟨terminal.from A, toTerminal_fibrant A⟩

@[simp]
lemma toTerminalIsofibration_map (A : K) : (toTerminalIsofibration A).1 = terminal.from A := rfl

/-- Note: proven by Aristotle. -/
theorem binary_prod_map_fibrant {X Y X' Y' : K} {f : X ↠ Y} {g : X' ↠ Y'} :
    IsIsofibration (prod.map f.1 g.1) := by
  rw [show prod.map f.1 g.1 = prod.map f.1 (𝟙 X') ≫ prod.map (𝟙 Y) g.1
    from by rw [prod.map_map, comp_id, id_comp]]
  apply comp_isIsofibration ⟨_, ?_⟩ ⟨_, ?_⟩
  · exact pullback_isIsofibration f prod.fst prod.fst (prod.map f.1 (𝟙 X'))
      (IsPullback.of_bot
        (by convert IsPullback.of_hasBinaryProduct' X X' using 1
            · simp [prod.map_snd]
            · simp [terminal.comp_from])
        (prod.map_fst _ _).symm
        (IsPullback.of_hasBinaryProduct' Y X'))
  · exact pullback_isIsofibration g prod.snd prod.snd (prod.map (𝟙 Y) g.1)
      (IsPullback.of_bot
        (by convert (IsPullback.of_hasBinaryProduct' Y X').flip using 1
            · simp [prod.map_fst]
            · simp [terminal.comp_from])
        (prod.map_snd _ _).symm
        (IsPullback.of_hasBinaryProduct' Y Y').flip)

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.
noncomputable def cotensorInitialIso (A : K) : (⊥_ SSet.{v} ) ⋔ A ≅ ⊤_ K where
  hom := terminal.from ((⊥_ SSet.{v}) ⋔ A)
  inv := (cotensor.iso.underlying (⊥_ SSet.{v}) A (⊤_ K)).symm (initial.to (sHom (⊤_ K) A))
  hom_inv_id := (cotensor.iso.underlying (⊥_ SSet.{v}) A ((⊥_ SSet.{v} ) ⋔ A)).injective
    (initial.hom_ext _ _)
  inv_hom_id := terminal.hom_ext _ _

noncomputable def cotensorInitial_isTerminal (A : K) : IsTerminal ((⊥_ SSet.{v} ) ⋔ A) :=
  terminalIsTerminal.ofIso (cotensorInitialIso A).symm

lemma cotensorCovMapInitial_isIso {A B : K} (f : A ⟶ B) : IsIso (cotensorCovMap (⊥_ SSet.{v}) f) :=
  isIso_of_isTerminal (cotensorInitial_isTerminal A) (cotensorInitial_isTerminal B)
    (cotensorCovMap (⊥_ SSet.{v}) f)

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.
noncomputable def cotensorToTerminalIso (U : SSet) {T : K} (hT : IsConicalTerminal SSet T) :
    U ⋔ T ≅ ⊤_ K where
  hom := terminal.from _
  inv := by
    refine (cotensor.iso.underlying U T (⊤_ K)).symm ?_
    exact (terminal.from U) ≫ (IsConicalTerminal.eHomIso SSet hT (⊤_ K)).inv
  hom_inv_id := by
    apply (cotensor.iso.underlying U T (U ⋔ T)).injective
    have : IsTerminal (sHom (U ⋔ T) T) :=
      terminalIsTerminal.ofIso (IsConicalTerminal.eHomIso SSet hT (U ⋔ T)).symm
    apply IsTerminal.hom_ext this
  inv_hom_id := terminal.hom_ext _ _

noncomputable def cotensorToConicalTerminal_isTerminal
    (U : SSet) {T : K} (hT : IsConicalTerminal SSet T) : IsTerminal (U ⋔ T) :=
  terminalIsTerminal.ofIso (cotensorToTerminalIso U hT).symm

lemma cotensorContraMapToTerminal_isIso {U V : SSet} (i : U ⟶ V)
    {T : K} (hT : IsConicalTerminal SSet T) : IsIso (cotensorContraMap i T) :=
  isIso_of_isTerminal (cotensorToConicalTerminal_isTerminal V hT)
    (cotensorToConicalTerminal_isTerminal U hT) (cotensorContraMap i T)

lemma cotensorInitialSquare_isPullback (V : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsPullback (terminal.from (V ⋔ B) ≫ (cotensorInitialIso A).inv) (𝟙 _)
      (cotensorCovMap (⊥_ SSet.{v}) f.1) (cotensorContraMap (initial.to V) B) := by
  have := cotensorCovMapInitial_isIso f.1
  refine IsPullback.of_vert_isIso ?_
  constructor
  apply IsTerminal.hom_ext (cotensorInitial_isTerminal _)

theorem cotensorCovMap_fibrant (V : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsIsofibration (cotensorCovMap V f.1) := by
  have := IsPullback.lift_snd
    (cotensorInitialSquare_isPullback V f) (cotensorContraMap (initial.to V) A)
    (cotensorCovMap V f.1) (cotensor_bifunctoriality (initial.to V) f.1)
  rw [← this, comp_id]
  exact
    (leibniz_cotensor_isIsofibration (initial.to V) f _ _ (cotensorInitialSquare_isPullback V f))

/-- An explicit isofibration obtained by cotensoring `V` with an isofibration `f`. -/
noncomputable def cotensorCovIsofibration (V : SSet.{v}) {A B : K} (f : A ↠ B) : V ⋔ A ↠ V ⋔ B :=
  ⟨cotensorCovMap V f.1, cotensorCovMap_fibrant V f⟩

@[simp]
lemma cotensorCovIsofibration_map (V : SSet.{v}) {A B : K} (f : A ↠ B) :
    (cotensorCovIsofibration V f).1 = cotensorCovMap V f.1 := rfl

lemma cotensorTerminalSquare_isPullback {U V : SSet.{v}} (i : U ⟶ V) (A : K) :
    IsPullback
      (𝟙 _) (terminal.from (U ⋔ A) ≫ (cotensorToTerminalIso V terminalIsConicalTerminal).inv)
      (cotensorCovMap U (terminal.from A)) (cotensorContraMap i (⊤_ K)) := by
  have := cotensorContraMapToTerminal_isIso i (T := ⊤_ K) terminalIsConicalTerminal
  refine IsPullback.of_horiz_isIso ?_
  constructor
  apply IsTerminal.hom_ext (cotensorToConicalTerminal_isTerminal U terminalIsConicalTerminal)

theorem cotensorContraMap_fibrant {U V : SSet} (i : U ⟶ V) [Mono i] (A : K) :
    IsIsofibration (cotensorContraMap i A) := by
  have := IsPullback.lift_fst
    (cotensorTerminalSquare_isPullback i A) (cotensorContraMap i A)
    (cotensorCovMap V (terminal.from A)) (cotensor_bifunctoriality i (terminal.from A))
  rw [← this, comp_id]
  exact (leibniz_cotensor_isIsofibration i (toTerminalIsofibration A) _ _
    (cotensorTerminalSquare_isPullback i A))

/-- An explicit isofibration obtained by cotensoring a monomorphism `i` with `A`. -/
noncomputable def cotensorContraIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (A : K) :
    V ⋔ A ↠ U ⋔ A := ⟨cotensorContraMap i A, cotensorContraMap_fibrant i A⟩

@[simp]
lemma cotensorContraIsofibration_map {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (A : K) :
    (cotensorContraIsofibration i A).1 = cotensorContraMap i A := rfl

/-- An explicit choice of codomain for the Leibniz cotensor of a monomorphism and an
isofibration. -/
@[nolint unusedArguments]
noncomputable def leibnizCotensorCod {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    K := by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) := by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback (cotensorCovMap U f.1) (cotensorContraMap i B)

/-- An explicit choice of the top map in the Leibniz pullback square. -/
noncomputable def leibnizCotensor.fst {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    leibnizCotensorCod i f ⟶ U ⋔ A := by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) := by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.fst (cotensorCovMap U f.1) (cotensorContraMap i B)

/-- An explicit choice of the left map in the Leibniz pullback square. -/
noncomputable def leibnizCotensor.snd {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    leibnizCotensorCod i f ⟶ V ⋔ B := by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) := by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.snd (cotensorCovMap U f.1) (cotensorContraMap i B)

/-- An explicitly chosen Leibniz pullback square, as a commutative square . -/
noncomputable def leibnizCotensor.commSq {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : A ↠ B) : CommSq (leibnizCotensor.fst i f) (leibnizCotensor.snd i f)
                    (cotensorCovMap U f.1) (cotensorContraMap i B) := by
  constructor
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) := by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.condition

/-- An explicitly chosen Leibniz pullback square. -/
noncomputable def leibnizCotensor.isPullback {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : A ↠ B) : IsPullback (leibnizCotensor.fst i f) (leibnizCotensor.snd i f)
                    (cotensorCovMap U f.1) (cotensorContraMap i B) := by
  refine ⟨leibnizCotensor.commSq i f, ?_⟩
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) := by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  refine IsPullback.isLimit' ?_
  apply IsPullback.of_hasPullback

/-- Covariant representables preserve the chosen Leibniz cotensor pullback square. -/
theorem leibnizCotensor.representableIsPullback {U V : SSet.{v}} (i : U ⟶ V)
    [Mono i] {A B : K} (f : A ↠ B) (X : K) :
    IsPullback (representableMap X (leibnizCotensor.fst i f))
      (representableMap X (leibnizCotensor.snd i f))
      (representableMap X (cotensorCovMap U f.1))
      (representableMap X (cotensorContraMap i B)) := by
  haveI : HasConicalPullback SSet (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
  change IsPullback ((eCoyoneda SSet X).map (leibnizCotensor.fst i f))
    ((eCoyoneda SSet X).map (leibnizCotensor.snd i f))
    ((eCoyoneda SSet X).map (cotensorCovMap U f.1))
    ((eCoyoneda SSet X).map (cotensorContraMap i B))
  exact (leibnizCotensor.isPullback i f).map (eCoyoneda SSet X)

/-- An explicitly chosen Leibniz pullback square, as a pullback cone. -/
@[nolint unusedArguments]
noncomputable def leibnizCotensor.pullbackCone {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : A ↠ B) : PullbackCone (cotensorCovMap U f.1) (cotensorContraMap i B) := by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) := by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.cone (cotensorCovMap U f.1) (cotensorContraMap i B)

/-- An explicitly chosen Leibniz cotensor map of a monomorphism `i` with an isofibration `f`. -/
noncomputable def leibnizCotensorMap {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    V ⋔ A ⟶ leibnizCotensorCod i f :=
  IsPullback.lift (leibnizCotensor.isPullback i f) (cotensorContraMap i A) (cotensorCovMap V f.1)
    (cotensor_bifunctoriality i f.1)

/-- An explicitly chosen Leibniz cotensor isofibration of a monomorphism `i` with an isofibration
`f`. -/
noncomputable def leibnizCotensorIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : A ↠ B) : V ⋔ A ↠ leibnizCotensorCod i f :=
  ⟨leibnizCotensorMap i f, leibniz_cotensor_isIsofibration _ _ _ _ _⟩

lemma leibnizCotensorIsofibration_map {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    (leibnizCotensorIsofibration i f).1 = leibnizCotensorMap i f := rfl

/-- The source vertex inclusion of the coherent isomorphism is a monomorphism. -/
instance coherentIsoSrc_mono : Mono SSet.coherentIso.src := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b _h
  apply (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := n)).injective
  apply SimplexCategory.Hom.ext
  ext x
  have ha : ((SSet.stdSimplex.objEquiv a).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  have hb : ((SSet.stdSimplex.objEquiv b).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  rw [ha, hb]

/-- The target vertex inclusion of the coherent isomorphism is a monomorphism. -/
instance coherentIsoTgt_mono : Mono SSet.coherentIso.tgt := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b _h
  apply (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := n)).injective
  apply SimplexCategory.Hom.ext
  ext x
  have ha : ((SSet.stdSimplex.objEquiv a).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  have hb : ((SSet.stdSimplex.objEquiv b).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  rw [ha, hb]

/-- The map into the point cotensor corresponding to an ordinary morphism. -/
noncomputable def cotensorPointMap {A B : K} (f : A ⟶ B) : A ⟶ (Δ[0] : SSet.{v}) ⋔ B :=
  (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A).symm
    (SSet.pointIsUnit.hom ≫
      (eHomEquiv SSet f : MonoidalCategoryStruct.tensorUnit SSet ⟶ sHom A B))

/-- The map from the point cotensor to the underlying object, inverse to `cotensorPointMap (𝟙 B)`. -/
noncomputable def cotensorPointIsoHom (B : K) : (Δ[0] : SSet.{v}) ⋔ B ⟶ B :=
  (eHomEquiv SSet).symm (SSet.pointIsUnit.inv ≫ cotensor.cone (Δ[0] : SSet.{v}) B)

/-- The enriched morphism corresponding to `cotensorPointIsoHom`. -/
lemma cotensorPointIsoHom_homEquiv (B : K) :
    eHomEquiv SSet (cotensorPointIsoHom B) =
      SSet.pointIsUnit.inv ≫ cotensor.cone (Δ[0] : SSet.{v}) B := by
  simp [cotensorPointIsoHom]

/-- The underlying map represented by `cotensorPointMap`. -/
lemma cotensorPointMap_underlying {A B : K} (f : A ⟶ B) :
    (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A) (cotensorPointMap f) =
      SSet.pointIsUnit.hom ≫ eHomEquiv SSet f := by
  simp [cotensorPointMap]

/-- Composing a point-cotensor map with the point-cotensor comparison recovers the original map. -/
lemma cotensorPointMap_comp_cotensorPointIsoHom {A B : K} (f : A ⟶ B) :
    cotensorPointMap f ≫ cotensorPointIsoHom B = f := by
  apply (eHomEquiv SSet).injective
  rw [← eHomEquiv_comp_eHomWhiskerRight]
  rw [cotensorPointIsoHom_homEquiv]
  rw [Category.assoc]
  have hmap := cotensorPointMap_underlying f
  rw [cotensor_iso_underlying_eq_cone] at hmap
  change SSet.pointIsUnit.inv ≫
      ((getCotensor (Δ[0] : SSet.{v}) B).cone ≫
        eHomWhiskerRight SSet (cotensorPointMap f) B) =
    (eHomEquiv SSet) f
  rw [hmap]
  rw [← Category.assoc, SSet.pointIsUnit.inv_hom_id, Category.id_comp]

/-- One inverse identity for the point-cotensor comparison. -/
lemma cotensorPointIso_hom_inv_id (B : K) :
    cotensorPointIsoHom B ≫ cotensorPointMap (𝟙 B) = 𝟙 ((Δ[0] : SSet.{v}) ⋔ B) := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B ((Δ[0] : SSet.{v}) ⋔ B)).injective
  rw [cotensor_iso_underlying_eq_cone]
  rw [cotensor_iso_underlying_eq_cone]
  rw [eHomWhiskerRight_comp]
  change (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      (eHomWhiskerRight SSet (cotensorPointMap (𝟙 B)) B ≫
        eHomWhiskerRight SSet (cotensorPointIsoHom B) B) =
    (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eHomWhiskerRight SSet (𝟙 ((Δ[0] : SSet.{v}) ⋔ B)) B
  rw [← Category.assoc]
  have hmap := cotensorPointMap_underlying (𝟙 B)
  rw [cotensor_iso_underlying_eq_cone] at hmap
  rw [hmap, Category.assoc, eHomEquiv_comp_eHomWhiskerRight, Category.comp_id,
    cotensorPointIsoHom_homEquiv]
  rw [← Category.assoc, SSet.pointIsUnit.hom_inv_id, Category.id_comp, eHomWhiskerRight_id]
  change (getCotensor (Δ[0] : SSet.{v}) B).cone =
    (getCotensor (Δ[0] : SSet.{v}) B).cone ≫ 𝟙 _
  rw [Category.comp_id]

/-- The other inverse identity for the point-cotensor comparison. -/
lemma cotensorPointIso_inv_hom_id (B : K) :
    cotensorPointMap (𝟙 B) ≫ cotensorPointIsoHom B = 𝟙 B :=
  cotensorPointMap_comp_cotensorPointIsoHom (𝟙 B)

/-- The point cotensor is isomorphic to the original object. -/
noncomputable def cotensorPointIso (B : K) : (Δ[0] : SSet.{v}) ⋔ B ≅ B where
  hom := cotensorPointIsoHom B
  inv := cotensorPointMap (𝟙 B)
  hom_inv_id := cotensorPointIso_hom_inv_id B
  inv_hom_id := cotensorPointIso_inv_hom_id B

set_option backward.isDefEq.respectTransparency false in
/-- On representables, the point-cotensor comparison evaluates the cotensor isomorphism at the
unique point of `Δ[0]`. -/
lemma representableMap_cotensorPointIsoHom {B : K} (X : K) :
    representableMap X (cotensorPointIsoHom B) =
      (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫ (sHom X B).expPointIsoSelf.hom := by
  change eHomWhiskerLeft SSet X (cotensorPointIsoHom B) =
    (getCotensor (Δ[0] : SSet.{v}) B).coneNatTrans X ≫
      (sHom X B).expPointIsoSelf.hom
  let point : SSet.{v} := Δ[0]
  let Cobj : K := (getCotensor point B).obj
  let Y : SSet.{v} := sHom X Cobj
  let cone := (getCotensor point B).cone
  let H := (β_ point Y).hom ≫ (Y ◁ cone) ≫ eComp SSet X Cobj B
  have hcone : (getCotensor point B).coneNatTrans X =
      MonoidalClosed.curry H := by
    apply MonoidalClosed.uncurry_injective (A := point)
    dsimp [H]
    rw [(getCotensor point B).toPrecotensor.coneNatTrans_eq]
    rw [MonoidalClosed.uncurry_curry]
  rw [hcone]
  rw [SSet.curry_expPointIsoSelf_hom]
  dsimp [H]
  change eHomWhiskerLeft SSet X (cotensorPointIsoHom B) =
    (λ_ (sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj)).inv ≫
      (SSet.pointIsUnit.inv ▷ sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj) ≫
      (β_ (Δ[0] : SSet.{v}) (sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj)).hom ≫
      (sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj) ◁
        (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B
  dsimp [eHomWhiskerLeft]
  rw [cotensorPointIsoHom_homEquiv]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  let Y : SSet.{v} := sHom X (getCotensor (Δ[0] : SSet.{v}) B).obj
  change ((ρ_ Y).inv ≫ Y ◁ SSet.pointIsUnit.inv) ≫
      Y ◁ (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B =
    ((λ_ Y).inv ≫ SSet.pointIsUnit.inv ▷ Y ≫
      (β_ (Δ[0] : SSet.{v}) Y).hom) ≫
      Y ◁ (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ Y ◁ (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
      eComp SSet X (getCotensor (Δ[0] : SSet.{v}) B).obj B)
    (SSet.rightUnitor_inv_pointIsUnit_inv Y)

set_option backward.isDefEq.respectTransparency false in
/-- On representables, `cotensorPointMap` is the original map followed by the inverse
point-evaluation isomorphism. -/
lemma representableMap_cotensorPointMap_hom {A B : K} (f : A ⟶ B) (X : K) :
    representableMap X (cotensorPointMap f) ≫ (cotensor.iso (Δ[0] : SSet.{v}) B X).hom =
      representableMap X f ≫ (sHom X B).expPointIsoSelf.inv := by
  apply (cancel_mono (sHom X B).expPointIsoSelf.hom).mp
  calc
    (representableMap X (cotensorPointMap f) ≫
        (cotensor.iso (Δ[0] : SSet.{v}) B X).hom) ≫
        (sHom X B).expPointIsoSelf.hom =
      representableMap X (cotensorPointMap f) ≫ representableMap X (cotensorPointIsoHom B) := by
        rw [Category.assoc, representableMap_cotensorPointIsoHom]
    _ = representableMap X (cotensorPointMap f ≫ cotensorPointIsoHom B) := by
        rw [representableMap_comp]
    _ = representableMap X f := by
        rw [cotensorPointMap_comp_cotensorPointIsoHom]
    _ = (representableMap X f ≫ (sHom X B).expPointIsoSelf.inv) ≫
        (sHom X B).expPointIsoSelf.hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The map on representables induced by source evaluation from the coherent-isomorphism cotensor
is a quasi-category equivalence. -/
noncomputable def representableCotensorContraMapCoherentIsoSrcEquiv (B X : K) :
    @QCat.Equiv (Fun X (SSet.coherentIso ⋔ B)).obj (Fun X ((Δ[0] : SSet.{v}) ⋔ B)).obj
      (Fun X (SSet.coherentIso ⋔ B)).property (Fun X ((Δ[0] : SSet.{v}) ⋔ B)).property := by
  let eA : (Fun X (SSet.coherentIso ⋔ B)).obj ≅
      SSet.pathSpace (I := SSet.coherentIso) (sHom X B) :=
    cotensor.iso SSet.coherentIso B X
  let eB : (Fun X ((Δ[0] : SSet.{v}) ⋔ B)).obj ≅ sHom X B :=
    cotensor.iso (Δ[0] : SSet.{v}) B X ≪≫ (sHom X B).expPointIsoSelf
  exact SSet.Equiv.congrIso (I := SSet.coherentIso) eA eB
    (SSet.pathSpace.srcEquiv (sHom X B))

/-- The forward map of `representableCotensorContraMapCoherentIsoSrcEquiv` is the representable
of `cotensorContraMap SSet.coherentIso.src B`. -/
lemma representableCotensorContraMapCoherentIsoSrcEquiv_toFun (B X : K) :
    (representableCotensorContraMapCoherentIsoSrcEquiv B X).toFun =
      representableMap X (cotensorContraMap SSet.coherentIso.src B) := by
  dsimp [representableCotensorContraMapCoherentIsoSrcEquiv, SSet.Equiv.congrIso,
    SSet.pathSpace.srcEquiv]
  let eB : (Fun X ((Δ[0] : SSet.{v}) ⋔ B)).obj ≅ sHom X B :=
    cotensor.iso (Δ[0] : SSet.{v}) B X ≪≫ (sHom X B).expPointIsoSelf
  apply (cancel_mono eB.hom).mp
  dsimp [eB]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  rw [Iso.inv_hom_id]
  simp only [Category.comp_id]
  calc
    (cotensor.iso SSet.coherentIso B X).hom ≫ SSet.pathSpace.src (sHom X B) =
        ((cotensor.iso SSet.coherentIso B X).hom ≫
          (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B)) ≫
          (sHom X B).expPointIsoSelf.hom := rfl
    _ = (representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
          (cotensor.iso (Δ[0] : SSet.{v}) B X).hom) ≫
          (sHom X B).expPointIsoSelf.hom := by
          exact congrArg (fun q => q ≫ (sHom X B).expPointIsoSelf.hom)
            (cotensor_iso_hom_naturality_precompose SSet.coherentIso.src B X).symm
    _ = representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
          ((cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫
            (sHom X B).expPointIsoSelf.hom) := by
          rw [Category.assoc]

/-- Source evaluation from the coherent-isomorphism cotensor is an equivalence in an
∞-cosmos. -/
theorem cotensorContraMap_coherentIsoSrc_equivalence (B : K) :
    Equivalence (cotensorContraMap SSet.coherentIso.src B) := by
  intro X
  exact ⟨representableCotensorContraMapCoherentIsoSrcEquiv B X,
    representableCotensorContraMapCoherentIsoSrcEquiv_toFun B X⟩

/-- Source evaluation from the coherent-isomorphism cotensor is a trivial fibration in an
∞-cosmos. -/
theorem cotensorContraMap_coherentIsoSrc_trivialFibration (B : K) :
    TrivialFibration (cotensorContraMap SSet.coherentIso.src B) :=
  ⟨cotensorContraMap_fibrant SSet.coherentIso.src B,
    cotensorContraMap_coherentIsoSrc_equivalence B⟩

/-- The constant coherent-isomorphism path corresponding to an ordinary morphism. -/
noncomputable def coherentIsoPathMap {A B : K} (f : A ⟶ B) : A ⟶ SSet.coherentIso ⋔ B :=
  (cotensor.iso.underlying SSet.coherentIso B A).symm
    ((SSet.isTerminalDeltaZero.from SSet.coherentIso ≫ SSet.pointIsUnit.hom) ≫
      (eHomEquiv SSet f : MonoidalCategoryStruct.tensorUnit SSet ⟶ sHom A B))

/-- The source endpoint of the constant coherent-isomorphism path is `f`. -/
lemma coherentIsoPathMap_src {A B : K} (f : A ⟶ B) :
    coherentIsoPathMap f ≫ cotensorContraMap SSet.coherentIso.src B = cotensorPointMap f := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A).injective
  rw [cotensor_iso_underlying_precompose]
  simp [coherentIsoPathMap, cotensorPointMap]
  have hsrc :
      SSet.coherentIso.src ≫ SSet.isTerminalDeltaZero.from SSet.coherentIso =
        𝟙 (Δ[0] : SSet.{v}) :=
    SSet.isTerminalDeltaZero.hom_ext _ _
  rw [← Category.assoc, hsrc, Category.id_comp]

/-- The target endpoint of the constant coherent-isomorphism path is also `f`. -/
lemma coherentIsoPathMap_tgt {A B : K} (f : A ⟶ B) :
    coherentIsoPathMap f ≫ cotensorContraMap SSet.coherentIso.tgt B = cotensorPointMap f := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A).injective
  rw [cotensor_iso_underlying_precompose]
  simp [coherentIsoPathMap, cotensorPointMap]
  have htgt :
      SSet.coherentIso.tgt ≫ SSet.isTerminalDeltaZero.from SSet.coherentIso =
        𝟙 (Δ[0] : SSet.{v}) :=
    SSet.isTerminalDeltaZero.hom_ext _ _
  rw [← Category.assoc, htgt, Category.id_comp]

lemma representableMap_coherentIsoPathMap_src_cotensor {A B : K} (f : A ⟶ B) (X : K) :
    (representableMap X (coherentIsoPathMap f) ≫ (cotensor.iso SSet.coherentIso B X).hom) ≫
        (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) =
      representableMap X (cotensorPointMap f) ≫
        (cotensor.iso (Δ[0] : SSet.{v}) B X).hom := by
  rw [Category.assoc]
  rw [(cotensor_iso_hom_naturality_precompose SSet.coherentIso.src B X).symm]
  change representableMap X (coherentIsoPathMap f) ≫
      representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
      (cotensor.iso (Δ[0] : SSet.{v}) B X).hom =
    representableMap X (cotensorPointMap f) ≫
      (cotensor.iso (Δ[0] : SSet.{v}) B X).hom
  rw [← Category.assoc, ← representableMap_comp, coherentIsoPathMap_src]

set_option backward.isDefEq.respectTransparency false in
/-- On representables, the constant coherent-isomorphism path is the constant path in the
corresponding hom quasi-category. -/
lemma representableMap_coherentIsoPathMap_const {A B : K} (f : A ⟶ B) (X : K) :
    representableMap X (coherentIsoPathMap f) ≫ (cotensor.iso SSet.coherentIso B X).hom =
      representableMap X f ≫ SSet.pathSpace.const (I := SSet.coherentIso) (sHom X B) := by
  change representableMap X (coherentIsoPathMap f) ≫ (cotensor.iso SSet.coherentIso B X).hom =
      representableMap X f ≫ (sHom X B).expPointIsoSelf.inv ≫
        (MonoidalClosed.pre
          (SSet.isTerminalDeltaZero.from SSet.coherentIso : SSet.coherentIso ⟶ Δ[0])).app
          (sHom X B)
  apply MonoidalClosed.uncurry_injective (A := SSet.coherentIso)
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_pre_app]
  change SSet.coherentIso ◁ representableMap X (coherentIsoPathMap f) ≫
      MonoidalClosed.uncurry ((getCotensor SSet.coherentIso B).coneNatTrans X) =
    SSet.coherentIso ◁ representableMap X f ≫
      (SSet.isTerminalDeltaZero.from SSet.coherentIso ▷ sHom X B) ≫
      MonoidalClosed.uncurry (sHom X B).expPointIsoSelf.inv
  rw [(getCotensor SSet.coherentIso B).toPrecotensor.coneNatTrans_eq]
  dsimp [representableMap, representableMap']
  change SSet.coherentIso ◁ eHomWhiskerLeft SSet X (coherentIsoPathMap f) ≫
      (β_ SSet.coherentIso (sHom X (SSet.coherentIso ⋔ B))).hom ≫
      (sHom X (SSet.coherentIso ⋔ B)) ◁ (cotensor.cone SSet.coherentIso B) ≫
      eComp SSet X (SSet.coherentIso ⋔ B) B =
    SSet.coherentIso ◁ eHomWhiskerLeft SSet X f ≫
      SSet.isTerminalDeltaZero.from SSet.coherentIso ▷ sHom X B ≫
      MonoidalClosed.uncurry (sHom X B).expPointIsoSelf.inv
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  rw [eComp_eHomWhisker_middle]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have hpath := cotensor_iso_underlying_eq_cone (U := SSet.coherentIso) B A
    (coherentIsoPathMap f)
  change (β_ SSet.coherentIso (X ⟶[SSet] A)).hom ≫
      (X ⟶[SSet] A) ◁ ((getCotensor SSet.coherentIso B).cone ≫
        eHomWhiskerRight SSet (coherentIsoPathMap f) B) ≫
      eComp SSet X A B = _
  rw [← hpath]
  dsimp [coherentIsoPathMap]
  simp only [Equiv.apply_symm_apply]
  dsimp [eHomWhiskerLeft]
  simp only [Category.assoc]
  rw [SSet.uncurry_expPointIsoSelf_inv]
  ext n x
  cases n using Opposite.rec
  rcases x with ⟨i, a⟩
  simp [SSet.pointIsUnit]
  rfl

/-- The pullback used to define the Brown factorization object exists. -/
noncomputable instance brownFactorization_hasPullback {A B : K} (f : A ⟶ B) :
    HasPullback (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f) := by
  have : HasConicalPullback SSet
      (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f) := by
    exact has_isofibration_pullbacks (cotensorContraIsofibration SSet.coherentIso.src B)
      (cotensorPointMap f)
  infer_instance

/-- The Brown factorization pullback object, before identifying `Δ[0] ⋔ B` with `B`. -/
noncomputable def brownFactorizationObj {A B : K} (f : A ⟶ B) : K :=
  pullback (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f)

/-- The projection from the Brown factorization object to the coherent-isomorphism path object. -/
noncomputable def brownFactorizationPath {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ SSet.coherentIso ⋔ B :=
  pullback.fst (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f)

/-- The left projection from the Brown factorization object. -/
noncomputable def brownFactorizationLeft {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ A :=
  pullback.snd (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f)

/-- The defining Brown factorization square is a pullback square. -/
lemma brownFactorization_isPullback {A B : K} (f : A ⟶ B) :
    IsPullback (brownFactorizationPath f) (brownFactorizationLeft f)
      (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f) := by
  unfold brownFactorizationPath brownFactorizationLeft brownFactorizationObj
  exact IsPullback.of_hasPullback _ _

/-- Covariant representables preserve the Brown factorization pullback square. -/
lemma brownFactorization_representableIsPullback {A B : K} (f : A ⟶ B) (X : K) :
    IsPullback
      (representableMap X (brownFactorizationPath f))
      (representableMap X (brownFactorizationLeft f))
      (representableMap X (cotensorContraMap SSet.coherentIso.src B))
      (representableMap X (cotensorPointMap f)) := by
  haveI : HasConicalPullback SSet
      (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f) :=
    has_isofibration_pullbacks (cotensorContraIsofibration SSet.coherentIso.src B)
      (cotensorPointMap f)
  change IsPullback
    ((eCoyoneda SSet X).map (brownFactorizationPath f))
    ((eCoyoneda SSet X).map (brownFactorizationLeft f))
    ((eCoyoneda SSet X).map (cotensorContraMap SSet.coherentIso.src B))
    ((eCoyoneda SSet X).map (cotensorPointMap f))
  exact (brownFactorization_isPullback f).map (eCoyoneda SSet X)

/-- The left projection in the Brown factorization is an isofibration. -/
lemma brownFactorizationLeft_isIsofibration {A B : K} (f : A ⟶ B) :
    IsIsofibration (brownFactorizationLeft f) :=
  pullback_isIsofibration (cotensorContraIsofibration SSet.coherentIso.src B)
    (cotensorPointMap f) (brownFactorizationPath f) (brownFactorizationLeft f)
    (brownFactorization_isPullback f)

/-- The right endpoint map from the Brown factorization object, valued in the point cotensor. -/
noncomputable def brownFactorizationRightPoint {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ (Δ[0] : SSet.{v}) ⋔ B :=
  brownFactorizationPath f ≫ cotensorContraMap SSet.coherentIso.tgt B

/-- The section of the Brown factorization map induced by the constant path. -/
noncomputable def brownFactorizationSection {A B : K} (f : A ⟶ B) :
    A ⟶ brownFactorizationObj f :=
  pullback.lift (coherentIsoPathMap f) (𝟙 A) (by
    rw [Category.id_comp, coherentIsoPathMap_src])

/-- The path projection of the Brown section is the constant coherent-isomorphism path. -/
lemma brownFactorizationSection_path {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationPath f = coherentIsoPathMap f := by
  unfold brownFactorizationSection brownFactorizationPath
  exact pullback.lift_fst _ _ _

/-- The left projection of the Brown section is the identity. -/
lemma brownFactorizationSection_left {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationLeft f = 𝟙 A := by
  unfold brownFactorizationSection brownFactorizationLeft
  exact pullback.lift_snd _ _ _

/-- The right endpoint of the Brown section is the point-cotensor map of `f`. -/
lemma brownFactorizationSection_rightPoint {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationRightPoint f = cotensorPointMap f := by
  rw [brownFactorizationRightPoint, ← Category.assoc, brownFactorizationSection_path,
    coherentIsoPathMap_tgt]

/-- The right map of the Brown factorization, after identifying `Δ[0] ⋔ B` with `B`. -/
noncomputable def brownFactorizationRight {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ B :=
  brownFactorizationRightPoint f ≫ (cotensorPointIso B).hom

/-- The Brown section followed by the right map is the original morphism. -/
lemma brownFactorization_fac {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationRight f = f := by
  unfold brownFactorizationRight
  rw [← Category.assoc, brownFactorizationSection_rightPoint]
  exact cotensorPointMap_comp_cotensorPointIsoHom f

/- The following private declarations build the representable homotopy witnessing that the left
projection in the Brown factorization is an equivalence. -/

private lemma tensorEndpoint_snd {I X : SSet.{v}} (endpoint : Δ[0] ⟶ I) :
    (λ_ X).inv ≫ ((SSet.pointIsUnit.inv ≫ endpoint) ▷ X) ≫
      CartesianMonoidalCategory.snd I X = 𝟙 X := by
  ext n x
  cases n using Opposite.rec
  rfl

private lemma tensorEndpoint_whiskerLeft {I X Y : SSet.{v}} (endpoint : Δ[0] ⟶ I)
    (f : X ⟶ Y) :
    (λ_ X).inv ≫ ((SSet.pointIsUnit.inv ≫ endpoint) ▷ X) ≫ (I ◁ f) =
      f ≫ (λ_ Y).inv ≫ ((SSet.pointIsUnit.inv ≫ endpoint) ▷ Y) := by
  ext n x
  · cases n using Opposite.rec
    rfl
  · cases n using Opposite.rec
    rfl

private noncomputable def brownFactorizationRepresentableHomotopyPath {A B : K}
    (f : A ⟶ B) (X : K) :
    SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) ⟶ sHom X (SSet.coherentIso ⋔ B) :=
  (SSet.coherentIso ◁
      (representableMap X (brownFactorizationPath f) ≫
        (cotensor.iso SSet.coherentIso B X).hom)) ≫
    SSet.pathSpace.srcContractionEval (sHom X B) ≫
    (cotensor.iso SSet.coherentIso B X).inv

private noncomputable def brownFactorizationRepresentableHomotopyLeft {A B : K}
    (f : A ⟶ B) (X : K) :
    SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) ⟶ sHom X A :=
  CartesianMonoidalCategory.snd SSet.coherentIso (sHom X (brownFactorizationObj f)) ≫
    representableMap X (brownFactorizationLeft f)

private lemma cotensorIso_inv_naturality_precompose {U V : SSet.{v}} (i : U ⟶ V)
    (B X : K) :
    (cotensor.iso V B X).inv ≫ representableMap X (cotensorContraMap i B) ≫
      (cotensor.iso U B X).hom =
        (MonoidalClosed.pre i).app (sHom X B) := by
  calc
    (cotensor.iso V B X).inv ≫ representableMap X (cotensorContraMap i B) ≫
        (cotensor.iso U B X).hom =
      (cotensor.iso V B X).inv ≫
        (representableMap X (cotensorContraMap i B) ≫ (cotensor.iso U B X).hom) := by
        rfl
    _ = (cotensor.iso V B X).inv ≫
        ((cotensor.iso V B X).hom ≫ (MonoidalClosed.pre i).app (sHom X B)) := by
        exact congrArg (fun q => (cotensor.iso V B X).inv ≫ q)
          (cotensor_iso_hom_naturality_precompose i B X)
    _ = (MonoidalClosed.pre i).app (sHom X B) := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma brownFactorizationRepresentableHomotopy_fac {A B : K} (f : A ⟶ B) (X : K) :
    brownFactorizationRepresentableHomotopyPath f X ≫
        representableMap X (cotensorContraMap SSet.coherentIso.src B) =
      brownFactorizationRepresentableHomotopyLeft f X ≫ representableMap X (cotensorPointMap f) := by
  let eB : sHom X ((Δ[0] : SSet.{v}) ⋔ B) ≅ sHom X B :=
    cotensor.iso (Δ[0] : SSet.{v}) B X ≪≫ (sHom X B).expPointIsoSelf
  apply (cancel_mono eB.hom).mp
  dsimp [brownFactorizationRepresentableHomotopyPath, brownFactorizationRepresentableHomotopyLeft,
    eB]
  simp only [Iso.trans_hom, Category.assoc]
  let r : SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) ⟶
      SSet.coherentIso ⊗ (ihom SSet.coherentIso).obj (sHom X B) :=
    SSet.coherentIso ◁ (representableMap X (brownFactorizationPath f) ≫
      (cotensor.iso SSet.coherentIso B X).hom)
  let q : SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) ⟶
      (ihom SSet.coherentIso).obj (sHom X B) :=
    r ≫ SSet.pathSpace.srcContractionEval (sHom X B)
  have hnat := cotensorIso_inv_naturality_precompose SSet.coherentIso.src B X
  change q ≫ (cotensor.iso SSet.coherentIso B X).inv ≫
          representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
          (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫ (sHom X B).expPointIsoSelf.hom =
    SemiCartesianMonoidalCategory.snd SSet.coherentIso (sHom X (brownFactorizationObj f)) ≫
      representableMap X (brownFactorizationLeft f) ≫
        representableMap X (cotensorPointMap f) ≫ (cotensor.iso Δ[0] B X).hom ≫
          (sHom X B).expPointIsoSelf.hom
  calc
    q ≫ (cotensor.iso SSet.coherentIso B X).inv ≫
          representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
          (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫ (sHom X B).expPointIsoSelf.hom =
        q ≫ ((cotensor.iso SSet.coherentIso B X).inv ≫
          representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
          (cotensor.iso (Δ[0] : SSet.{v}) B X).hom) ≫
          (sHom X B).expPointIsoSelf.hom := by
        simp only [Category.assoc]
    _ = q ≫ (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) ≫
          (sHom X B).expPointIsoSelf.hom := by
        rw [hnat]
  change q ≫ SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) =
    SemiCartesianMonoidalCategory.snd SSet.coherentIso (sHom X (brownFactorizationObj f)) ≫
      representableMap X (brownFactorizationLeft f) ≫
        representableMap X (cotensorPointMap f) ≫ (cotensor.iso Δ[0] B X).hom ≫
          (sHom X B).expPointIsoSelf.hom
  dsimp [q]
  calc
    (r ≫ SSet.pathSpace.srcContractionEval (sHom X B)) ≫
        SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) =
      r ≫ (SSet.pathSpace.srcContractionEval (sHom X B) ≫
        SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B)) := by
        rw [Category.assoc]
    _ = r ≫ (CartesianMonoidalCategory.snd SSet.coherentIso
        (SSet.pathSpace (I := SSet.coherentIso) (sHom X B)) ≫
        SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B)) := by
        rw [SSet.pathSpace.srcContractionEval_path_src]
    _ =
      SemiCartesianMonoidalCategory.snd SSet.coherentIso (sHom X (brownFactorizationObj f)) ≫
        representableMap X (brownFactorizationLeft f) ≫
          representableMap X (cotensorPointMap f) ≫ (cotensor.iso Δ[0] B X).hom ≫
            (sHom X B).expPointIsoSelf.hom := by
      dsimp [r]
      calc
        (SSet.coherentIso ◁
              (representableMap X (brownFactorizationPath f) ≫
                (cotensor.iso SSet.coherentIso B X).hom)) ≫
            CartesianMonoidalCategory.snd SSet.coherentIso
              ((ihom SSet.coherentIso).obj (sHom X B)) ≫
            SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) =
          SemiCartesianMonoidalCategory.snd SSet.coherentIso (sHom X (brownFactorizationObj f)) ≫
            (representableMap X (brownFactorizationPath f) ≫
              (cotensor.iso SSet.coherentIso B X).hom) ≫
            SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) := by
          change (SSet.coherentIso ◁
                (representableMap X (brownFactorizationPath f) ≫
                  (cotensor.iso SSet.coherentIso B X).hom)) ≫
              CartesianMonoidalCategory.snd SSet.coherentIso
                ((ihom SSet.coherentIso).obj (sHom X B)) ≫
              ((MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) ≫
                (sHom X B).expPointIsoSelf.hom) =
            SemiCartesianMonoidalCategory.snd SSet.coherentIso
              (sHom X (brownFactorizationObj f)) ≫
              (representableMap X (brownFactorizationPath f) ≫
                (cotensor.iso SSet.coherentIso B X).hom) ≫
              ((MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) ≫
                (sHom X B).expPointIsoSelf.hom)
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) ≫
              (sHom X B).expPointIsoSelf.hom)
            (CartesianMonoidalCategory.whiskerLeft_snd SSet.coherentIso
              (representableMap X (brownFactorizationPath f) ≫
                (cotensor.iso SSet.coherentIso B X).hom))
        _ = SemiCartesianMonoidalCategory.snd SSet.coherentIso (sHom X (brownFactorizationObj f)) ≫
            representableMap X (brownFactorizationPath f) ≫
            representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
            (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫
            (sHom X B).expPointIsoSelf.hom := by
          have hsrc : representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
              (cotensor.iso (Δ[0] : SSet.{v}) B X).hom =
                (cotensor.iso SSet.coherentIso B X).hom ≫
                  (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) := by
            change eHomWhiskerLeft SSet X (cotensorContraMap SSet.coherentIso.src B) ≫
              (cotensor.iso (Δ[0] : SSet.{v}) B X).hom =
                (cotensor.iso SSet.coherentIso B X).hom ≫
                  (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B)
            exact cotensor_iso_hom_naturality_precompose SSet.coherentIso.src B X
          change SemiCartesianMonoidalCategory.snd SSet.coherentIso
              (sHom X (brownFactorizationObj f)) ≫
            representableMap X (brownFactorizationPath f) ≫
            ((cotensor.iso SSet.coherentIso B X).hom ≫
              (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) ≫
              (sHom X B).expPointIsoSelf.hom) = _
          simpa only [Category.assoc] using congrArg
            (fun q => SemiCartesianMonoidalCategory.snd SSet.coherentIso
              (sHom X (brownFactorizationObj f)) ≫
              representableMap X (brownFactorizationPath f) ≫ q ≫
              (sHom X B).expPointIsoSelf.hom) hsrc.symm
        _ = SemiCartesianMonoidalCategory.snd SSet.coherentIso (sHom X (brownFactorizationObj f)) ≫
            representableMap X (brownFactorizationLeft f) ≫
            representableMap X (cotensorPointMap f) ≫
            (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫
            (sHom X B).expPointIsoSelf.hom := by
          simpa only [Category.assoc] using congrArg
            (fun q => SemiCartesianMonoidalCategory.snd SSet.coherentIso
              (sHom X (brownFactorizationObj f)) ≫ q ≫
              (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫
              (sHom X B).expPointIsoSelf.hom)
            (brownFactorization_representableIsPullback f X).w

private noncomputable def brownFactorizationRepresentableHomotopy {A B : K}
    (f : A ⟶ B) (X : K) :
    SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) ⟶
      sHom X (brownFactorizationObj f) :=
  IsPullback.lift (brownFactorization_representableIsPullback f X)
    (brownFactorizationRepresentableHomotopyPath f X)
    (brownFactorizationRepresentableHomotopyLeft f X)
    (brownFactorizationRepresentableHomotopy_fac f X)

private lemma brownFactorizationRepresentableHomotopy_path {A B : K} (f : A ⟶ B) (X : K) :
    brownFactorizationRepresentableHomotopy f X ≫ representableMap X (brownFactorizationPath f) =
      brownFactorizationRepresentableHomotopyPath f X := by
  exact IsPullback.lift_fst (brownFactorization_representableIsPullback f X)
    (brownFactorizationRepresentableHomotopyPath f X)
    (brownFactorizationRepresentableHomotopyLeft f X)
    (brownFactorizationRepresentableHomotopy_fac f X)

private lemma brownFactorizationRepresentableHomotopy_left {A B : K} (f : A ⟶ B) (X : K) :
    brownFactorizationRepresentableHomotopy f X ≫ representableMap X (brownFactorizationLeft f) =
      brownFactorizationRepresentableHomotopyLeft f X := by
  exact IsPullback.lift_snd (brownFactorization_representableIsPullback f X)
    (brownFactorizationRepresentableHomotopyPath f X)
    (brownFactorizationRepresentableHomotopyLeft f X)
    (brownFactorizationRepresentableHomotopy_fac f X)

private lemma brownFactorizationRepresentableHomotopy_tgt {A B : K} (f : A ⟶ B) (X : K) :
    (λ_ (sHom X (brownFactorizationObj f))).inv ≫
        ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
          sHom X (brownFactorizationObj f)) ≫
        brownFactorizationRepresentableHomotopy f X =
      𝟙 (sHom X (brownFactorizationObj f)) := by
  apply IsPullback.hom_ext (brownFactorization_representableIsPullback f X)
  · calc
      ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
          ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
            sHom X (brownFactorizationObj f)) ≫
          brownFactorizationRepresentableHomotopy f X) ≫
          representableMap X (brownFactorizationPath f) =
        ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
          ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
            sHom X (brownFactorizationObj f))) ≫
          brownFactorizationRepresentableHomotopyPath f X := by
          simpa only [Category.assoc] using congrArg
            (fun q => ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
              ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
                sHom X (brownFactorizationObj f))) ≫ q)
            (brownFactorizationRepresentableHomotopy_path f X)
      _ = representableMap X (brownFactorizationPath f) := by
          dsimp [brownFactorizationRepresentableHomotopyPath]
          let m : sHom X (brownFactorizationObj f) ⟶
              SSet.pathSpace (I := SSet.coherentIso) (sHom X B) :=
            representableMap X (brownFactorizationPath f) ≫
              (cotensor.iso SSet.coherentIso B X).hom
          change ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
              ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
                sHom X (brownFactorizationObj f))) ≫
              ((SSet.coherentIso ◁ m) ≫
                SSet.pathSpace.srcContractionEval (sHom X B) ≫
                (cotensor.iso SSet.coherentIso B X).inv) =
            representableMap X (brownFactorizationPath f)
          calc
            ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
                ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
                  sHom X (brownFactorizationObj f))) ≫
                ((SSet.coherentIso ◁ m) ≫
                  SSet.pathSpace.srcContractionEval (sHom X B) ≫
                  (cotensor.iso SSet.coherentIso B X).inv) =
              (((λ_ (sHom X (brownFactorizationObj f))).inv ≫
                ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
                  sHom X (brownFactorizationObj f))) ≫
                (SSet.coherentIso ◁ m)) ≫
                  SSet.pathSpace.srcContractionEval (sHom X B) ≫
                  (cotensor.iso SSet.coherentIso B X).inv := by
                simp only [Category.assoc]
            _ = (m ≫ (λ_ (SSet.pathSpace (I := SSet.coherentIso) (sHom X B))).inv ≫
                ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
                  SSet.pathSpace (I := SSet.coherentIso) (sHom X B))) ≫
                  SSet.pathSpace.srcContractionEval (sHom X B) ≫
                  (cotensor.iso SSet.coherentIso B X).inv := by
                simpa only [Category.assoc] using congrArg
                  (fun q => q ≫ SSet.pathSpace.srcContractionEval (sHom X B) ≫
                    (cotensor.iso SSet.coherentIso B X).inv)
                  (tensorEndpoint_whiskerLeft SSet.coherentIso.tgt m)
            _ = m ≫ ((λ_ (SSet.pathSpace (I := SSet.coherentIso) (sHom X B))).inv ≫
                ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
                  SSet.pathSpace (I := SSet.coherentIso) (sHom X B)) ≫
                  SSet.pathSpace.srcContractionEval (sHom X B)) ≫
                  (cotensor.iso SSet.coherentIso B X).inv := by
                simp only [Category.assoc]
            _ = m ≫ 𝟙 _ ≫ (cotensor.iso SSet.coherentIso B X).inv := by
                rw [SSet.pathSpace.srcContractionEval_tgt]
            _ = representableMap X (brownFactorizationPath f) := by
                dsimp [m]
                change (representableMap X (brownFactorizationPath f) ≫
                    (cotensor.iso SSet.coherentIso B X).hom) ≫
                    𝟙 ((ihom SSet.coherentIso).obj (sHom X B)) ≫
                    (cotensor.iso SSet.coherentIso B X).inv =
                  representableMap X (brownFactorizationPath f)
                calc
                  (representableMap X (brownFactorizationPath f) ≫
                      (cotensor.iso SSet.coherentIso B X).hom) ≫
                      𝟙 ((ihom SSet.coherentIso).obj (sHom X B)) ≫
                      (cotensor.iso SSet.coherentIso B X).inv =
                    (representableMap X (brownFactorizationPath f) ≫
                        (cotensor.iso SSet.coherentIso B X).hom) ≫
                        (cotensor.iso SSet.coherentIso B X).inv := by
                      rw [Category.id_comp]
                  _ = representableMap X (brownFactorizationPath f) ≫
                      ((cotensor.iso SSet.coherentIso B X).hom ≫
                        (cotensor.iso SSet.coherentIso B X).inv) := by
                      rw [← Category.assoc]
                  _ = representableMap X (brownFactorizationPath f) := by
                      rw [Iso.hom_inv_id, Category.comp_id]
      _ = 𝟙 (sHom X (brownFactorizationObj f)) ≫
          representableMap X (brownFactorizationPath f) := by
          rw [Category.id_comp]
  · calc
      ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
          ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
            sHom X (brownFactorizationObj f)) ≫
          brownFactorizationRepresentableHomotopy f X) ≫
          representableMap X (brownFactorizationLeft f) =
        ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
          ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
            sHom X (brownFactorizationObj f))) ≫
          brownFactorizationRepresentableHomotopyLeft f X := by
          simpa only [Category.assoc] using congrArg
            (fun q => ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
              ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.tgt) ▷
                sHom X (brownFactorizationObj f))) ≫ q)
            (brownFactorizationRepresentableHomotopy_left f X)
      _ = representableMap X (brownFactorizationLeft f) := by
          dsimp [brownFactorizationRepresentableHomotopyLeft]
          simpa only [Category.assoc, Category.id_comp] using congrArg
            (fun q => q ≫ representableMap X (brownFactorizationLeft f))
            (tensorEndpoint_snd (I := SSet.coherentIso)
              (X := sHom X (brownFactorizationObj f)) SSet.coherentIso.tgt)
      _ = 𝟙 (sHom X (brownFactorizationObj f)) ≫
          representableMap X (brownFactorizationLeft f) := by
          rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma brownFactorizationPath_src_representable {A B : K} (f : A ⟶ B) (X : K) :
    (representableMap X (brownFactorizationPath f) ≫
        (cotensor.iso SSet.coherentIso B X).hom) ≫
        SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) =
      representableMap X (brownFactorizationLeft f) ≫ representableMap X f := by
  change (representableMap X (brownFactorizationPath f) ≫
        (cotensor.iso SSet.coherentIso B X).hom) ≫
        ((MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) ≫
          (sHom X B).expPointIsoSelf.hom) =
      representableMap X (brownFactorizationLeft f) ≫ representableMap X f
  have hsrc : representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
      (cotensor.iso (Δ[0] : SSet.{v}) B X).hom =
        (cotensor.iso SSet.coherentIso B X).hom ≫
          (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) := by
    change eHomWhiskerLeft SSet X (cotensorContraMap SSet.coherentIso.src B) ≫
      (cotensor.iso (Δ[0] : SSet.{v}) B X).hom =
        (cotensor.iso SSet.coherentIso B X).hom ≫
          (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B)
    exact cotensor_iso_hom_naturality_precompose SSet.coherentIso.src B X
  calc
    (representableMap X (brownFactorizationPath f) ≫
        (cotensor.iso SSet.coherentIso B X).hom) ≫
        ((MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B) ≫
          (sHom X B).expPointIsoSelf.hom) =
      representableMap X (brownFactorizationPath f) ≫
        ((cotensor.iso SSet.coherentIso B X).hom ≫
          (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X B)) ≫
          (sHom X B).expPointIsoSelf.hom := by
        simp only [Category.assoc]
    _ = representableMap X (brownFactorizationPath f) ≫
        (representableMap X (cotensorContraMap SSet.coherentIso.src B) ≫
          (cotensor.iso (Δ[0] : SSet.{v}) B X).hom) ≫
          (sHom X B).expPointIsoSelf.hom := by
        exact congrArg
          (fun q => representableMap X (brownFactorizationPath f) ≫ q ≫
            (sHom X B).expPointIsoSelf.hom) hsrc.symm
    _ = (representableMap X (brownFactorizationLeft f) ≫
          representableMap X (cotensorPointMap f)) ≫
          (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫
          (sHom X B).expPointIsoSelf.hom := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ (cotensor.iso (Δ[0] : SSet.{v}) B X).hom ≫
            (sHom X B).expPointIsoSelf.hom)
          (brownFactorization_representableIsPullback f X).w
    _ = representableMap X (brownFactorizationLeft f) ≫
        (representableMap X (cotensorPointMap f) ≫
          (cotensor.iso (Δ[0] : SSet.{v}) B X).hom) ≫
          (sHom X B).expPointIsoSelf.hom := by
        simp only [Category.assoc]
    _ = representableMap X (brownFactorizationLeft f) ≫
        (representableMap X f ≫ (sHom X B).expPointIsoSelf.inv) ≫
          (sHom X B).expPointIsoSelf.hom := by
        exact congrArg
          (fun q => representableMap X (brownFactorizationLeft f) ≫ q ≫
            (sHom X B).expPointIsoSelf.hom)
          (representableMap_cotensorPointMap_hom f X)
    _ = representableMap X (brownFactorizationLeft f) ≫ representableMap X f := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private lemma brownFactorizationRepresentableHomotopy_src {A B : K} (f : A ⟶ B) (X : K) :
    (λ_ (sHom X (brownFactorizationObj f))).inv ≫
        ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.src) ▷
          sHom X (brownFactorizationObj f)) ≫
        brownFactorizationRepresentableHomotopy f X =
      representableMap X (brownFactorizationLeft f) ≫
        representableMap X (brownFactorizationSection f) := by
  apply IsPullback.hom_ext (brownFactorization_representableIsPullback f X)
  · apply (cancel_mono (cotensor.iso SSet.coherentIso B X).hom).mp
    let endpoint : sHom X (brownFactorizationObj f) ⟶
        SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) :=
      (λ_ (sHom X (brownFactorizationObj f))).inv ≫
        ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.src) ▷
          sHom X (brownFactorizationObj f))
    let m : sHom X (brownFactorizationObj f) ⟶
        SSet.pathSpace (I := SSet.coherentIso) (sHom X B) :=
      representableMap X (brownFactorizationPath f) ≫
        (cotensor.iso SSet.coherentIso B X).hom
    calc
      ((endpoint ≫ brownFactorizationRepresentableHomotopy f X) ≫
          representableMap X (brownFactorizationPath f)) ≫
          (cotensor.iso SSet.coherentIso B X).hom =
        endpoint ≫ brownFactorizationRepresentableHomotopyPath f X ≫
          (cotensor.iso SSet.coherentIso B X).hom := by
          simpa only [Category.assoc] using congrArg
            (fun q => endpoint ≫ q ≫ (cotensor.iso SSet.coherentIso B X).hom)
            (brownFactorizationRepresentableHomotopy_path f X)
      _ = representableMap X (brownFactorizationLeft f) ≫ representableMap X f ≫
          SSet.pathSpace.const (I := SSet.coherentIso) (sHom X B) := by
          dsimp [brownFactorizationRepresentableHomotopyPath, endpoint, m]
          calc
            ((λ_ (sHom X (brownFactorizationObj f))).inv ≫
                  ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.src) ▷
                    sHom X (brownFactorizationObj f))) ≫
                (SSet.coherentIso ◁ m ≫
                  SSet.pathSpace.srcContractionEval (sHom X B) ≫
                  (cotensor.iso SSet.coherentIso B X).inv) ≫
                (cotensor.iso SSet.coherentIso B X).hom =
              (((λ_ (sHom X (brownFactorizationObj f))).inv ≫
                  ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.src) ▷
                    sHom X (brownFactorizationObj f))) ≫
                  SSet.coherentIso ◁ m) ≫
                  SSet.pathSpace.srcContractionEval (sHom X B) ≫
                  (cotensor.iso SSet.coherentIso B X).inv ≫
                (cotensor.iso SSet.coherentIso B X).hom := by
                simp only [Category.assoc]
            _ = (m ≫ (λ_ (SSet.pathSpace (I := SSet.coherentIso) (sHom X B))).inv ≫
                  ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.src) ▷
                    SSet.pathSpace (I := SSet.coherentIso) (sHom X B))) ≫
                  SSet.pathSpace.srcContractionEval (sHom X B) ≫
                  (cotensor.iso SSet.coherentIso B X).inv ≫
                (cotensor.iso SSet.coherentIso B X).hom := by
                simpa only [Category.assoc] using congrArg
                  (fun q => q ≫ SSet.pathSpace.srcContractionEval (sHom X B) ≫
                    (cotensor.iso SSet.coherentIso B X).inv ≫
                    (cotensor.iso SSet.coherentIso B X).hom)
                  (tensorEndpoint_whiskerLeft SSet.coherentIso.src m)
            _ = m ≫
                  ((λ_ (SSet.pathSpace (I := SSet.coherentIso) (sHom X B))).inv ≫
                    ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.src) ▷
                      SSet.pathSpace (I := SSet.coherentIso) (sHom X B)) ≫
                    SSet.pathSpace.srcContractionEval (sHom X B)) ≫
                  (cotensor.iso SSet.coherentIso B X).inv ≫
                (cotensor.iso SSet.coherentIso B X).hom := by
                simp only [Category.assoc]
            _ = m ≫
                  (SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) ≫
                    SSet.pathSpace.const (I := SSet.coherentIso) (sHom X B)) ≫
                  (cotensor.iso SSet.coherentIso B X).inv ≫
                (cotensor.iso SSet.coherentIso B X).hom := by
                rw [SSet.pathSpace.srcContractionEval_src]
            _ = representableMap X (brownFactorizationPath f) ≫
                  (cotensor.iso SSet.coherentIso B X).hom ≫
                  SSet.pathSpace.src (I := SSet.coherentIso) (sHom X B) ≫
                  SSet.pathSpace.const (I := SSet.coherentIso) (sHom X B) := by
                rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
            _ = representableMap X (brownFactorizationLeft f) ≫ representableMap X f ≫
                  SSet.pathSpace.const (I := SSet.coherentIso) (sHom X B) := by
                simpa only [Category.assoc] using congrArg
                  (fun q => q ≫ SSet.pathSpace.const (I := SSet.coherentIso) (sHom X B))
                  (brownFactorizationPath_src_representable f X)
      _ = (representableMap X (brownFactorizationLeft f) ≫
            representableMap X (brownFactorizationSection f) ≫
            representableMap X (brownFactorizationPath f)) ≫
          (cotensor.iso SSet.coherentIso B X).hom := by
          calc
            representableMap X (brownFactorizationLeft f) ≫ representableMap X f ≫
                SSet.pathSpace.const (I := SSet.coherentIso) (sHom X B) =
              representableMap X (brownFactorizationLeft f) ≫
                (representableMap X (coherentIsoPathMap f) ≫
                  (cotensor.iso SSet.coherentIso B X).hom) := by
                rw [representableMap_coherentIsoPathMap_const f X]
            _ = representableMap X (brownFactorizationLeft f) ≫
                representableMap X (brownFactorizationSection f) ≫
                representableMap X (brownFactorizationPath f) ≫
                (cotensor.iso SSet.coherentIso B X).hom := by
                rw [← brownFactorizationSection_path f]
                rw [representableMap_comp]
                simp only [Category.assoc]
  · let endpoint : sHom X (brownFactorizationObj f) ⟶
        SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) :=
      (λ_ (sHom X (brownFactorizationObj f))).inv ≫
        ((SSet.pointIsUnit.inv ≫ SSet.coherentIso.src) ▷
          sHom X (brownFactorizationObj f))
    have hsection_left :
        representableMap X (brownFactorizationSection f) ≫
          representableMap X (brownFactorizationLeft f) =
          𝟙 (sHom X A) := by
      calc
        representableMap X (brownFactorizationSection f) ≫
            representableMap X (brownFactorizationLeft f) =
          representableMap X (brownFactorizationSection f ≫ brownFactorizationLeft f) := by
          rw [representableMap_comp]
        _ = representableMap X (𝟙 A) := by rw [brownFactorizationSection_left]
        _ = 𝟙 (sHom X A) := by rw [representableMap_id]
    calc
      (endpoint ≫ brownFactorizationRepresentableHomotopy f X) ≫
          representableMap X (brownFactorizationLeft f) =
        endpoint ≫ brownFactorizationRepresentableHomotopyLeft f X := by
        simpa only [Category.assoc] using congrArg
          (fun q => endpoint ≫ q)
          (brownFactorizationRepresentableHomotopy_left f X)
      _ = representableMap X (brownFactorizationLeft f) := by
        dsimp [brownFactorizationRepresentableHomotopyLeft, endpoint]
        simpa only [Category.assoc, Category.id_comp] using congrArg
          (fun q => q ≫ representableMap X (brownFactorizationLeft f))
          (tensorEndpoint_snd (I := SSet.coherentIso)
            (X := sHom X (brownFactorizationObj f)) SSet.coherentIso.src)
      _ = (representableMap X (brownFactorizationLeft f) ≫
            representableMap X (brownFactorizationSection f)) ≫
            representableMap X (brownFactorizationLeft f) := by
        rw [Category.assoc, hsection_left, Category.comp_id]

private noncomputable def brownFactorizationRepresentableLeftHomotopy {A B : K}
    (f : A ⟶ B) (X : K) :
    SSet.Homotopy (I := SSet.coherentIso)
      (representableMap X (brownFactorizationLeft f) ≫
        representableMap X (brownFactorizationSection f))
      (𝟙 (sHom X (brownFactorizationObj f))) where
  homotopy := MonoidalClosed.curry (brownFactorizationRepresentableHomotopy f X)
  source_eq := by
    change MonoidalClosed.curry (brownFactorizationRepresentableHomotopy f X) ≫
        (MonoidalClosed.pre SSet.coherentIso.src).app (sHom X (brownFactorizationObj f)) ≫
        (sHom X (brownFactorizationObj f)).expPointIsoSelf.hom =
      representableMap X (brownFactorizationLeft f) ≫
        representableMap X (brownFactorizationSection f)
    rw [SSet.curry_endpoint_eval]
    exact brownFactorizationRepresentableHomotopy_src f X
  target_eq := by
    change MonoidalClosed.curry (brownFactorizationRepresentableHomotopy f X) ≫
        (MonoidalClosed.pre SSet.coherentIso.tgt).app (sHom X (brownFactorizationObj f)) ≫
        (sHom X (brownFactorizationObj f)).expPointIsoSelf.hom =
      𝟙 (sHom X (brownFactorizationObj f))
    rw [SSet.curry_endpoint_eval]
    exact brownFactorizationRepresentableHomotopy_tgt f X

/-- The left projection in the Brown factorization is an equivalence. -/
theorem brownFactorizationLeft_equivalence {A B : K} (f : A ⟶ B) :
    Equivalence (brownFactorizationLeft f) := by
  intro X
  let e : @QCat.Equiv (Fun X (brownFactorizationObj f)).obj (Fun X A).obj
      (Fun X (brownFactorizationObj f)).property (Fun X A).property :=
    {
    toFun := representableMap X (brownFactorizationLeft f)
    invFun := representableMap X (brownFactorizationSection f)
    left_inv := brownFactorizationRepresentableLeftHomotopy f X
    right_inv := by
      have hsection_left :
          representableMap X (brownFactorizationSection f) ≫
            representableMap X (brownFactorizationLeft f) =
            𝟙 (sHom X A) := by
        calc
          representableMap X (brownFactorizationSection f) ≫
              representableMap X (brownFactorizationLeft f) =
            representableMap X (brownFactorizationSection f ≫ brownFactorizationLeft f) := by
            rw [representableMap_comp]
          _ = representableMap X (𝟙 A) := by rw [brownFactorizationSection_left]
          _ = 𝟙 (sHom X A) := by rw [representableMap_id]
      change SSet.Homotopy (I := SSet.coherentIso)
        (representableMap X (brownFactorizationSection f) ≫
          representableMap X (brownFactorizationLeft f))
        (𝟙 (sHom X A))
      rw [hsection_left]
      exact SSet.Homotopy.refl (I := SSet.coherentIso) (𝟙 (sHom X A))
    }
  exact ⟨e, rfl⟩

/-- The left projection in the Brown factorization is a trivial fibration. -/
theorem brownFactorizationLeft_trivialFibration {A B : K} (f : A ⟶ B) :
    TrivialFibration (brownFactorizationLeft f) :=
  ⟨brownFactorizationLeft_isIsofibration f, brownFactorizationLeft_equivalence f⟩

end InfinityCosmos
