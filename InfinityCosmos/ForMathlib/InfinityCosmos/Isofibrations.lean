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

/-
This file only proves the Brown factorization construction. The conclusion needed to finish
Lemma 1.5.12 is intentionally not asserted here: the missing downstream statement is that
`brownFactorizationLeft f` is a trivial fibration, and hence that the section above exhibits the
left map as an equivalence. In a later API this would have the shape
`brownFactorizationLeft_trivialFibration (f) : IsTrivialFibration (brownFactorizationLeft f)`.
That statement depends on the stability of trivial fibrations under products, pullbacks, and
inverse limits of towers from #114, and under Leibniz cotensors with monomorphisms from #115.
-/

end InfinityCosmos
