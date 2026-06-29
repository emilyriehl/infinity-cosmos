/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JHU Category Theory Seminar
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.CotensorIso
import InfinityCosmos.ForMathlib.InfinityCosmos.CotensorPointIso

open scoped Simplicial

/-!
# Explicit isofibrations in an ∞-cosmos.

This file constructs a few explicit isofibrations in an ∞-cosmos as consequences of the axioms.

Simple examples include:

* `compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C`
* `pullbackIsofibration {E B A : K} (p : E ↠ B) (f : A ⟶ B) : pullbackIsofibrationObj p f ↠ A`
* `toTerminalIsofibration (A : K) : A ↠ (⊤_ K)`

More elaborate examples include:

* `cotensorCovIsofibration (V : SSet.{v}) {A B : K} (f : A ↠ B) : V ⋔ₛ A ↠ V ⋔ₛ B`
* `cotensorContraIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (A : K) : V ⋔ₛ A ↠ U ⋔ₛ A`
* `leibnizCotensorIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :`
    `V ⋔ₛ A ↠ leibnizCotensorCod i f`

All but the first of these involve explicit choices of limits so are noncomputable.
-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos
open HasConicalTerminal
open MonoidalCategory BraidedCategory

local notation3:1024 U:1024 " ⋔ₛ " A:1024 =>
  CategoryTheory.SimplicialCategory.cotensor.obj U A

variable {K : Type u} [Category.{v} K] [InfinityCosmos.{0} K]

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
noncomputable def cotensorInitialIso (A : K) : (⊥_ SSet.{v} ) ⋔ₛ A ≅ ⊤_ K where
  hom := terminal.from ((⊥_ SSet.{v}) ⋔ₛ A)
  inv := (cotensor.iso.underlying (⊥_ SSet.{v}) A (⊤_ K)).symm (initial.to (sHom (⊤_ K) A))
  hom_inv_id := (cotensor.iso.underlying (⊥_ SSet.{v}) A ((⊥_ SSet.{v} ) ⋔ₛ A)).injective
    (initial.hom_ext _ _)
  inv_hom_id := terminal.hom_ext _ _

noncomputable def cotensorInitial_isTerminal (A : K) : IsTerminal ((⊥_ SSet.{v} ) ⋔ₛ A) :=
  terminalIsTerminal.ofIso (cotensorInitialIso A).symm

lemma cotensorCovMapInitial_isIso {A B : K} (f : A ⟶ B) : IsIso (cotensorCovMap (⊥_ SSet.{v}) f) :=
  isIso_of_isTerminal (cotensorInitial_isTerminal A) (cotensorInitial_isTerminal B)
    (cotensorCovMap (⊥_ SSet.{v}) f)

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.
noncomputable def cotensorToTerminalIso (U : SSet) {T : K} (hT : IsConicalTerminal SSet T) :
    U ⋔ₛ T ≅ ⊤_ K where
  hom := terminal.from _
  inv := by
    refine (cotensor.iso.underlying U T (⊤_ K)).symm ?_
    exact (terminal.from U) ≫ (IsConicalTerminal.eHomIso SSet hT (⊤_ K)).inv
  hom_inv_id := by
    apply (cotensor.iso.underlying U T (U ⋔ₛ T)).injective
    have : IsTerminal (sHom (U ⋔ₛ T) T) :=
      terminalIsTerminal.ofIso (IsConicalTerminal.eHomIso SSet hT (U ⋔ₛ T)).symm
    apply IsTerminal.hom_ext this
  inv_hom_id := terminal.hom_ext _ _

noncomputable def cotensorToConicalTerminal_isTerminal
    (U : SSet) {T : K} (hT : IsConicalTerminal SSet T) : IsTerminal (U ⋔ₛ T) :=
  terminalIsTerminal.ofIso (cotensorToTerminalIso U hT).symm

lemma cotensorContraMapToTerminal_isIso {U V : SSet} (i : U ⟶ V)
    {T : K} (hT : IsConicalTerminal SSet T) : IsIso (cotensorContraMap i T) :=
  isIso_of_isTerminal (cotensorToConicalTerminal_isTerminal V hT)
    (cotensorToConicalTerminal_isTerminal U hT) (cotensorContraMap i T)

lemma cotensorInitialSquare_isPullback (V : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsPullback (terminal.from (V ⋔ₛ B) ≫ (cotensorInitialIso A).inv) (𝟙 _)
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
noncomputable def cotensorCovIsofibration (V : SSet.{v}) {A B : K} (f : A ↠ B) : V ⋔ₛ A ↠ V ⋔ₛ B :=
  ⟨cotensorCovMap V f.1, cotensorCovMap_fibrant V f⟩

@[simp]
lemma cotensorCovIsofibration_map (V : SSet.{v}) {A B : K} (f : A ↠ B) :
    (cotensorCovIsofibration V f).1 = cotensorCovMap V f.1 := rfl

lemma cotensorTerminalSquare_isPullback {U V : SSet.{v}} (i : U ⟶ V) (A : K) :
    IsPullback
      (𝟙 _) (terminal.from (U ⋔ₛ A) ≫ (cotensorToTerminalIso V terminalIsConicalTerminal).inv)
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
    V ⋔ₛ A ↠ U ⋔ₛ A := ⟨cotensorContraMap i A, cotensorContraMap_fibrant i A⟩

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
    leibnizCotensorCod i f ⟶ U ⋔ₛ A := by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) := by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.fst (cotensorCovMap U f.1) (cotensorContraMap i B)

/-- An explicit choice of the left map in the Leibniz pullback square. -/
noncomputable def leibnizCotensor.snd {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :
    leibnizCotensorCod i f ⟶ V ⋔ₛ B := by
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
    V ⋔ₛ A ⟶ leibnizCotensorCod i f :=
  IsPullback.lift (leibnizCotensor.isPullback i f) (cotensorContraMap i A) (cotensorCovMap V f.1)
    (cotensor_bifunctoriality i f.1)

/-- An explicitly chosen Leibniz cotensor isofibration of a monomorphism `i` with an isofibration
`f`. -/
noncomputable def leibnizCotensorIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : A ↠ B) : V ⋔ₛ A ↠ leibnizCotensorCod i f :=
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

/-- The endpoint inclusion of the source vertex into the boundary of the coherent isomorphism. -/
noncomputable def coherentIsoBoundarySrc :
    (Δ[0] : SSet.{v}) ⟶ SSet.coherentIso.boundary.toSSet :=
  SSet.Subcomplex.lift SSet.coherentIso.src (by
    intro n x hx
    exact Or.inl hx)

/-- The endpoint inclusion of the target vertex into the boundary of the coherent isomorphism. -/
noncomputable def coherentIsoBoundaryTgt :
    (Δ[0] : SSet.{v}) ⟶ SSet.coherentIso.boundary.toSSet :=
  SSet.Subcomplex.lift SSet.coherentIso.tgt (by
    intro n x hx
    exact Or.inr hx)

@[simp, reassoc]
lemma coherentIsoBoundarySrc_ι :
    coherentIsoBoundarySrc ≫ SSet.coherentIso.boundary.ι = SSet.coherentIso.src := by
  simp [coherentIsoBoundarySrc]

@[simp, reassoc]
lemma coherentIsoBoundaryTgt_ι :
    coherentIsoBoundaryTgt ≫ SSet.coherentIso.boundary.ι = SSet.coherentIso.tgt := by
  simp [coherentIsoBoundaryTgt]

private lemma deltaZero_obj_subsingleton (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((Δ[0] : SSet.{v}).obj n) := by
  constructor
  intro a b
  apply (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := n)).injective
  apply SimplexCategory.Hom.ext
  ext x
  have ha : ((SSet.stdSimplex.objEquiv a).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  have hb : ((SSet.stdSimplex.objEquiv b).toOrderHom x : Fin 1) = 0 := Fin.eq_zero _
  rw [ha, hb]

private noncomputable def coherentIsoBoundarySrcPreimage {n : SimplexCategoryᵒᵖ}
    {x : SSet.coherentIso.obj n}
    (hsrc : x ∈ (SSet.Subcomplex.range SSet.coherentIso.src).obj n) :
    (Δ[0] : SSet.{v}).obj n :=
  Classical.choose (show ∃ y, SSet.coherentIso.src.app n y = x from hsrc)

private lemma coherentIsoBoundarySrcPreimage_spec {n : SimplexCategoryᵒᵖ}
    {x : SSet.coherentIso.obj n}
    (hsrc : x ∈ (SSet.Subcomplex.range SSet.coherentIso.src).obj n) :
    SSet.coherentIso.src.app n (coherentIsoBoundarySrcPreimage hsrc) = x :=
  Classical.choose_spec (show ∃ y, SSet.coherentIso.src.app n y = x from hsrc)

private noncomputable def coherentIsoBoundaryTgtPreimage {n : SimplexCategoryᵒᵖ}
    {x : SSet.coherentIso.obj n}
    (htgt : x ∈ (SSet.Subcomplex.range SSet.coherentIso.tgt).obj n) :
    (Δ[0] : SSet.{v}).obj n :=
  Classical.choose (show ∃ y, SSet.coherentIso.tgt.app n y = x from htgt)

private lemma coherentIsoBoundaryTgtPreimage_spec {n : SimplexCategoryᵒᵖ}
    {x : SSet.coherentIso.obj n}
    (htgt : x ∈ (SSet.Subcomplex.range SSet.coherentIso.tgt).obj n) :
    SSet.coherentIso.tgt.app n (coherentIsoBoundaryTgtPreimage htgt) = x :=
  Classical.choose_spec (show ∃ y, SSet.coherentIso.tgt.app n y = x from htgt)

private noncomputable def coherentIsoBoundaryBinaryDescObj (n : SimplexCategoryᵒᵖ)
    (s : BinaryCofan ((Δ[0] : SSet.{v}).obj n) ((Δ[0] : SSet.{v}).obj n)) :
    SSet.coherentIso.boundary.toSSet.obj n ⟶ s.pt := by
  classical
  exact ↾fun x =>
    if hsrc : x.1 ∈ (SSet.Subcomplex.range SSet.coherentIso.src).obj n then
      s.inl (coherentIsoBoundarySrcPreimage hsrc)
    else
      have htgt : x.1 ∈ (SSet.Subcomplex.range SSet.coherentIso.tgt).obj n := by
        rcases SSet.coherentIso.mem_boundary_iff.mp x.2 with h | h
        · exact False.elim (hsrc h)
        · exact h
      s.inr (coherentIsoBoundaryTgtPreimage htgt)

private lemma coherentIsoBoundaryBinaryDescObj_src (n : SimplexCategoryᵒᵖ)
    (s : BinaryCofan ((Δ[0] : SSet.{v}).obj n) ((Δ[0] : SSet.{v}).obj n)) :
    coherentIsoBoundarySrc.app n ≫ coherentIsoBoundaryBinaryDescObj n s = s.inl := by
  classical
  ext x
  dsimp [coherentIsoBoundaryBinaryDescObj, coherentIsoBoundarySrc]
  split
  · exact congrArg s.inl (@Subsingleton.elim _ (deltaZero_obj_subsingleton n) _ _)
  · rename_i hsrc
    exact False.elim (hsrc ⟨x, rfl⟩)

private lemma coherentIsoBoundaryBinaryDescObj_tgt (n : SimplexCategoryᵒᵖ)
    (s : BinaryCofan ((Δ[0] : SSet.{v}).obj n) ((Δ[0] : SSet.{v}).obj n)) :
    coherentIsoBoundaryTgt.app n ≫ coherentIsoBoundaryBinaryDescObj n s = s.inr := by
  classical
  ext x
  dsimp [coherentIsoBoundaryBinaryDescObj, coherentIsoBoundaryTgt]
  have htgt :
      SSet.coherentIso.tgt.app n x ∈
        (SSet.Subcomplex.range SSet.coherentIso.tgt).obj n :=
    ⟨x, rfl⟩
  have hsrc_false :
      ¬ SSet.coherentIso.tgt.app n x ∈
        (SSet.Subcomplex.range SSet.coherentIso.src).obj n :=
    SSet.coherentIso.not_mem_range_src_of_mem_range_tgt htgt
  rw [dif_neg hsrc_false]
  exact congrArg s.inr (@Subsingleton.elim _ (deltaZero_obj_subsingleton n) _ _)

private noncomputable def coherentIsoBoundaryBinaryCofanObj_isColimit (n : SimplexCategoryᵒᵖ) :
    IsColimit
      (BinaryCofan.mk
        (coherentIsoBoundarySrc.app n)
        (coherentIsoBoundaryTgt.app n)) := by
  classical
  refine BinaryCofan.isColimitMk
    (fun s => coherentIsoBoundaryBinaryDescObj n s) ?_ ?_ ?_
  · exact coherentIsoBoundaryBinaryDescObj_src n
  · exact coherentIsoBoundaryBinaryDescObj_tgt n
  · intro s m hm₁ hm₂
    ext x
    dsimp [coherentIsoBoundaryBinaryDescObj]
    split
    · rename_i hsrc
      have hx :
          coherentIsoBoundarySrc.app n (coherentIsoBoundarySrcPreimage hsrc) = x := by
        apply Subtype.ext
        exact coherentIsoBoundarySrcPreimage_spec hsrc
      have hm := ConcreteCategory.congr_hom hm₁ (coherentIsoBoundarySrcPreimage hsrc)
      calc
        (ConcreteCategory.hom m) x =
            (ConcreteCategory.hom m)
              ((ConcreteCategory.hom (coherentIsoBoundarySrc.app n))
                (coherentIsoBoundarySrcPreimage hsrc)) := by
              rw [hx]
        _ = (ConcreteCategory.hom (coherentIsoBoundarySrc.app n ≫ m))
              (coherentIsoBoundarySrcPreimage hsrc) := rfl
        _ = (ConcreteCategory.hom s.inl) (coherentIsoBoundarySrcPreimage hsrc) := hm
    · rename_i hsrc
      have htgt : x.1 ∈ (SSet.Subcomplex.range SSet.coherentIso.tgt).obj n := by
        rcases SSet.coherentIso.mem_boundary_iff.mp x.2 with h | h
        · exact False.elim (hsrc h)
        · exact h
      have hx :
          coherentIsoBoundaryTgt.app n (coherentIsoBoundaryTgtPreimage htgt) = x := by
        apply Subtype.ext
        exact coherentIsoBoundaryTgtPreimage_spec htgt
      have hm := ConcreteCategory.congr_hom hm₂ (coherentIsoBoundaryTgtPreimage htgt)
      calc
        (ConcreteCategory.hom m) x =
            (ConcreteCategory.hom m)
              ((ConcreteCategory.hom (coherentIsoBoundaryTgt.app n))
                (coherentIsoBoundaryTgtPreimage htgt)) := by
              rw [hx]
        _ = (ConcreteCategory.hom (coherentIsoBoundaryTgt.app n ≫ m))
              (coherentIsoBoundaryTgtPreimage htgt) := rfl
        _ = (ConcreteCategory.hom s.inr) (coherentIsoBoundaryTgtPreimage htgt) := hm

/-- The boundary of the coherent isomorphism is the coproduct of its two endpoints. -/
noncomputable def coherentIsoBoundary_isColimit :
    IsColimit (BinaryCofan.mk coherentIsoBoundarySrc coherentIsoBoundaryTgt) := by
  apply evaluationJointlyReflectsColimits
  intro n
  exact (isColimitMapCoconeBinaryCofanEquiv
    ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n)
    coherentIsoBoundarySrc coherentIsoBoundaryTgt).symm
    (coherentIsoBoundaryBinaryCofanObj_isColimit n)

lemma cotensorContraMap_comp {U V W : SSet.{v}} (i : U ⟶ V) (j : V ⟶ W) (A : K) :
    cotensorContraMap j A ≫ cotensorContraMap i A = cotensorContraMap (i ≫ j) A := by
  apply (cotensor.iso.underlying U A (W ⋔ₛ A)).injective
  calc
    (cotensor.iso.underlying U A (W ⋔ₛ A)) (cotensorContraMap j A ≫ cotensorContraMap i A) =
        i ≫ (cotensor.iso.underlying V A (W ⋔ₛ A)) (cotensorContraMap j A) := by
      rw [cotensor_iso_underlying_precompose]
    _ = i ≫ (j ≫ (cotensor.iso.underlying W A (W ⋔ₛ A)) (𝟙 (W ⋔ₛ A))) := by
      have hj := cotensor_iso_underlying_precompose j A (W ⋔ₛ A) (𝟙 (W ⋔ₛ A))
      simpa using congrArg (fun q => i ≫ q) hj
    _ = (i ≫ j) ≫ (cotensor.iso.underlying W A (W ⋔ₛ A)) (𝟙 (W ⋔ₛ A)) := by
      rw [Category.assoc]
    _ = (cotensor.iso.underlying U A (W ⋔ₛ A)) (cotensorContraMap (i ≫ j) A) := by
      have hij := cotensor_iso_underlying_precompose (i ≫ j) A (W ⋔ₛ A) (𝟙 (W ⋔ₛ A))
      simpa [Category.assoc] using hij.symm

/-- The endpoint-pair map of coherent-isomorphism paths. -/
noncomputable def coherentIsoEndpointPair (B : K) :
    SSet.coherentIso ⋔ₛ B ⟶ ((Δ[0] : SSet.{v}) ⋔ₛ B) ⨯ ((Δ[0] : SSet.{v}) ⋔ₛ B) :=
  prod.lift (cotensorContraMap SSet.coherentIso.src B)
    (cotensorContraMap SSet.coherentIso.tgt B)

/-- The map from the boundary cotensor to the product of endpoint cotensors. -/
noncomputable def coherentIsoBoundaryCotensorToProduct (B : K) :
    SSet.coherentIso.boundary.toSSet ⋔ₛ B ⟶
      ((Δ[0] : SSet.{v}) ⋔ₛ B) ⨯ ((Δ[0] : SSet.{v}) ⋔ₛ B) :=
  prod.lift (cotensorContraMap coherentIsoBoundarySrc B)
    (cotensorContraMap coherentIsoBoundaryTgt B)

lemma coherentIsoBoundaryCotensorToProduct_comp (B : K) :
    cotensorContraMap SSet.coherentIso.boundary.ι B ≫
      coherentIsoBoundaryCotensorToProduct B = coherentIsoEndpointPair B := by
  apply prod.hom_ext
  · dsimp [coherentIsoBoundaryCotensorToProduct, coherentIsoEndpointPair]
    rw [Category.assoc, prod.lift_fst, prod.lift_fst, cotensorContraMap_comp,
      coherentIsoBoundarySrc_ι]
  · dsimp [coherentIsoBoundaryCotensorToProduct, coherentIsoEndpointPair]
    rw [Category.assoc, prod.lift_snd, prod.lift_snd, cotensorContraMap_comp,
      coherentIsoBoundaryTgt_ι]

private noncomputable def coherentIsoBoundaryCotensorProductLift (B : K) {W : K}
    (fst : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B)
    (snd : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B) :
    W ⟶ SSet.coherentIso.boundary.toSSet ⋔ₛ B :=
  (cotensor.iso.underlying SSet.coherentIso.boundary.toSSet B W).symm
    (BinaryCofan.IsColimit.desc coherentIsoBoundary_isColimit
      ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) fst)
      ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) snd))

private lemma coherentIsoBoundaryCotensorProductLift_fst (B : K) {W : K}
    (fst : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B)
    (snd : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B) :
    coherentIsoBoundaryCotensorProductLift B fst snd ≫
      cotensorContraMap coherentIsoBoundarySrc B = fst := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B W).injective
  rw [cotensor_iso_underlying_precompose]
  dsimp [coherentIsoBoundaryCotensorProductLift]
  simp only [Equiv.apply_symm_apply]
  exact BinaryCofan.IsColimit.inl_desc coherentIsoBoundary_isColimit
    ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) fst)
    ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) snd)

private lemma coherentIsoBoundaryCotensorProductLift_snd (B : K) {W : K}
    (fst : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B)
    (snd : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B) :
    coherentIsoBoundaryCotensorProductLift B fst snd ≫
      cotensorContraMap coherentIsoBoundaryTgt B = snd := by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B W).injective
  rw [cotensor_iso_underlying_precompose]
  dsimp [coherentIsoBoundaryCotensorProductLift]
  simp only [Equiv.apply_symm_apply]
  exact BinaryCofan.IsColimit.inr_desc coherentIsoBoundary_isColimit
    ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) fst)
    ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) snd)

private lemma coherentIsoBoundaryCotensorProductLift_uniq (B : K) {W : K}
    (fst : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B)
    (snd : W ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B)
    (m : W ⟶ SSet.coherentIso.boundary.toSSet ⋔ₛ B)
    (hm₁ : m ≫ cotensorContraMap coherentIsoBoundarySrc B = fst)
    (hm₂ : m ≫ cotensorContraMap coherentIsoBoundaryTgt B = snd) :
    m = coherentIsoBoundaryCotensorProductLift B fst snd := by
  apply (cotensor.iso.underlying SSet.coherentIso.boundary.toSSet B W).injective
  apply BinaryCofan.IsColimit.hom_ext coherentIsoBoundary_isColimit
  · have h := congrArg (cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) hm₁
    rw [cotensor_iso_underlying_precompose] at h
    dsimp [coherentIsoBoundaryCotensorProductLift]
    simp only [Equiv.apply_symm_apply]
    exact h.trans (BinaryCofan.IsColimit.inl_desc coherentIsoBoundary_isColimit
      ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) fst)
      ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) snd)).symm
  · have h := congrArg (cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) hm₂
    rw [cotensor_iso_underlying_precompose] at h
    dsimp [coherentIsoBoundaryCotensorProductLift]
    simp only [Equiv.apply_symm_apply]
    exact h.trans (BinaryCofan.IsColimit.inr_desc coherentIsoBoundary_isColimit
      ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) fst)
      ((cotensor.iso.underlying (Δ[0] : SSet.{v}) B W) snd)).symm

/-- Cotensoring the coherent-isomorphism boundary identifies it with the binary product of the
endpoint cotensors. -/
noncomputable def coherentIsoBoundaryCotensorProductIsLimit (B : K) :
    IsLimit (BinaryFan.mk (cotensorContraMap coherentIsoBoundarySrc B)
      (cotensorContraMap coherentIsoBoundaryTgt B)) := by
  refine BinaryFan.IsLimit.mk _ (fun f g => coherentIsoBoundaryCotensorProductLift B f g) ?_ ?_ ?_
  · intro T f g
    exact coherentIsoBoundaryCotensorProductLift_fst B f g
  · intro T f g
    exact coherentIsoBoundaryCotensorProductLift_snd B f g
  · intro T f g m hm₁ hm₂
    exact coherentIsoBoundaryCotensorProductLift_uniq B f g m hm₁ hm₂

lemma coherentIsoBoundaryCotensorToProduct_isIso (B : K) :
    IsIso (coherentIsoBoundaryCotensorToProduct B) := by
  let e := IsLimit.conePointUniqueUpToIso (coherentIsoBoundaryCotensorProductIsLimit (B := B))
    (prodIsProd ((Δ[0] : SSet.{v}) ⋔ₛ B) ((Δ[0] : SSet.{v}) ⋔ₛ B))
  have he : e.hom = coherentIsoBoundaryCotensorToProduct B := by
    apply prod.hom_ext
    · dsimp [coherentIsoBoundaryCotensorToProduct]
      calc
        e.hom ≫ prod.fst = cotensorContraMap coherentIsoBoundarySrc B := by
          exact IsLimit.conePointUniqueUpToIso_hom_comp
            (coherentIsoBoundaryCotensorProductIsLimit (B := B))
            (prodIsProd ((Δ[0] : SSet.{v}) ⋔ₛ B) ((Δ[0] : SSet.{v}) ⋔ₛ B))
            ⟨WalkingPair.left⟩
        _ = prod.lift (cotensorContraMap coherentIsoBoundarySrc B)
            (cotensorContraMap coherentIsoBoundaryTgt B) ≫ prod.fst := by
            rw [prod.lift_fst]
    · dsimp [coherentIsoBoundaryCotensorToProduct]
      calc
        e.hom ≫ prod.snd = cotensorContraMap coherentIsoBoundaryTgt B := by
          exact IsLimit.conePointUniqueUpToIso_hom_comp
            (coherentIsoBoundaryCotensorProductIsLimit (B := B))
            (prodIsProd ((Δ[0] : SSet.{v}) ⋔ₛ B) ((Δ[0] : SSet.{v}) ⋔ₛ B))
            ⟨WalkingPair.right⟩
        _ = prod.lift (cotensorContraMap coherentIsoBoundarySrc B)
            (cotensorContraMap coherentIsoBoundaryTgt B) ≫ prod.snd := by
            rw [prod.lift_snd]
  rw [← he]
  infer_instance

lemma coherentIsoEndpointPair_isIsofibration (B : K) :
    IsIsofibration (coherentIsoEndpointPair B) := by
  haveI : IsIso (coherentIsoBoundaryCotensorToProduct B) :=
    coherentIsoBoundaryCotensorToProduct_isIso B
  rw [← coherentIsoBoundaryCotensorToProduct_comp B]
  exact comp_isIsofibration
    (cotensorContraIsofibration SSet.coherentIso.boundary.ι B)
    ⟨coherentIsoBoundaryCotensorToProduct B,
      iso_isIsofibration (coherentIsoBoundaryCotensorToProduct B)⟩

/-- The map on representables induced by source evaluation from the coherent-isomorphism cotensor
is a quasi-category equivalence. -/
noncomputable def representableCotensorContraMapCoherentIsoSrcEquiv (B X : K) :
    @QCat.Equiv (Fun X (SSet.coherentIso ⋔ₛ B)).obj (Fun X ((Δ[0] : SSet.{v}) ⋔ₛ B)).obj
      (Fun X (SSet.coherentIso ⋔ₛ B)).property (Fun X ((Δ[0] : SSet.{v}) ⋔ₛ B)).property := by
  let eA : (Fun X (SSet.coherentIso ⋔ₛ B)).obj ≅
      SSet.pathSpace (I := SSet.coherentIso) (sHom X B) :=
    cotensor.iso SSet.coherentIso B X
  let eB : (Fun X ((Δ[0] : SSet.{v}) ⋔ₛ B)).obj ≅ sHom X B :=
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
  let eB : (Fun X ((Δ[0] : SSet.{v}) ⋔ₛ B)).obj ≅ sHom X B :=
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
noncomputable def coherentIsoPathMap {A B : K} (f : A ⟶ B) : A ⟶ SSet.coherentIso ⋔ₛ B :=
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
      (β_ SSet.coherentIso (sHom X (SSet.coherentIso ⋔ₛ B))).hom ≫
      (sHom X (SSet.coherentIso ⋔ₛ B)) ◁ (cotensor.cone SSet.coherentIso B) ≫
      eComp SSet X (SSet.coherentIso ⋔ₛ B) B =
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

/-- The Brown factorization pullback object, before identifying `Δ[0] ⋔ₛ B` with `B`. -/
noncomputable def brownFactorizationObj {A B : K} (f : A ⟶ B) : K :=
  pullback (cotensorContraMap SSet.coherentIso.src B) (cotensorPointMap f)

/-- The projection from the Brown factorization object to the coherent-isomorphism path object. -/
noncomputable def brownFactorizationPath {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ SSet.coherentIso ⋔ₛ B :=
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
    brownFactorizationObj f ⟶ (Δ[0] : SSet.{v}) ⋔ₛ B :=
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

/-- The right map of the Brown factorization, after identifying `Δ[0] ⋔ₛ B` with `B`. -/
noncomputable def brownFactorizationRight {A B : K} (f : A ⟶ B) :
    brownFactorizationObj f ⟶ B :=
  brownFactorizationRightPoint f ≫ (cotensorPointIso B).hom

/-- The Brown section followed by the right map is the original morphism. -/
lemma brownFactorization_fac {A B : K} (f : A ⟶ B) :
    brownFactorizationSection f ≫ brownFactorizationRight f = f := by
  unfold brownFactorizationRight
  rw [← Category.assoc, brownFactorizationSection_rightPoint]
  exact cotensorPointMap_comp_cotensorPointIsoHom f

lemma brownFactorization_endpointPair_isPullback {A B : K} (f : A ⟶ B) :
    IsPullback (brownFactorizationPath f)
      (prod.lift (brownFactorizationLeft f) (brownFactorizationRightPoint f))
      (coherentIsoEndpointPair B)
      (prod.map (cotensorPointMap f) (𝟙 ((Δ[0] : SSet.{v}) ⋔ₛ B))) := by
  refine IsPullback.mk' ?w ?hom_ext ?exists_lift
  · apply prod.hom_ext
    · rw [Category.assoc, Category.assoc]
      dsimp [coherentIsoEndpointPair]
      rw [prod.lift_fst, prod.map_fst, ← Category.assoc, prod.lift_fst]
      exact (brownFactorization_isPullback f).w
    · rw [Category.assoc, Category.assoc]
      dsimp [coherentIsoEndpointPair, brownFactorizationRightPoint]
      rw [prod.lift_snd, prod.map_snd, Category.comp_id, prod.lift_snd]
  · intro T φ φ' hpath hprod
    have hleft : φ ≫ brownFactorizationLeft f = φ' ≫ brownFactorizationLeft f := by
      have h := congrArg (fun q => q ≫ prod.fst) hprod
      rw [Category.assoc, Category.assoc, prod.lift_fst] at h
      exact h
    exact (brownFactorization_isPullback f).hom_ext hpath hleft
  · intro T a b hcomm
    have hsrc :
        a ≫ cotensorContraMap SSet.coherentIso.src B =
          (b ≫ prod.fst) ≫ cotensorPointMap f := by
      have h := congrArg (fun q => q ≫ prod.fst) hcomm
      rw [Category.assoc, Category.assoc] at h
      dsimp [coherentIsoEndpointPair] at h
      rw [prod.lift_fst, prod.map_fst, ← Category.assoc] at h
      exact h
    let l := (brownFactorization_isPullback f).lift a (b ≫ prod.fst) hsrc
    refine ⟨l, ?_, ?_⟩
    · exact (brownFactorization_isPullback f).lift_fst a (b ≫ prod.fst) hsrc
    · apply prod.hom_ext
      · have hfst : l ≫ brownFactorizationLeft f = b ≫ prod.fst :=
          (brownFactorization_isPullback f).lift_snd a (b ≫ prod.fst) hsrc
        rw [Category.assoc, prod.lift_fst]
        exact hfst
      · have hlpath : l ≫ brownFactorizationPath f = a :=
          (brownFactorization_isPullback f).lift_fst a (b ≫ prod.fst) hsrc
        have htgt : a ≫ cotensorContraMap SSet.coherentIso.tgt B = b ≫ prod.snd := by
          have h := congrArg (fun q => q ≫ prod.snd) hcomm
          rw [Category.assoc, Category.assoc] at h
          dsimp [coherentIsoEndpointPair] at h
          rw [prod.lift_snd, prod.map_snd, Category.comp_id] at h
          exact h
        have hright : l ≫ brownFactorizationRightPoint f = b ≫ prod.snd := by
          dsimp [brownFactorizationRightPoint]
          rw [← Category.assoc, hlpath, htgt]
        rw [Category.assoc, prod.lift_snd]
        exact hright

private lemma binaryProduct_snd_isIsofibration (A D : K) :
    IsIsofibration (prod.snd : A ⨯ D ⟶ D) :=
  pullback_isIsofibration (toTerminalIsofibration A) (terminal.from D)
    prod.fst prod.snd (IsPullback.of_hasBinaryProduct' A D)

lemma brownFactorizationRightPoint_isIsofibration {A B : K} (f : A ⟶ B) :
    IsIsofibration (brownFactorizationRightPoint f) := by
  let liftMap :
      brownFactorizationObj f ⟶ A ⨯ ((Δ[0] : SSet.{v}) ⋔ₛ B) :=
    prod.lift (brownFactorizationLeft f) (brownFactorizationRightPoint f)
  have hLift : IsIsofibration liftMap := by
    exact pullback_isIsofibration
      ⟨coherentIsoEndpointPair B, coherentIsoEndpointPair_isIsofibration B⟩
      (prod.map (cotensorPointMap f) (𝟙 ((Δ[0] : SSet.{v}) ⋔ₛ B)))
      (brownFactorizationPath f) liftMap
      (by simpa [liftMap] using brownFactorization_endpointPair_isPullback f)
  have hSnd : IsIsofibration
      (prod.snd : A ⨯ ((Δ[0] : SSet.{v}) ⋔ₛ B) ⟶ ((Δ[0] : SSet.{v}) ⋔ₛ B)) :=
    binaryProduct_snd_isIsofibration A ((Δ[0] : SSet.{v}) ⋔ₛ B)
  have hcomp : liftMap ≫ prod.snd = brownFactorizationRightPoint f := by
    dsimp [liftMap]
    rw [prod.lift_snd]
  rw [← hcomp]
  exact comp_isIsofibration ⟨liftMap, hLift⟩ ⟨prod.snd, hSnd⟩

theorem brownFactorizationRight_isIsofibration {A B : K} (f : A ⟶ B) :
    IsIsofibration (brownFactorizationRight f) := by
  unfold brownFactorizationRight
  exact comp_isIsofibration
    ⟨brownFactorizationRightPoint f, brownFactorizationRightPoint_isIsofibration f⟩
    ⟨(cotensorPointIso B).hom, iso_isIsofibration (cotensorPointIso B).hom⟩

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
    SSet.coherentIso ⊗ sHom X (brownFactorizationObj f) ⟶ sHom X (SSet.coherentIso ⋔ₛ B) :=
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
  let eB : sHom X ((Δ[0] : SSet.{v}) ⋔ₛ B) ≅ sHom X B :=
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

/-- The Brown section is an equivalence. -/
theorem brownFactorizationSection_equivalence {A B : K} (f : A ⟶ B) :
    Equivalence (brownFactorizationSection f) := by
  intro X
  let e : @QCat.Equiv (Fun X A).obj (Fun X (brownFactorizationObj f)).obj
      (Fun X A).property (Fun X (brownFactorizationObj f)).property :=
    {
    toFun := representableMap X (brownFactorizationSection f)
    invFun := representableMap X (brownFactorizationLeft f)
    left_inv := by
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
    right_inv := brownFactorizationRepresentableLeftHomotopy f X
    }
  exact ⟨e, rfl⟩

end InfinityCosmos

namespace InfinityCosmos
namespace Equivalence

open CategoryTheory
open CategoryTheory.InfinityCosmos

universe u v

variable {K : Type u} [Category.{v} K] [CategoryTheory.InfinityCosmos K]

/-- The composite of equivalences in an ∞-cosmos is an equivalence. -/
theorem comp {A B C : K} {f : A ⟶ B} {g : B ⟶ C}
    (hf : CategoryTheory.InfinityCosmos.Equivalence f)
    (hg : CategoryTheory.InfinityCosmos.Equivalence g) :
    CategoryTheory.InfinityCosmos.Equivalence (f ≫ g) := by
  intro X
  rcases hf X with ⟨ef, hef⟩
  rcases hg X with ⟨eg, heg⟩
  refine ⟨@SSet.Equiv.comp (Fun X A).obj (Fun X B).obj (Fun X C).obj
    (Fun X A).property (Fun X B).property (Fun X C).property ef eg, ?_⟩
  dsimp [SSet.Equiv.comp]
  rw [hef, heg]
  change representableMap X f ≫ representableMap X g = representableMap X (f ≫ g)
  rw [representableMap_comp]

/-- If `g` and `f ≫ g` are equivalences, then `f` is an equivalence. -/
theorem of_comp_left {A B C : K} {f : A ⟶ B} {g : B ⟶ C}
    (hg : CategoryTheory.InfinityCosmos.Equivalence g)
    (hfg : CategoryTheory.InfinityCosmos.Equivalence (f ≫ g)) :
    CategoryTheory.InfinityCosmos.Equivalence f := by
  intro X
  rcases hg X with ⟨eg, heg⟩
  rcases hfg X with ⟨efg, hefg⟩
  let F := (toFunMap X f).hom
  let G := (toFunMap X g).hom
  have hcomp : efg.toFun = F ≫ G := by
    dsimp [F, G]
    rw [hefg]
    change representableMap X (f ≫ g) = representableMap X f ≫ representableMap X g
    rw [representableMap_comp]
  refine ⟨@SSet.Equiv.of_comp_left (Fun X A).obj (Fun X B).obj (Fun X C).obj
    (Fun X A).property (Fun X B).property (Fun X C).property F G eg heg efg hcomp, rfl⟩

/-- If `f` and `f ≫ g` are equivalences, then `g` is an equivalence. -/
theorem of_comp_right {A B C : K} {f : A ⟶ B} {g : B ⟶ C}
    (hf : CategoryTheory.InfinityCosmos.Equivalence f)
    (hfg : CategoryTheory.InfinityCosmos.Equivalence (f ≫ g)) :
    CategoryTheory.InfinityCosmos.Equivalence g := by
  intro X
  rcases hf X with ⟨ef, hef⟩
  rcases hfg X with ⟨efg, hefg⟩
  let F := (toFunMap X f).hom
  let G := (toFunMap X g).hom
  have hcomp : efg.toFun = F ≫ G := by
    dsimp [F, G]
    rw [hefg]
    change representableMap X (f ≫ g) = representableMap X f ≫ representableMap X g
    rw [representableMap_comp]
  refine ⟨@SSet.Equiv.of_comp_right (Fun X A).obj (Fun X B).obj (Fun X C).obj
    (Fun X A).property (Fun X B).property (Fun X C).property F G ef hef efg hcomp, rfl⟩

end Equivalence
end InfinityCosmos

namespace InfinityCosmos

open CategoryTheory
open CategoryTheory.InfinityCosmos

universe u v

variable {K : Type u} [Category.{v} K] [CategoryTheory.InfinityCosmos K]

/-- In the Brown factorization, the original map is an equivalence iff the right map is a
trivial fibration. -/
theorem brownFactorization_equivalence_iff_right_trivialFibration {A B : K} (f : A ⟶ B) :
    CategoryTheory.InfinityCosmos.Equivalence f ↔
      CategoryTheory.InfinityCosmos.TrivialFibration (brownFactorizationRight f) := by
  constructor
  · intro hf
    refine ⟨brownFactorizationRight_isIsofibration f, ?_⟩
    refine InfinityCosmos.Equivalence.of_comp_right (brownFactorizationSection_equivalence f) ?_
    rw [brownFactorization_fac]
    exact hf
  · intro hright
    rw [← brownFactorization_fac f]
    exact InfinityCosmos.Equivalence.comp (brownFactorizationSection_equivalence f)
      hright.equivalence

end InfinityCosmos
