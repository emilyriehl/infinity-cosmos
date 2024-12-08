/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JHU Category Theory Seminar
-/
import InfinityCosmos.ForMathlib.InfinityCosmos.Basic

/-!
# Explicit isofibrations in an ∞-cosmos.

This file constructs a few explicit isofibrations in an ∞-cosmos as consequences of the axioms.

-/

namespace InfinityCosmos

universe u v

open CategoryTheory Category PreInfinityCosmos SimplicialCategory Limits InfinityCosmos

variable {K : Type u} [Category.{v} K] [InfinityCosmos K]

section products

def compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C :=
  ⟨(f.1 ≫ g.1), comp_isIsofibration f g⟩

theorem toTerminal_fibrant (A : K) : IsIsofibration (terminal.from A) :=
  all_objects_fibrant terminalIsTerminal _

theorem binary_prod_map_fibrant {X Y X' Y' : K} {f : X ↠ Y} {g : X' ↠ Y'} :
    IsIsofibration (prod.map f.1 g.1) := by sorry

end products
section terminal

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.
noncomputable def cotensorInitialIso (A : K) : (⊥_ SSet ) ⋔ A ≅ ⊤_ K where
  hom := terminal.from ((⊥_ SSet) ⋔ A)
  inv := (cotensor.iso.underlying (⊥_ SSet) A (⊤_ K)).symm (initial.to (sHom (⊤_ K) A))
  hom_inv_id := (cotensor.iso.underlying (⊥_ SSet) A ((⊥_ SSet ) ⋔ A)).injective
    (initial.hom_ext _ _)
  inv_hom_id := terminal.hom_ext _ _

noncomputable instance cotensorInitial_isTerminal (A : K) : IsTerminal ((⊥_ SSet ) ⋔ A) :=
  terminalIsTerminal.ofIso (cotensorInitialIso A).symm

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.
noncomputable def cotensorToTerminalIso (U : SSet) {T : K} (hT : IsTerminal T) : U ⋔ T ≅ ⊤_ K where
  hom := terminal.from _
  inv := (cotensor.iso.underlying U T (⊤_ K)).symm (by sorry)
  hom_inv_id := (cotensor.iso.underlying U T (U ⋔ T)).injective
    (by sorry)
  inv_hom_id := terminal.hom_ext _ _

noncomputable instance cotensorToTerminal_isTerminal (U : SSet) {T : K} (hT : IsTerminal T) :
    IsTerminal (U ⋔ T) := terminalIsTerminal.ofIso (cotensorToTerminalIso U hT).symm

end terminal

lemma initialSquare_isIso {A B : K} (f : A ⟶ B) : IsIso (cotensorCovMap (⊥_ SSet) f) :=
  isIso_of_isTerminal (cotensorInitial_isTerminal A) (cotensorInitial_isTerminal B)
    (cotensorCovMap (⊥_ SSet) f)

lemma initialSquare_isPullback (V : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsPullback (terminal.from (V ⋔ B) ≫ (cotensorInitialIso A).inv) (𝟙 _)
      (cotensorCovMap (⊥_ SSet) f.1) (cotensorContraMap (initial.to V) B) := by
  have := initialSquare_isIso f.1
  refine IsPullback.of_vert_isIso ?_
  constructor
  apply IsTerminal.hom_ext (cotensorInitial_isTerminal _)

theorem cotensorCovMap_fibrant (V : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsIsofibration (cotensorCovMap V f.1) := by
  have := Initial.mono_to V
  have := leibniz_cotensor (initial.to V) f _ _ (initialSquare_isPullback V f)
  have := IsPullback.lift_snd (initialSquare_isPullback V f) (cotensorContraMap (initial.to V) A)
    (cotensorCovMap V f.1) (cotensor_bifunctoriality (initial.to V) f.1)
  rw [comp_id] at this
  rw [← this]
  exact (leibniz_cotensor (initial.to V) f _ _ (initialSquare_isPullback V f))

theorem cotensorContraMap_fibrant {U V : SSet} (i : U ⟶ V) [Mono i] (A : K) :
    IsIsofibration (cotensorContraMap i A) := sorry

  -- leibniz_cotensor  {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) {P : K}
  --   (fst : P ⟶ U ⋔ A) (snd : P ⟶ V ⋔ B)
  --   (h : IsPullback fst snd (cotensorCovMap U f.1) (cotensorContraMap i B)) :
  --   IsIsofibration (h.isLimit.lift <|
  --     PullbackCone.mk (cotensorContraMap i A) (cotensorCovMap V f.1)
  --       (cotensor_bifunctoriality i f.1)) --TODO : Prove that these pullbacks exist.


end InfinityCosmos
