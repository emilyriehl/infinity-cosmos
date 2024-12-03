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

def compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C :=
  ⟨(f.1 ≫ g.1), comp_isIsofibration f g⟩

theorem toTerminal_fibrant (A : K) : IsIsofibration (terminal.from A) :=
  all_objects_fibrant terminalIsTerminal _

theorem binary_prod_map_fibrant {X Y X' Y' : K} {f : X ↠ Y} {g : X' ↠ Y'} :
    IsIsofibration (prod.map f.1 g.1) := by sorry

section terminal

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.
noncomputable def cotensorInitialIso (A : K) : (⊥_ SSet ) ⋔ A ≅ ⊤_ K where
  hom := terminal.from ((⊥_ SSet) ⋔ A)
  inv := (cotensor.iso.underlying (⊥_ SSet) A (⊤_ K)).symm (initial.to (sHom (⊤_ K) A))
  hom_inv_id := (cotensor.iso.underlying (⊥_ SSet) A ((⊥_ SSet ) ⋔ A)).injective
    (initial.hom_ext _ _)
  inv_hom_id := terminal.hom_ext _ _

noncomputable instance cotensorInitial_isTerminal (A : K) : IsTerminal ((⊥_ SSet ) ⋔ A) :=
  terminalIsTerminal.ofIso (id (cotensorInitialIso A).symm)

end terminal

lemma initialSquare_isPullback' (U : SSet.{v}) (B : K) :
    IsPullback  (cotensorContraMap (initial.to U) B) (𝟙 _)
    (𝟙 _) (cotensorContraMap (initial.to U) B) := IsPullback.of_id_snd


noncomputable def initialSquare.snd (U : SSet.{v}) (A B : K) : U ⋔ B ⟶ (⊥_ SSet ) ⋔ A :=
  terminal.from (U ⋔ B) ≫ (cotensorInitialIso A).inv

lemma initialSquare_isIso {A B : K} (f : A ⟶ B) : IsIso (cotensorCovMap (⊥_ SSet) f) :=
  isIso_of_isTerminal (cotensorInitial_isTerminal A) (cotensorInitial_isTerminal B)
    (cotensorCovMap (⊥_ SSet) f)

lemma initialSquare_isPullback (U : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsPullback (𝟙 _) (initialSquare.snd U A B)
      (cotensorContraMap (initial.to U) B) (cotensorCovMap (⊥_ SSet) f.1) := by
  have := initialSquare_isIso f.1
  refine IsPullback.of_horiz_isIso ?_
  unfold initialSquare.snd
  constructor
  apply IsTerminal.hom_ext (cotensorInitial_isTerminal _)

theorem cotensorCovMap_fibrant (U : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsIsofibration (cotensorCovMap U f.1) := by
  let map : ⊥_ SSet ⟶ U := initial.to U
  have hyp : Mono map := Initial.mono_to U
  have := leibniz_cotensor (initial.to U) f _ _ (initialSquare_isPullback U f)
  have := IsPullback.lift_fst (initialSquare_isPullback U f) (cotensorCovMap U f.1)
    (cotensorContraMap (initial.to U) A) (cotensor_bifunctoriality (initial.to U) f.1)
  simp only [comp_id] at this
  rw [← this]
  exact (leibniz_cotensor (initial.to U) f _ _ (initialSquare_isPullback U f))

end InfinityCosmos
