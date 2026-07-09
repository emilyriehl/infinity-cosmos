/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
import Mathlib.CategoryTheory.Bicategory.Kan.Adjunction
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.AbsoluteLifting
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.Closed

/-!
# Colimits in a cartesian closed strict bicategory

Following [RV], in a cartesian closed strict bicategory `C` a *cocone* over a diagram
`d : D ⟶ (J ⟶[C] A)` is a left lift of `d` through the constant-diagram 1-cell
`const A J : A ⟶ (J ⟶[C] A)`, and a *colimit* cocone is one exhibiting an absolute left Kan
lift. We define these notions and show that a 1-cell admitting a right adjoint preserves
colimits, the dual of [RV] Proposition 2.4.2.

## Main definitions

* `CategoryTheory.Bicategory.Strict.CartesianClosed.const`: the constant-diagram 1-cell
  `Δ : A ⟶ (J ⟶[C] A)`, together with its strict 2-naturality
  (`const_ihom`, `const_whiskerLeft_ihomMap₂`).
* `CategoryTheory.Bicategory.Strict.CartesianClosed.Cocone`, `IsColimit`, `ColimitCocone`,
  `PreservesColimit`: cocones over a diagram and colimit cocones.
* `CategoryTheory.Bicategory.Strict.CartesianClosed.preservesColimitOfAdjunction`: a 1-cell
  admitting a right adjoint preserves colimits.

We also record, for a strict bicategory, the stability of absolute left Kan lifts under
whiskering (`LeftLift.IsAbsKan.whisker`). The transport of (absolute) left Kan lifts along
isomorphisms of their boundary 1-cells (`LeftLift.ofIso`) is in `AbsoluteLifting`, as it needs no
strictness.

## References
* [E. Riehl and D. Verity, *Elements of ∞-Category Theory*][RiehlVerity2022]
-/

universe w v u

namespace CategoryTheory.Bicategory

open MonoidalCategory CartesianMonoidalCategory MonoidalClosed Strict.CartesianMonoidal

variable {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]

namespace LeftLift

set_option backward.isDefEq.respectTransparency false in
/-- Whiskering an absolute left Kan lift yields an absolute left Kan lift. -/
noncomputable def IsAbsKan.whisker {a b x y : C}
    {f : b ⟶ a} {g : x ⟶ a} {t : LeftLift f g} (H : t.IsAbsKan) (h : y ⟶ x) :
    (t.whisker h).IsAbsKan := by
  intro z k
  -- whiskering twice agrees, up to strict associativity, with whiskering by the composite
  have i : (t.whisker (k ≫ h)).ofIso (Iso.refl _) (eqToIso (Strict.assoc k h g)) ≅
      (t.whisker h).whisker k :=
    StructuredArrow.isoMk (eqToIso (Strict.assoc k h t.lift)) (by
      simp only [LeftLift.ofIso_unit, LeftLift.ofIso_lift, Iso.refl_hom, whiskerLeft_id,
        whisker_unit, whisker_lift, Strict.associator_eqToIso,
        eqToIso.hom, eqToIso.inv, eqToHom_map, whiskerLeft_comp, whiskerLeft_eqToHom,
        Category.assoc, eqToHom_trans, Category.comp_id]
      rw [whiskerLeft_whiskerLeft_strict]
      simp)
  exact ((H (k ≫ h)).ofIso (Iso.refl _) (eqToIso (Strict.assoc k h g))).ofIsoKan i

end LeftLift

namespace Strict.CartesianClosed

variable [Strict.CartesianClosed C]

/-- The constant-diagram 1-cell `Δ : A ⟶ (J ⟶[C] A)`, currying the projection. -/
def const (A J : C) : A ⟶ (J ⟶[C] A) := curry (snd J A)

variable {J A : C}

/-- Strict naturality of `const`: `u ≫ Δ_B = Δ_A ≫ u^J`. -/
lemma const_ihom {B} (u : A ⟶ B) : u ≫ const B J = const A J ≫ (ihom J).map u := by
  simp only [const, ← curry_natural_left, ← curry_natural_right, whiskerLeft_snd]

/-- Pasting the naturality squares of `const` for `u` and `f`:
`(u ≫ f) ≫ Δ_A = Δ_A ≫ (u^J ≫ f^J)`. -/
lemma const_ihom_comp {B : C} (u : A ⟶ B) (f : B ⟶ A) :
    (u ≫ f) ≫ const A J = const A J ≫ ((ihom J).map u ≫ (ihom J).map f) := by
  rw [Strict.assoc, const_ihom f, ← Strict.assoc, const_ihom u, Strict.assoc]

/-- Uncurrying `const` gives the projection: `(J ◁ Δ) ≫ ev = snd`. -/
lemma whiskerLeft_const_ev (X : C) : J ◁ const X J ≫ (ihom.ev J).app X = snd J X := by
  rw [const, ← uncurry_eq, uncurry_curry]

set_option backward.isDefEq.respectTransparency false in
/-- For a point `a : 𝟙_ C ⟶ A`, the constant cocone `a ≫ const A J` transposes to the
1-cell constant at `a`, i.e. to the composite `toUnit J ≫ a : J ⟶ A` with the (now trivial)
exponent variable curried back in. -/
lemma transposeIso_point_const (a : 𝟙_ C ⟶ A) :
    (transposeIso J (𝟙_ C) A).functor.obj (a ≫ const A J) =
      toUnit J ≫ a ≫ const A (𝟙_ C) := by
  letI : BraidedCategory C := .ofCartesianMonoidalCategory
  -- both sides become `_ ≫ a` after uncurrying, by uniqueness of the maps to the unit
  have hfwd : (uncurryIso (𝟙_ C) J A).functor.obj (toUnit J ≫ a ≫ const A (𝟙_ C)) =
      (β_ J (𝟙_ C)).inv ≫ (uncurryIso J (𝟙_ C) A).functor.obj (a ≫ const A J) := by
    rw [uncurryIso_functor_obj, uncurryIso_functor_obj]
    simp only [Functor.id_obj, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      whiskerLeft_const_ev, whiskerLeft_snd]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ a) (toUnit_unique _ _)
  show (uncurryIso (𝟙_ C) J A).inverse.obj
      ((β_ J (𝟙_ C)).inv ≫ (uncurryIso J (𝟙_ C) A).functor.obj (a ≫ const A J)) = _
  rw [← hfwd]
  exact (Functor.congr_obj (uncurryIso (𝟙_ C) J A).unitIso _).symm

set_option backward.isDefEq.respectTransparency false in
/-- 2-naturality of `const` against the action of `ihom J` on 2-cells: `Δ` is a strict 2-natural
transformation `𝟭 C ⟶ ihom J`. -/
lemma const_whiskerLeft_ihomMap₂ {X Y : C} {u v : X ⟶ Y} (η : u ⟶ v) :
    const X J ◁ ihomMap₂ J η =
      eqToHom (const_ihom u).symm ≫ η ▷ const Y J ≫ eqToHom (const_ihom v) := by
  apply (uncurryIso J X Y).functor.map_injective
  simp only [Functor.map_comp, eqToHom_map]
  rw [uncurryIso_functor_map, uncurryIso_functor_map, tensorLeftMap₂_whiskerLeft,
    tensorLeftMap₂_whiskerRight]
  simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
  rw [whisker_assoc_strict, tensorLeftMap₂_ihomMap₂_whiskerRight_ev]
  simp only [whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc]
  rw [whiskerLeft_whiskerLeft_strict, congr_whiskerLeft (whiskerLeft_const_ev X) η,
    whiskerRight_whiskerRight_strict, whiskerRight_congr (whiskerLeft_const_ev Y)]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [tensorLeftMap₂_whiskerRight_snd]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- 2-functoriality of the cotensor in its exponent variable (`η^J Δ = Δ η` in the notation of
[RV]): whiskering the unit of the cotensored adjunction with `const A J` recovers the unit of
the original adjunction, up to the strict naturality of `const`. -/
lemma const_whiskerLeft_ihomMapAdjunction_unit {B : C} {u : A ⟶ B} {f : B ⟶ A} (adj : u ⊣ f) :
    const A J ◁ (ihomMapAdjunction J adj).unit =
      eqToHom (by rw [Strict.comp_id, Strict.id_comp]) ≫ adj.unit ▷ const A J ≫
        eqToHom (const_ihom_comp u f) := by
  have h : (ihomMapAdjunction J adj).unit =
      eqToHom ((ihom J).map_id A).symm ≫ ihomMap₂ J adj.unit ≫
        eqToHom ((ihom J).map_comp u f) :=
    StrictPseudofunctor.mapAdjunction_unit (ihomPseudofunctor J) adj
  rw [h]
  simp only [whiskerLeft_comp, whiskerLeft_eqToHom]
  rw [const_whiskerLeft_ihomMap₂ adj.unit]
  simp

variable {D : C} (d : D ⟶ J ⟶[C] A)

/-- A cocone over the diagram `d : D ⟶ (J ⟶[C] A)` is a left lift of `d` through the
constant-diagram 1-cell `const A J`. -/
abbrev Cocone := LeftLift (const A J) d

/-- A 1-cell `u : A ⟶ B` carries a cocone over `d` to a cocone over `d ≫ u^J`, by composing
the cocone leg with `u` and using the strict naturality of `const`. -/
def mapCocone {B} (u : A ⟶ B) (c : Cocone d) : Cocone (d ≫ (ihom J).map u) :=
  .mk (c.lift ≫ u) <|
    c.unit ▷ (ihom J).map u ≫
      eqToHom (by rw [Category.assoc, ← const_ihom u, ← Category.assoc])

variable {d} in
/-- A cocone is a colimit cocone if it is an absolute left Kan lift. -/
abbrev IsColimit (t : Cocone d) := t.IsAbsKan

/-- A 1-cell `u : A ⟶ B` preserves the colimit of `d` if it carries colimit cocones over `d`
to colimit cocones over `d ≫ u^J`. -/
class PreservesColimit {B} (u : A ⟶ B) where
  preserves {c : Cocone d} (hc : IsColimit c) : IsColimit (mapCocone d u c)

/-- A choice of colimit cocone over `d`. -/
structure ColimitCocone where
  /-- The cocone itself -/
  cocone : Cocone d
  /-- The proof that it is the colimit cocone -/
  isColimit : IsColimit cocone

/-- If `u : A ⟶ B` admits a right adjoint `f : B ⟶ A` (with unit `η : 𝟙 A ⟶ u ≫ f`), then `u`
preserves colimits: any absolute left lifting diagram exhibiting a colimit cocone for
`d : D ⟶ J ⟶[C] A` through `const A J` is carried to an absolute left lifting diagram for
`d ≫ (ihom J).map u` through `const B J`.

This is the dual of [RV, Proposition 2.4.2 and (2.4.3)]: there, `u` admits a *left* adjoint and
preserves absolute *right* lifting diagrams (limits); reversing 2-cells gives this statement. -/
@[reducible]
noncomputable def preservesColimitOfAdjunction {B : C} {u : A ⟶ B} {f : B ⟶ A}
    (adj : u ⊣ f) : PreservesColimit d u where
  preserves {c} hc := by
    -- The cotensor `ihom J` carries `u ⊣ f` to `u^J ⊣ f^J` ([RV] Proposition 2.1.7).
    let adjJ : (ihom J).map u ⊣ (ihom J).map f := ihomMapAdjunction J adj
    -- `(u^J, η^J)` is an absolute left lifting of the identity through `f^J`
    -- ([RV] Lemma 2.3.7), and it stays absolute after restriction along `d`.
    let t : LeftLift ((ihom J).map f) (d ≫ 𝟙 (J ⟶[C] A)) :=
      (LeftLift.mk ((ihom J).map u) adjJ.unit).whisker d
    have Ht : t.IsAbsKan := LeftLift.IsAbsKan.whisker adjJ.isAbsoluteLeftKanLift d
    -- Restricting the unit of `u ⊣ f` along the colimit 1-cell gives an absolute left
    -- lifting of `c.lift` through `f`.
    let s : LeftLift f c.lift :=
      ((LeftLift.mk u adj.unit).whisker c.lift).ofIso (Iso.refl _) (eqToIso (Strict.comp_id c.lift))
    have Hs : s.IsAbsKan :=
      LeftLift.IsAbsKan.ofIso (LeftLift.IsAbsKan.whisker adj.isAbsoluteLeftKanLift c.lift)
        (Iso.refl _) (eqToIso (Strict.comp_id c.lift))
    -- Pasting the colimit cocone with it is again absolute ([RV] Lemma 2.4.1, composition);
    -- we transport the pasted diagram along `f ≫ Δ_A = Δ_B ≫ f^J`.
    have Hp : ((c.paste s).ofIso (eqToIso (const_ihom f))
        (eqToIso (Strict.comp_id d).symm)).IsAbsKan :=
      LeftLift.IsAbsKan.ofIso (hc.paste Hs) (eqToIso (const_ihom f))
        (eqToIso (Strict.comp_id d).symm)
    -- Key comparison: by 2-functoriality of the cotensor in the exponent variable
    -- (`f^J Δ = Δ f` and `η^J Δ = Δ η`, see `const_whiskerLeft_ihomMapAdjunction_unit`),
    -- the pasted diagram above agrees with the transposed cone, i.e. with the pasting of
    -- the image cocone `mapCocone d u c` onto the restricted lifting `t`.
    have key : (c.paste s).ofIso (eqToIso (const_ihom f)) (eqToIso (Strict.comp_id d).symm) ≅
        t.paste (mapCocone d u c) := by
      refine StructuredArrow.isoMk (Iso.refl _) ?_
      -- comparison of the two pasted units, collapsing the double right-whisker
      simp only [t, s, adjJ, LeftLift.ofIso_unit, LeftLift.ofIso_lift, LeftLift.paste, mapCocone,
        LeftLift.whisker_unit, LeftLift.whisker_lift, StructuredArrow.mk_hom_eq_self,
        StructuredArrow.mk_right, Iso.refl_hom, whiskerLeft_id, Functor.map_id, Category.comp_id,
        Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
        whiskerLeft_eqToHom, comp_whiskerRight, eqToHom_whiskerRight,
        whiskerRight_whiskerRight_strict, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      -- exchange the two whiskered 2-cells
      rw [whisker_exchange_assoc]
      -- regroup the left whiskering and apply 2-naturality of `const`
      rw [comp_whiskerLeft_strict, const_whiskerLeft_ihomMapAdjunction_unit adj,
        whisker_assoc_strict]
      simp [Strict.rightUnitor_eqToIso]
    -- Cancel the absolute lifting `t` ([RV] Lemma 2.4.1, cancelation).
    intro x h
    exact Ht.ofPaste (Hp.ofIsoAbsKan key) h

end Strict.CartesianClosed

end CategoryTheory.Bicategory
