import Mathlib.CategoryTheory.Bicategory.Kan.Adjunction
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.AbsoluteLifting
import InfinityCosmos.ForMathlib.CategoryTheory.Bicategory.Strict.Closed

/-!
# Colimits in a cartesian closed strict bicategory
-/

universe w v u

namespace CategoryTheory.Bicategory

open MonoidalCategory CartesianMonoidalCategory MonoidalClosed Strict.CartesianMonoidal

variable {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]

namespace Strict.CartesianClosed

variable [Strict.CartesianClosed C]

variable {J A : C}

variable {D : C} (d : D ⟶ J ⟶[C] A)

/-- A cocone over the diagram `d : D ⟶ (J ⟶[C] A)` is a left lift of `d` through the
constant-diagram 1-cell `(const J).app A`. -/
abbrev Cocone := LeftLift ((const J).app A) d

/-- A 1-cell `u : A ⟶ B` carries a cocone over `d : D ⟶ (J ⟶[C] A)` to a cocone over `d ≫ u^J`, by
composing the cocone leg with `u` and using the strict naturality of `const`. -/
def mapCocone {B} (u : A ⟶ B) (c : Cocone d) : Cocone (d ≫ (ihom J).map u) :=
  .mk (c.lift ≫ u) <| c.unit ▷ (ihom J).map u ≫ eqToHom (by
    simp only [Category.assoc]
    exact congrArg (LeftLift.lift c ≫ ·) (const_naturality u).symm)

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

set_option backward.isDefEq.respectTransparency false in
/-- Left adjoints preserve colimits. -/
@[reducible]
noncomputable def preservesColimitOfAdjunction {B : C} {u : A ⟶ B} {f : B ⟶ A}
    (adj : u ⊣ f) : PreservesColimit d u where
  preserves {c} hc _ := by
    -- The adjunction `u^J ⊣ f^J` induced by the cotensor `ihom J`.
    let cotensorAdj : (ihom J).map u ⊣ (ihom J).map f := (ihomPseudofunctor J).mapAdjunction adj
    -- The induced absolute left kan lift of `d` through `f^J`, given by whiskering the unit of
    -- `u^J ⊣ f^J` with `d`.
    let t := (LeftLift.mk ((ihom J).map u) cotensorAdj.unit).whisker d
    have Ht : t.IsAbsKan := LeftLift.IsAbsKan.whisker cotensorAdj.isAbsoluteLeftKanLift d
    -- The induced absolute left kan lift of the colimit 1-cell `c.lift` through `f`, given by
    -- restricting the unit of `u ⊣ f` along `c.lift`.
    let s : LeftLift f c.lift :=
      ((LeftLift.mk u adj.unit).whisker c.lift).ofIso (Iso.refl _) (eqToIso (Strict.comp_id c.lift))
    have Hs : s.IsAbsKan :=
      LeftLift.IsAbsKan.ofIso (LeftLift.IsAbsKan.whisker adj.isAbsoluteLeftKanLift c.lift) _ _
    -- Pasting of the original colimit cocone with the absolute left lift `s`.
    let p := (c.paste s).ofIso (eqToIso (const_naturality f)) (eqToIso (Strict.comp_id d).symm)
    have Hp : p.IsAbsKan := LeftLift.IsAbsKan.ofIso (hc.paste Hs) _ _
    -- Via transposing the cones across the adjunction `u^J ⊣ f^J`, we see that the absolute left
    -- kan lift `p` is isomorphic to `t` pasted with `mapCocone d u c`.
    have key : p ≅ t.paste (mapCocone d u c) := by
      refine StructuredArrow.isoMk (Iso.refl _) ?_
      -- comparison of the two pasted units, collapsing the double right-whisker
      simp only [p, t, s, cotensorAdj, LeftLift.ofIso_unit, LeftLift.paste, mapCocone,
        LeftLift.whisker_unit, StructuredArrow.mk_hom_eq_self, StructuredArrow.mk_right,
        Iso.refl_hom, whiskerLeft_id, Functor.map_id, Strict.associator_eqToIso, eqToIso.hom,
        eqToIso.inv, whiskerLeft_eqToHom, comp_whiskerRight, whiskerRight_whiskerRight_strict,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      -- exchange the two whiskered 2-cells
      rw [whisker_exchange_assoc]
      -- regroup the left whiskering and apply 2-naturality of `const` against the unit
      rw [comp_whiskerLeft, StrictPseudofunctor.mapAdjunction_unit']
      simp [const_naturality₂ adj.unit, Strict.associator_eqToIso, Strict.rightUnitor_eqToIso]
    -- By cancellation, we obtain that `mapCocone d u c` is indeed absolute kan
    exact Ht.ofPaste (Hp.ofIsoAbsKan key)

end Strict.CartesianClosed

end CategoryTheory.Bicategory
