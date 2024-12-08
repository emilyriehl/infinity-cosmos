import Mathlib.CategoryTheory.Enriched.Ordinary

universe v' v u u'

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

def eHomWhiskerLeftIso (X : C) {Y Y' : C} (i : Y ≅ Y') :
    (X ⟶[V] Y) ≅ (X ⟶[V] Y') where
  hom := eHomWhiskerLeft V X i.hom
  inv := eHomWhiskerLeft V X i.inv
  hom_inv_id := by
    rw [← eHomWhiskerLeft_comp, i.hom_inv_id, eHomWhiskerLeft_id]
  inv_hom_id := by
    rw [← eHomWhiskerLeft_comp, i.inv_hom_id, eHomWhiskerLeft_id]

def eHomWhiskerRightIso {X X' : C} (i : X ≅ X') (Y : C) :
    (X' ⟶[V] Y) ≅ (X ⟶[V] Y) where
  hom := eHomWhiskerRight V i.hom Y
  inv := eHomWhiskerRight V i.inv Y
  hom_inv_id := by
    rw [← eHomWhiskerRight_comp, i.inv_hom_id, eHomWhiskerRight_id]
  inv_hom_id := by
    rw [← eHomWhiskerRight_comp, i.hom_inv_id, eHomWhiskerRight_id]

end CategoryTheory
