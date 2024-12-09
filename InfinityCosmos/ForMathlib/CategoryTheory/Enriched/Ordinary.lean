import Mathlib.CategoryTheory.Enriched.Ordinary

universe v' v u u'

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

@[simps]
def eHomCongr {X X' Y Y' : C} (α : X ≅ X') (β : Y ≅ Y') :
    (X ⟶[V] Y) ≅ (X' ⟶[V] Y') where
  hom := eHomWhiskerLeft V X β.hom ≫ eHomWhiskerRight V α.inv Y'
  inv := eHomWhiskerLeft V X' β.inv ≫ eHomWhiskerRight V α.hom Y
  hom_inv_id := by
    rw [eHom_whisker_exchange, assoc, ← assoc (eHomWhiskerLeft V X' β.hom)]
    rw [← eHomWhiskerLeft_comp, β.hom_inv_id, eHomWhiskerLeft_id, id_comp]
    rw [← eHomWhiskerRight_comp, α.hom_inv_id, eHomWhiskerRight_id]
  inv_hom_id := by
    rw [eHom_whisker_exchange, assoc, ← assoc (eHomWhiskerLeft V X β.inv)]
    rw [← eHomWhiskerLeft_comp, β.inv_hom_id, eHomWhiskerLeft_id, id_comp]
    rw [← eHomWhiskerRight_comp, α.inv_hom_id, eHomWhiskerRight_id]

end CategoryTheory
