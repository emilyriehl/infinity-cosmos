import Mathlib.CategoryTheory.Bicategory.EqToHom
import Mathlib.CategoryTheory.Category.Cat

universe w v u

namespace CategoryTheory.Bicategory

variable {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]

section EqToHom

variable {a b c d : C}

lemma whiskerLeft_whiskerLeft_strict (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η = eqToHom (by simp) ≫ (f ≫ g) ◁ η ≫ eqToHom (by simp) := by
  simp [comp_whiskerLeft, Strict.associator_eqToIso]

lemma comp_whiskerLeft_strict (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η = eqToHom (by simp) ≫ f ◁ g ◁ η ≫ eqToHom (by simp) := by
  simp [comp_whiskerLeft, Strict.associator_eqToIso]

lemma whiskerRight_comp_strict {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) = eqToHom (by simp) ≫ (η ▷ g) ▷ h ≫ eqToHom (by simp) := by
  simp [whiskerRight_comp, Strict.associator_eqToIso]

lemma whiskerRight_whiskerRight_strict {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    (η ▷ g) ▷ h = eqToHom (by simp) ≫ η ▷ (g ≫ h) ≫ eqToHom (by simp) := by
  simp [whiskerRight_comp, Strict.associator_eqToIso]

lemma whisker_assoc_strict (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h = eqToHom (by simp) ≫ f ◁ (η ▷ h) ≫ eqToHom (by simp) := by
  simp [whisker_assoc, Strict.associator_eqToIso]

end EqToHom

variable (C)

set_option backward.isDefEq.respectTransparency false in
/-- The hom functor `Cᵒᵖ ⥤ C ⥤ Cat` of a strict bicategory. -/
def homFunctor : Cᵒᵖ ⥤ C ⥤ Cat where
  obj X :=
    { obj Y := Cat.of (X.unop ⟶ Y)
      map φ := (postcomp X.unop φ).toCatHom
      map_id _ := Cat.ext <| Functor.ext (fun _ ↦ by simp)
        fun _ _ _ ↦ by simp [Functor.toCatHom, Strict.rightUnitor_eqToIso]
      map_comp _ _ := Cat.ext <| Functor.ext (fun _ ↦ by simp)
        fun _ _ _ ↦ by simp [Functor.toCatHom, Strict.associator_eqToIso] }
  map φ :=
    { app Y := (precomp Y φ.unop).toCatHom
      naturality _ _ _ := Cat.ext <| Functor.ext (fun _ ↦ by simp)
        fun _ _ _ ↦ by simp [Functor.toCatHom, Strict.associator_eqToIso] }
  map_id _ := by
    ext
    exact Functor.ext (fun _ ↦ by simp) fun _ _ _ ↦ by
      simp [Functor.toCatHom, Strict.leftUnitor_eqToIso]
  map_comp _ _ := by
    ext
    exact Functor.ext (fun _ ↦ by simp) fun _ _ _ ↦ by
      simp [Functor.toCatHom, Strict.associator_eqToIso]

end CategoryTheory.Bicategory
