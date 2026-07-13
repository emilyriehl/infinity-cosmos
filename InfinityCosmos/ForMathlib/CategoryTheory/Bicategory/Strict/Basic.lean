import Mathlib.CategoryTheory.Bicategory.EqToHom
import Mathlib.CategoryTheory.Category.Cat
import InfinityCosmos.ForMathlib.CategoryTheory.IsoCat

universe w v u

namespace CategoryTheory.Bicategory

variable {C : Type u} [Bicategory.{w, v} C] [Bicategory.Strict C]

section EqToHom

variable {a b c d : C}

lemma whiskerLeft_whiskerLeft_strict (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η = eqToHom (by simp) ≫ (f ≫ g) ◁ η ≫ eqToHom (by simp) := by
  simp [comp_whiskerLeft, Strict.associator_eqToIso]

lemma whiskerRight_whiskerRight_strict {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    (η ▷ g) ▷ h = eqToHom (by simp) ≫ η ▷ (g ≫ h) ≫ eqToHom (by simp) := by
  simp [whiskerRight_comp, Strict.associator_eqToIso]

end EqToHom

/-- `precomp` is functorial in the precomposed morphism (contravariantly). -/
lemma precomp_comp {X X' X'' : C} (g : X ⟶ X') (f : X' ⟶ X'') (A : C) :
    precomp A (g ≫ f) = precomp A f ⋙ precomp A g :=
  Functor.ext (fun h => by simp) fun h h' φ => by
    simp only [Functor.comp_map, precomp_map, comp_whiskerLeft, Strict.associator_eqToIso,
      eqToIso.hom, eqToIso.inv]
    rfl

/-- Precomposing by an identity is the identity functor on the hom-category. -/
lemma precomp_id (X A : C) : precomp A (𝟙 X) = 𝟭 (X ⟶ A) :=
  Functor.ext (fun h => by simp) fun h h' φ => by simp [precomp, Strict.leftUnitor_eqToIso]

/-- Precomposition by an isomorphism `e : X ≅ X'` of objects of `C` induces an isomorphism of
hom-categories `(X ⟶ A) ≅ (X' ⟶ A)`. -/
def homPrecomposeIso {X X' : C} (e : X ≅ X') (A : C) : IsoCat (X ⟶ A) (X' ⟶ A) where
  functor := precomp A e.inv
  inverse := precomp A e.hom
  unitIso := by rw [← precomp_comp, e.hom_inv_id, precomp_id]
  counitIso := by rw [← precomp_comp, e.inv_hom_id, precomp_id]

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
