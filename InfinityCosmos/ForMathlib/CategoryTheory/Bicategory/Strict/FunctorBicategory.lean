import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# The bicategory of strict pseudofunctors

Given a bicategory `B` and a strict bicategory `C`, we define a bicategory structure on
`StrictPseudofunctor B C` whose
* objects are strict pseudofunctors,
* 1-morphisms are strong natural transformations (of the underlying pseudofunctors), and
* 2-morphisms are modifications.

Moreover, when `C` is strict this bicategory is itself strict.

We scope this instance to the `CategoryTheory.StrictPseudofunctor` namespace to avoid potential
future conflicts with other bicategory instances on `StrictPseudofunctor B C`.

This follows the construction in `Mathlib/CategoryTheory/Bicategory/FunctorBicategory/Pseudo.lean`
for the bicategory of pseudofunctors.
-/

set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.StrictPseudofunctor

open Bicategory Pseudofunctor
open scoped Pseudofunctor.StrongTrans

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- Two isomorphisms are heterogeneously equal if their endpoints agree and the forward maps
agree after the corresponding transport. -/
theorem _root_.CategoryTheory.Iso.heq_of_hom_eq {D : Type*} [Category D] {X Y X' Y' : D}
    {i : X ≅ Y} {j : X' ≅ Y'} (hX : X = X') (hY : Y = Y')
    (h : i.hom = eqToHom hX ≫ j.hom ≫ eqToHom hY.symm) : i ≍ j := by
  subst hX; subst hY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact heq_of_eq (Iso.ext h)

/-- Two strong transformations of pseudofunctors are equal if their components agree and their
naturality constraints are (heterogeneously) equal. -/
theorem _root_.CategoryTheory.Pseudofunctor.StrongTrans.hext {F G : Pseudofunctor B C}
    {η θ : Pseudofunctor.StrongTrans F G} (happ : ∀ a, η.app a = θ.app a)
    (hnat : ∀ {a b} (f : a ⟶ b), η.naturality f ≍ θ.naturality f) : η = θ := by
  obtain ⟨ηa, ηn, _, _, _⟩ := η
  obtain ⟨θa, θn, _, _, _⟩ := θ
  have ha : ηa = θa := funext happ
  subst ha
  have hn : @ηn = @θn := by funext a b f; exact eq_of_heq (hnat f)
  subst hn
  rfl

variable (B C) in
/-- `CategoryStruct` on `StrictPseudofunctor B C`, where the 1-morphisms are given by strong
transformations of the underlying pseudofunctors.

Note that this instance is scoped to the `StrictPseudofunctor` namespace. -/
scoped instance categoryStruct : CategoryStruct (StrictPseudofunctor B C) where
  Hom F G := F.toPseudofunctor ⟶ G.toPseudofunctor
  id F := 𝟙 F.toPseudofunctor
  comp η θ := η ≫ θ

open Pseudofunctor.StrongTrans in
@[simp]
lemma id_app (F : StrictPseudofunctor B C) (a : B) :
    Pseudofunctor.StrongTrans.app (𝟙 F) a = 𝟙 (F.obj a) := rfl

open Pseudofunctor.StrongTrans in
@[simp]
lemma comp_app {F G H : StrictPseudofunctor B C} (η : F ⟶ G) (θ : G ⟶ H) (a : B) :
    Pseudofunctor.StrongTrans.app (η ≫ θ) a =
      Pseudofunctor.StrongTrans.app η a ≫ Pseudofunctor.StrongTrans.app θ a := rfl

lemma id_naturality (F : StrictPseudofunctor B C) {a b : B} (f : a ⟶ b) :
    Pseudofunctor.StrongTrans.naturality (𝟙 F) f = ρ_ (F.map f) ≪≫ (λ_ (F.map f)).symm := rfl

lemma comp_naturality {F G H : StrictPseudofunctor B C} (η : F ⟶ G) (θ : G ⟶ H) {a b : B}
    (f : a ⟶ b) : Pseudofunctor.StrongTrans.naturality (η ≫ θ) f =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫ α_ _ _ _ ≪≫
        whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm := rfl

variable (B C) in
/-- A bicategory structure on strict pseudofunctors, with strong transformations as 1-morphisms.

Note that this instance is scoped to the `StrictPseudofunctor` namespace. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
scoped instance bicategory : Bicategory (StrictPseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := StrongTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := StrongTrans.whiskerRight Γ η
  associator {F G H} I := StrongTrans.associator
  leftUnitor {F G} := StrongTrans.leftUnitor
  rightUnitor {F G} := StrongTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ :=
    @Bicategory.whisker_exchange (Pseudofunctor B C) _ _ _ _ _ _ _ _ η θ
  whiskerLeft_id {a b c} f g := @Bicategory.whiskerLeft_id (Pseudofunctor B C) _ _ _ _ f g
  whiskerLeft_comp {a b c} f g h i η θ :=
    @Bicategory.whiskerLeft_comp (Pseudofunctor B C) _ _ _ _ f g h i η θ
  id_whiskerLeft {a b} f g η := @Bicategory.id_whiskerLeft (Pseudofunctor B C) _ _ _ f g η
  comp_whiskerLeft {a b c d} f g h h' η :=
    @Bicategory.comp_whiskerLeft (Pseudofunctor B C) _ _ _ _ _ f g h h' η
  id_whiskerRight {a b c} f g := @Bicategory.id_whiskerRight (Pseudofunctor B C) _ _ _ _ f g
  comp_whiskerRight {a b c} f g h η θ i :=
    @Bicategory.comp_whiskerRight (Pseudofunctor B C) _ _ _ _ f g h η θ i
  whiskerRight_id {a b} f g η := @Bicategory.whiskerRight_id (Pseudofunctor B C) _ _ _ f g η
  whiskerRight_comp {a b c d} f g h h' η :=
    @Bicategory.whiskerRight_comp (Pseudofunctor B C) _ _ _ _ _ f g h h' η
  whisker_assoc {a b c d} f g g' η h :=
    @Bicategory.whisker_assoc (Pseudofunctor B C) _ _ _ _ _ f g g' η h
  pentagon {a b c d e} f g h i :=
    @Bicategory.pentagon (Pseudofunctor B C) _ _ _ _ _ _ f g h i
  triangle {a b c} f g := @Bicategory.triangle (Pseudofunctor B C) _ _ _ _ f g

@[simp]
lemma eqToHom_as_app {F G : StrictPseudofunctor B C} {η θ : F ⟶ G} (h : η = θ) (a : B) :
    (eqToHom h).as.app a = eqToHom (by rw [h]) := by
  subst h; rfl

variable (B C) in
/-- When `C` is a strict bicategory, the bicategory of strict pseudofunctors from `B` to `C` is
strict. -/
scoped instance strict [Strict C] : Strict (StrictPseudofunctor B C) where
  id_comp η := by
    apply Pseudofunctor.StrongTrans.hext
    · intro a; simp
    · intro a b f
      refine Iso.heq_of_hom_eq (by simp) (by simp) ?_
      simp [comp_naturality, id_naturality, Strict.associator_eqToIso,
        Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
  comp_id η := by
    apply Pseudofunctor.StrongTrans.hext
    · intro a; simp
    · intro a b f
      refine Iso.heq_of_hom_eq (by simp) (by simp) ?_
      simp [comp_naturality, id_naturality, Strict.associator_eqToIso,
        Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
  assoc η θ ι := by
    apply Pseudofunctor.StrongTrans.hext
    · intro a; simp
    · intro a b f
      refine Iso.heq_of_hom_eq (by simp) (by simp) ?_
      simp [comp_naturality, Strict.associator_eqToIso]
  leftUnitor_eqToIso η := by
    apply Iso.ext
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    simp [Strict.leftUnitor_eqToIso]
  rightUnitor_eqToIso η := by
    apply Iso.ext
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    simp [Strict.rightUnitor_eqToIso]
  associator_eqToIso η θ ι := by
    apply Iso.ext
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    simp [Strict.associator_eqToIso]

end CategoryTheory.StrictPseudofunctor
