/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
import Mathlib.CategoryTheory.Closed.Enrichment

/-!

# The monoidal product of enriched categories

When a monoidal category `V` is braided, we may define the monoidal product of
`V`-categories `C` and `D`, which is a `V`-category structure on the product type `C × D`.
The "middle-four exchange" map (known as `tensor_μ`) is required to define the composition morphism.

-/

universe u₁ u₂ u₃ u₄ v₁

namespace CategoryTheory

open MonoidalCategory

/-- The underlying type of the enriched tensor product of categories -/
@[nolint unusedArguments]
structure enrichedTensor (V : Type u₁) (C : Type u₂) (D : Type u₃) where
  pr₁ : C
  pr₂ : D

namespace enrichedTensor

notation C " ⊗[" V "] " D:10 => enrichedTensor V C D

def of_prod (V : Type u₁) {C : Type u₂} {D : Type u₃} (p : C × D) : enrichedTensor V C D :=
  ⟨p.1, p.2⟩

def to_prod (V : Type u₁) {C : Type u₂} {D : Type u₃} (q : C ⊗[V] D) : C × D := ⟨q.pr₁, q.pr₂⟩

@[simp]
theorem to_of_prod (V : Type u₁) {C : Type u₂} {D : Type u₃} (p : C × D) :
  to_prod V (of_prod V p) = p := rfl

@[simp]
theorem of_to_prod (V : Type u₁) {C : Type u₂} {D : Type u₃} (p : C ⊗[V] D) :
  of_prod V (to_prod V p) = p := rfl

/-- The type-level equivalence between the product type and the enriched tensor. -/
def equivToEnrichedOpposite (V : Type u₁) (C : Type u₂) (D : Type u₃) :
    C × D ≃ C ⊗[V] D where
  toFun := of_prod V
  invFun := to_prod V
  left_inv := congrFun rfl
  right_inv := congrFun rfl

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
variable (C : Type u₂) [EnrichedCategory V C]
variable (D : Type u₃) [EnrichedCategory V D]

-- Helper lemma for Bifunc.mk
lemma comp_tensor_comp_eq_comp_mid_left_right {a b c d e : C} :
    ((eComp V a b c) ⊗ₘ (eComp V c d e)) ≫ eComp V a c e =
      (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv ≫ _ ◁ ((eComp V b c d) ▷ _) ≫ _ ◁ (eComp V b d e) ≫
        eComp V a b e := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc, e_assoc, MonoidalCategory.whiskerLeft_comp]
  rw [← associator_naturality_right_assoc, e_assoc', ← tensorHom_def'_assoc]

section

variable [BraidedCategory V]

instance : EnrichedCategory V (C ⊗[V] D) where
  Hom := fun ⟨c, d⟩ ⟨c', d'⟩ => EnrichedCategory.Hom c c' ⊗ EnrichedCategory.Hom d d'
  id := fun ⟨c, d⟩ => (λ_ (𝟙_ V)).inv ≫ (EnrichedCategory.id c ⊗ₘ EnrichedCategory.id d)
  comp := fun ⟨c, d⟩ ⟨c', d'⟩ ⟨c'', d''⟩ =>
    tensorμ _ _ _ _ ≫ (EnrichedCategory.comp c c' c'' ⊗ₘ EnrichedCategory.comp d d' d'')
  id_comp := fun ⟨c, d⟩ ⟨c', d'⟩ => by
    simp only [comp_whiskerRight_assoc, tensorμ_natural_left_assoc]
    have := tensor_left_unitality (EnrichedCategory.Hom c c' : V) (EnrichedCategory.Hom d d')
    rw [← Category.assoc] at this
    have := (Iso.comp_inv_eq
      (tensorIso (λ_ (EnrichedCategory.Hom c c')) (λ_ (EnrichedCategory.Hom d d')))).mpr this
    slice_lhs 2 3 => rw [← this]
    simp only [tensorIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, EnrichedCategory.id_comp, EnrichedCategory.id_comp]
    exact id_tensorHom_id (c ⟶[V] c') (d ⟶[V] d')
  comp_id := fun ⟨c, d⟩ ⟨c', d'⟩ => by
    simp only [MonoidalCategory.whiskerLeft_comp_assoc, tensorμ_natural_right_assoc]
    have := tensor_right_unitality (EnrichedCategory.Hom c c' : V) (EnrichedCategory.Hom d d')
    rw [← Category.assoc] at this
    have := (Iso.comp_inv_eq
      (tensorIso (ρ_ (EnrichedCategory.Hom c c')) (ρ_ (EnrichedCategory.Hom d d')))).mpr this
    slice_lhs 2 3 => rw [← this]
    simp only [tensorIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, EnrichedCategory.comp_id, EnrichedCategory.comp_id]
    exact id_tensorHom_id (c ⟶[V] c') (d ⟶[V] d')
  assoc := fun ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ ⟨c₃, d₃⟩ ⟨c₄, d₄⟩ => by
    simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
      tensorμ_natural_left_assoc, tensorμ_natural_right_assoc]
    apply (Iso.inv_comp_eq _).mpr
    rw [← tensor_associativity_assoc]
    repeat rw [tensorHom_comp_tensorHom]
    rw [(Iso.inv_comp_eq _).mp (@EnrichedCategory.assoc V _ _ C _ c₁ c₂ c₃ c₄),
      (Iso.inv_comp_eq _).mp (@EnrichedCategory.assoc V _ _ D _ d₁ d₂ d₃ d₄)]

end

variable [SymmetricCategory V]

-- Look up if there is an analogous lemma for the unenriched setting
def eBifuncConstr {E : Type u₄} [EnrichedCategory V E]
    (F_obj : C → D → E)
    (F_map_left : (c c' : C) → (d : D) →
      (c ⟶[V] c') ⟶ EnrichedCategory.Hom (F_obj c d) (F_obj c' d))
    (F_map_right : (c : C) → (d d' : D) →
      (d ⟶[V] d') ⟶ EnrichedCategory.Hom (F_obj c d) (F_obj c d'))
    (F_id_left : (c : C) → (d : D) →
      eId V c ≫ F_map_left c c d = eId V _)
    (F_id_right : (c : C) → (d : D) →
      eId V d ≫ F_map_right c d d = eId V _)
    (F_comp_left : (c c' c'' : C) → (d : D) →
      eComp V c c' c'' ≫ F_map_left c c'' d = ((F_map_left c c' d) ⊗ₘ (F_map_left c' c'' d)) ≫ eComp V ..)
    (F_comp_right : (c : C) → (d d' d'' : D) →
      eComp V d d' d'' ≫ F_map_right c d d'' = ((F_map_right c d d') ⊗ₘ (F_map_right c d' d'')) ≫ eComp V ..)
    (F_left_right_naturality : (c c' : C) → (d d' : D) →
      ((F_map_left c c' d) ⊗ₘ (F_map_right c' d d')) ≫ eComp V _ _ _ = ((F_map_left c c' d') ⊗ₘ (F_map_right c d d')) ≫ (β_ _ _).hom ≫ eComp V ..)
    : EnrichedFunctor V (C ⊗[V] D) E where
  obj p := F_obj p.pr₁ p.pr₂
  map p q := ((F_map_left p.pr₁ q.pr₁ p.pr₂) ⊗ₘ (F_map_right q.pr₁ p.pr₂ q.pr₂)) ≫ eComp V ..
  map_id p := by
    have : eId V p = (λ_ _).inv ≫ ((eId V p.pr₁) ⊗ₘ (eId V p.pr₂)) := rfl
    simp only [this, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc, F_id_left, F_id_right, tensorHom_def', Category.assoc,
      ← leftUnitor_inv_naturality_assoc, e_id_comp]
    exact Category.comp_id (eId V (F_obj p.pr₁ p.pr₂))
  map_comp p q r := by
    have : eComp V p q r = tensorμ _ _ _ _ ≫
      (tensorHom (eComp V p.pr₁ q.pr₁ r.pr₁) (eComp V p.pr₂ q.pr₂ r.pr₂)) := rfl
    simp only [this, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc, F_comp_left, F_comp_right]
    repeat rw [← tensorHom_comp_tensorHom_assoc]
    rw [comp_tensor_comp_eq_comp_mid_left_right]
    simp only [associator_naturality_assoc]
    rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, associator_inv_naturality]
    have F_left_id : F_map_left p.pr₁ q.pr₁ p.pr₂ ≫ 𝟙 _ = 𝟙 _ ≫ F_map_left p.pr₁ q.pr₁ p.pr₂ := by
      aesop_cat
    rw [F_left_id, ← tensorHom_comp_tensorHom_assoc, ← tensorHom_id, ← id_tensorHom]
    nth_rw 2 [tensorHom_comp_tensorHom_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [F_left_right_naturality]
    rw [BraidedCategory.braiding_naturality_assoc]
    have F_right_id : F_map_right r.pr₁ q.pr₂ r.pr₂ ≫ 𝟙 _ = 𝟙 _ ≫ F_map_right r.pr₁ q.pr₂ r.pr₂ := by
      aesop_cat
    rw [F_right_id, ← tensorHom_comp_tensorHom, F_left_id, ← tensorHom_comp_tensorHom]
    simp only [id_tensorHom, tensorHom_id]
    unfold tensorμ
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
    nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.comp_whiskerRight, SymmetricCategory.symmetry]
    simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [tensorHom_def, @tensorHom_def' V _ _ _ _ _ _
      ((F_map_right q.pr₁ p.pr₂ q.pr₂ ⊗ₘ F_map_left q.pr₁ r.pr₁ q.pr₂) ≫
        eComp V (F_obj q.pr₁ p.pr₂) (F_obj q.pr₁ q.pr₂) (F_obj r.pr₁ q.pr₂))
          (F_map_right r.pr₁ q.pr₂ r.pr₂)]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    nth_rw 3 [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← e_assoc', MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
    nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc, ← tensorHom_id]
    rw [associator_naturality, MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, associator_naturality_right,
        MonoidalCategory.whiskerLeft_comp_assoc, ← whisker_exchange_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
            MonoidalCategory.whiskerLeft_id, Category.id_comp, ← e_assoc,
              associator_inv_naturality_right_assoc]
    nth_rw 4 [← id_tensorHom]
    rw [associator_inv_naturality_assoc, associator_inv_naturality_right_assoc,
      associator_inv_naturality_left_assoc, Iso.hom_inv_id_assoc, ← tensorHom_id, ← tensorHom_id,
        ← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id, Category.id_comp, id_tensorHom, tensorHom_id]
    rw [← tensorHom_def, ← tensorHom_def', ← tensorHom_def'_assoc]

end enrichedTensor

end CategoryTheory
