/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.CodiscreteCategory

universe u v u' v'

open CategoryTheory Nat

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects called
`zero` and `one`. Perhaps these should have different names?-/
inductive WalkingIso : Type u where
  | zero : WalkingIso
  | one : WalkingIso

open WalkingIso

namespace WalkingIso

/-- The free isomorphism is the codiscrete category on two objects. Can we make this a special
case of the other definition?-/
instance : Category (WalkingIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u'} [Category.{v'} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category.-/
def toIso  (F : WalkingIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map PUnit.unit
  inv := F.map PUnit.unit
  hom_inv_id := by rw [← F.map_comp, ← F.map_id]; rfl
  inv_hom_id := by rw [← F.map_comp, ← F.map_id]; rfl

/-- From an isomorphism in a category, one can build a functor out of `WalkingIso` to
that category.-/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso ⥤ C where
  obj := fun
    | zero => X
    | one => Y
  map := @fun
    | zero, zero, _ => 𝟙 _
    | zero, one,  _ => e.hom
    | one,  zero, _ => e.inv
    | one,  one,  _ => 𝟙 _
  map_comp := by rintro (_ | _) (_ | _) (_ | _) _ _ <;> simp

def equiv : (WalkingIso ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · intro i; cases i <;> rfl
    · intro i j
      simp only [fromIso, toIso]
      cases i <;> cases j <;> intro ⟨⟩ <;> simp only [heq_eq_eq] <;> rw [← F.map_id] <;> rfl

end

def coev (i : WalkingIso) : Fin 1 ⥤ WalkingIso := ComposableArrows.mk₀ i

end WalkingIso

end CategoryTheory

namespace SSet

def coherentIso : SSet.{u} := nerve WalkingIso
namespace coherentIso

open Simplicial SimplicialCategory SSet SimplexCategory Truncated Functor

def pt (i : WalkingIso) : Δ[0] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm (WalkingIso.coev i)

def oneSimplex (X₀ X₁ : WalkingIso) : Δ[1] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm
    (ComposableArrows.mk₁ (X₀ := X₀) (X₁ := X₁) ⟨⟩)

theorem oneSimplex_ext {X₀ X₁ Y₀ Y₁ : WalkingIso} (e₀ : X₀ = Y₀) (e₁ : X₁ = Y₁) :
    oneSimplex X₀ X₁ = oneSimplex Y₀ Y₁ :=
  congrArg (yonedaEquiv coherentIso _).symm (ComposableArrows.ext₁ e₀ e₁ rfl)

def twoSimplex (X₀ X₁ X₂ : WalkingIso) : Δ[2] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm
    (ComposableArrows.mk₂ (X₀ := X₀) (X₁ := X₁) (X₂ := X₂) ⟨⟩ ⟨⟩)

theorem oneSimplex_const (X₀ : WalkingIso) :
    oneSimplex X₀ X₀ = stdSimplex.map ([1].const [0] 0) ≫ pt X₀ := by
  unfold oneSimplex pt
  sorry

theorem twoSimplex_δ0 (X₀ X₁ X₂ : WalkingIso) :
    stdSimplex.δ 0 ≫ twoSimplex X₀ X₁ X₂ = oneSimplex X₁ X₂ := rfl

theorem twoSimplex_δ1 (X₀ X₁ X₂ : WalkingIso) :
    stdSimplex.δ 1 ≫ twoSimplex X₀ X₁ X₂ = oneSimplex X₀ X₂ := by
  unfold twoSimplex oneSimplex
  sorry

theorem twoSimplex_δ2 (X₀ X₁ X₂ : WalkingIso) :
    stdSimplex.δ 2 ≫ twoSimplex X₀ X₁ X₂ = oneSimplex X₀ X₁ := by
  unfold twoSimplex oneSimplex
  sorry



theorem twoSimplex_ext {X₀ X₁ X₂ Y₀ Y₁ Y₂ : WalkingIso}
    (e₀ : X₀ = Y₀) (e₁ : X₁ = Y₁) (e₂ : X₂ = Y₂) : twoSimplex X₀ X₁ X₂ = twoSimplex Y₀ Y₁ Y₂ :=
  congrArg (yonedaEquiv coherentIso _).symm (ComposableArrows.ext₂ e₀ e₁ e₂ rfl rfl)

def hom : Δ[1] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm
    (ComposableArrows.mk₁ (X₀ := WalkingIso.zero) (X₁ := WalkingIso.one) ⟨⟩)

def inv : Δ[1] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm
    (ComposableArrows.mk₁ (X₀ := WalkingIso.one) (X₁ := WalkingIso.zero) ⟨⟩)

def homInvId : Δ[2] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm
    (ComposableArrows.mk₂
      (X₀ := WalkingIso.zero) (X₁ := WalkingIso.one) (X₂ := WalkingIso.zero) ⟨⟩ ⟨⟩)

noncomputable def isPointwiseRightKanExtensionAt (n : ℕ) :
    (rightExtensionInclusion coherentIso 0).IsPointwiseRightKanExtensionAt ⟨[n]⟩ where
  lift s x := sorry
  fac s j := sorry
  uniq s m hm := sorry

noncomputable def isPointwiseRightKanExtension :
    (rightExtensionInclusion coherentIso 0).IsPointwiseRightKanExtension :=
  fun Δ => isPointwiseRightKanExtensionAt Δ.unop.len

theorem isRightKanExtension :
    coherentIso.IsRightKanExtension (𝟙 ((Truncated.inclusion 0).op ⋙ coherentIso)) :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    isPointwiseRightKanExtension

theorem is0Coskeletal : SimplicialObject.IsCoskeletal (n := 0) (coherentIso) where
  isRightKanExtension := isRightKanExtension

def simplex {n : ℕ} (obj : Fin n → WalkingIso) : Δ[n] ⟶ coherentIso := sorry

def simplex_ext {n : ℕ} (obj obj' : Fin n → WalkingIso)
  (hyp : (i : Fin n) → obj i = obj' i) : coherentIso.simplex obj = coherentIso.simplex obj' := sorry

end coherentIso

end SSet
