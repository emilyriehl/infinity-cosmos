/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.CodiscreteCategory

universe u v u' v'

open CategoryTheory Nat

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects called
`zero` and `one`. -/
inductive WalkingIso : Type u where
  | zero : WalkingIso
  | one : WalkingIso

open WalkingIso

namespace WalkingIso

/-- The free isomorphism is the codiscrete category on two objects. Can we make this a special
case of the other definition? -/
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

/-- Because the coherent iso is 0-coskeletal, an n-simplex in it can be defined by a sequence
of objects. -/
def simplex {n : ℕ} (obj : Fin (n + 1) → WalkingIso) : Δ[n] ⟶ coherentIso := by
  refine (yonedaEquiv coherentIso _).symm ?_
  exact {
    obj := obj
    map := fun _ => ⟨⟩
  }

abbrev get_map {k n : ℕ} (res : Fin (k + 1) →o Fin (n + 1)) : Δ[k] ⟶ Δ[n] :=
  stdSimplex.map <| mkHom res

theorem simplex_ext {n : ℕ} (obj obj' : Fin (n + 1) → WalkingIso) (e : obj = obj') :
    simplex obj = simplex obj' :=
  congrArg (yonedaEquiv coherentIso _).symm
    (ComposableArrows.ext (fun i => congrFun e i) (fun _ _ => rfl))

theorem simplex_map {n m : ℕ}
    (obj : Fin (n + 1) → WalkingIso) (α : ([m] : SimplexCategory) ⟶ [n]) :
    stdSimplex.map α ≫ simplex obj = simplex (obj ∘ α.toOrderHom) := rfl

noncomputable def pushout_simplex {n m k : ℕ} (obj : Fin (n + 1) → WalkingIso)
  (obj' : Fin (m + 1) → WalkingIso) (res : Fin (k + 1) →o Fin ( n + 1 ))
  (res' : Fin (k + 1) →o Fin (m +1)) (p : obj ∘ res = obj' ∘ res')
    : Limits.pushout (get_map res) (get_map res') ⟶ coherentIso :=
  Limits.pushout.desc (simplex obj) (simplex obj') (by
  rw [simplex_map, simplex_map, simplex_ext]
  exact p)

/-- The `n = 0` special case of `simplex` with more convenient arguments. -/
def zeroSimplex (X : WalkingIso) : Δ[0] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm (WalkingIso.coev X)

theorem zeroSimplex_as_simplex (X₀ : WalkingIso) : zeroSimplex X₀ = simplex (fun _ => X₀) := rfl

/-- The `n = 1`  special case of `simplex` with more convenient arguments. -/
def oneSimplex (X₀ X₁ : WalkingIso) : Δ[1] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm
    (ComposableArrows.mk₁ (X₀ := X₀) (X₁ := X₁) ⟨⟩)

theorem oneSimplex_as_simplex (X₀ X₁ : WalkingIso) : oneSimplex X₀ X₁ = simplex (![X₀, X₁]) := by
  unfold oneSimplex simplex
  congr 1
  unfold ComposableArrows.mk₁
  congr
  ext n
  fin_cases n <;> rfl

theorem oneSimplex_ext {X₀ X₁ Y₀ Y₁ : WalkingIso} (e₀ : X₀ = Y₀) (e₁ : X₁ = Y₁) :
    oneSimplex X₀ X₁ = oneSimplex Y₀ Y₁ :=
  congrArg (yonedaEquiv coherentIso _).symm (ComposableArrows.ext₁ e₀ e₁ rfl)

theorem oneSimplex_const (X₀ : WalkingIso) :
    oneSimplex X₀ X₀ = stdSimplex.map ([1].const [0] 0) ≫ zeroSimplex X₀ := by
  rw [zeroSimplex_as_simplex, simplex_map]
  apply simplex_ext
  ext n
  fin_cases n <;> rfl

/-- The `n = 2`  special case of `simplex` with more convenient arguments. -/
def twoSimplex (X₀ X₁ X₂ : WalkingIso) : Δ[2] ⟶ coherentIso :=
  (yonedaEquiv coherentIso _).symm
    (ComposableArrows.mk₂ (X₀ := X₀) (X₁ := X₁) (X₂ := X₂) ⟨⟩ ⟨⟩)

theorem twoSimplex_as_simplex (X₀ X₁ X₂ : WalkingIso) :
    twoSimplex X₀ X₁ X₂ = simplex (![X₀, X₁, X₂]) := by
  unfold twoSimplex simplex
  congr 1
  unfold ComposableArrows.mk₂ ComposableArrows.mk₁ ComposableArrows.precomp
  congr
  ext n
  fin_cases n <;> rfl

theorem twoSimplex_ext {X₀ X₁ X₂ Y₀ Y₁ Y₂ : WalkingIso}
    (e₀ : X₀ = Y₀) (e₁ : X₁ = Y₁) (e₂ : X₂ = Y₂) : twoSimplex X₀ X₁ X₂ = twoSimplex Y₀ Y₁ Y₂ :=
  congrArg (yonedaEquiv coherentIso _).symm (ComposableArrows.ext₂ e₀ e₁ e₂ rfl rfl)

theorem twoSimplex_δ0 (X₀ X₁ X₂ : WalkingIso) :
    stdSimplex.δ 0 ≫ twoSimplex X₀ X₁ X₂ = oneSimplex X₁ X₂ := rfl

theorem twoSimplex_δ1 (X₀ X₁ X₂ : WalkingIso) :
    stdSimplex.δ 1 ≫ twoSimplex X₀ X₁ X₂ = oneSimplex X₀ X₂ := by
  rw [twoSimplex_as_simplex, oneSimplex_as_simplex]
  have : (stdSimplex.δ 1 : Δ[1] ⟶ Δ[2]) = stdSimplex.map (δ 1) := rfl
  rw [this, simplex_map]
  apply simplex_ext
  ext n
  fin_cases n <;> rfl

theorem twoSimplex_δ2 (X₀ X₁ X₂ : WalkingIso) :
    stdSimplex.δ 2 ≫ twoSimplex X₀ X₁ X₂ = oneSimplex X₀ X₁ := by
  rw [twoSimplex_as_simplex, oneSimplex_as_simplex]
  have : (stdSimplex.δ 2 : Δ[1] ⟶ Δ[2]) = stdSimplex.map (δ 2) := rfl
  rw [this, simplex_map]
  apply simplex_ext
  ext n
  fin_cases n <;> rfl

def hom : Δ[1] ⟶ coherentIso := oneSimplex WalkingIso.zero WalkingIso.one

def inv : Δ[1] ⟶ coherentIso := oneSimplex WalkingIso.one WalkingIso.zero

def homInvId : Δ[2] ⟶ coherentIso := twoSimplex WalkingIso.zero WalkingIso.one WalkingIso.zero

def invHomId : Δ[2] ⟶ coherentIso := twoSimplex WalkingIso.one WalkingIso.zero WalkingIso.one

/-- If we wanted to prove that `coherentIso` is 0-coskeletal, we should start here. -/
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

end coherentIso

end SSet
