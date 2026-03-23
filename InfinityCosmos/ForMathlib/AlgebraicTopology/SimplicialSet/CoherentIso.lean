/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import Architect
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe u v

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects called
`zero` and `one`. Perhaps these should have different names?-/
def WalkingIso : Type u := ULift (Fin 2)

@[match_pattern]
def WalkingIso.zero : WalkingIso := ULift.up (0 : Fin 2)

@[match_pattern]
def WalkingIso.one : WalkingIso := ULift.up (1 : Fin 2)

open WalkingIso

namespace WalkingIso

/-- The free isomorphism is the codiscrete category on two objects. Can we make this a special
case of the other definition?-/
instance : Category (WalkingIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u} [Category.{v} C]

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
    | one, zero, _ => e.inv
    | one, one,  _ => 𝟙 _
  map_comp := by simp [WalkingIso, Quiver.Hom]

/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
def equiv : (WalkingIso ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · simp [WalkingIso]
      constructor <;> rfl
    · simp [WalkingIso]
      simp only [fromIso, toIso]
      constructor <;> constructor <;>
      ( intro ⟨⟩
        try rfl
        try (rw [← F.map_id]; rfl) )

end

def coev (i : WalkingIso) : Fin 1 ⥤ WalkingIso := ComposableArrows.mk₀ i

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial Edge

@[blueprint
  "defn:coherent-isomorphism"
  (statement := /--
  The \textbf{homotopy coherent isomorphism} $\iso$, is the nerve of the free-living isomorphism. Its n-simplices are sequences of arrows in WalkingIso.
  -/)]
def coherentIso : SSet := nerve WalkingIso

namespace coherentIso

/-- Since the morphisms in WalkingIso do not carry information, an n-simplex of coherentIso is equivalent to an (n + 1)-vector of the objects of WalkingIso. -/
def equivFun {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → Fin 2) where
  toFun f := ULift.down ∘ f.obj
  invFun f := .mk (ULift.up ∘ f) (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Since Fin 2 has decidable equality, the simplices of coherentIso have decidable equality as well. -/
instance (n : ℕ) : DecidableEq (coherentIso _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso.equivFun)

/-- The source vertex of `coherentIso`. -/
def x₀ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero

/-- The target edge of `coherentIso`. -/
def x₁ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one

/-- The forwards edge of `coherentIso`. -/
def hom : Edge x₀ x₁ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The backwards edge of `coherentIso`. -/
def inv : Edge x₁ x₀ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The forwards and backwards edge of `coherentIso` compose to the identity. -/
def homInvId : Edge.CompStruct hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The backwards and forwards edge of `coherentIso` compose to the identity. -/
def invHomId : Edge.CompStruct inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` is an isomorphism. -/
def isIsoHom : Edge.IsIso coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/-- The image of `hom` under an SSet morphism is an isomorphism. -/
def isIsoMapHom
  {X : SSet}
  (g : coherentIso ⟶ X)
  : IsIso (coherentIso.hom.map g)
  := isIsoHom.map g

/-- If an edge is equal to the image of `hom` under an SSet morphism, this edge is an isomorphism. -/
def isIsoOfEqMapHom
  {X : SSet}
  {x₀ x₁ : X _⦋0⦌}
  {f : Edge x₀ x₁}
  {g : coherentIso ⟶ X}
  (hfg : f.edge = g.app _ hom.edge)
  : f.IsIso
  := (isIsoMapHom g).ofEq hfg.symm

/-- The inclusion of the source vertex of `CoherentIso`. -/
def src : Δ[0] ⟶ coherentIso := yonedaEquiv.symm (coherentIso.x₀)

/-- The inclusion of the target vertex of `CoherentIso`. -/
def tgt : Δ[0] ⟶ coherentIso := yonedaEquiv.symm (coherentIso.x₁)

end coherentIso

end SSet
