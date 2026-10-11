module

/-
Copyright (c) 2026 Alejandro José Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro José Soto Franco
-/
public import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Tensors
public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits
public import Mathlib.CategoryTheory.Limits.Yoneda

@[expose] public section

/-!
# Conical limits from tensors

If a `V`-enriched ordinary category `C` is tensored over `V`, every limit cone in the
underlying ordinary category of `C` is already a conical limit cone.

The argument is Kelly's (*Basic Concepts of Enriched Category Theory*, §3.8): a tensor
`Tensor v X` gives an isomorphism `(v ⊗ X ⟶[V] Y) ≅ Ihom v (X ⟶[V] Y)` natural in `Y`, and
composing this with the unenriched/enriched hom comparison `eHomEquiv` and the currying
adjunction produces a bijection

`(v ⊗ X ⟶ Y) ≃ (v ⟶ (X ⟶[V] Y))`

natural in `Y`. Testing whether `(X ⟶[V] c.pt)` is a limit of `(X ⟶[V] F -)` in `V` therefore
reduces, for each `v : V`, to testing whether `v ⊗ X ⟶ c.pt` is a limit of `v ⊗ X ⟶ F -` in
`Type`, which holds automatically since `c` is already a limit cone in `C`, and every
representable functor preserves limits.

## Main results

* `tensorHomEquiv`: the bijection above.
* `preservesLimit_eCoyoneda_of_tensoredCategory`: `(X ⟶[V] -)` preserves any limit that exists
  in the underlying category of `C`, given `TensoredCategory V C`.
* `HasConicalLimit.ofTensoredCategory`: an instance discharging `HasConicalLimit` from
  `HasLimit` and `TensoredCategory V C`.
-/

universe v₁ u₁ v' v u u'

namespace CategoryTheory.Enriched

open Limits MonoidalCategory MonoidalClosed Tensor TensoredCategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V] [MonoidalClosed V]
  [SymmetricCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C] [TensoredCategory V C]

omit [MonoidalClosed V] [SymmetricCategory V] [TensoredCategory V C] in
/-- `eHomEquiv`, varying in the codomain, is a natural transformation `Hom C X ⟹ eCoyoneda V X`
after taking `𝟙_ V`-points: `eCoyoneda V X` is a functor `C ⥤ V`, and this compares its
underlying-`Type`-valued shadow with the honest hom-set functor `C(X, -)`. -/
lemma eHomEquiv_naturality {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V f ≫ eHomWhiskerLeft V X g := by
  rw [eHomEquiv_comp, eHomWhiskerLeft, rightUnitor_inv_naturality_assoc, tensorHom_def,
    show (λ_ (𝟙_ V)) = ρ_ (𝟙_ V) from Iso.ext unitors_equal]
  simp

omit [SymmetricCategory V] [TensoredCategory V C] in
/-- `Pretensor.coneNatTrans`, varying in `y`, is a natural transformation
`eCoyoneda V vx.obj ⟹ eCoyoneda V x ⋙ ihom v`. -/
lemma coneNatTrans_naturality {v : V} {x : C} (vx : Pretensor v x) {y y' : C} (g : y ⟶ y') :
    eHomWhiskerLeft V vx.obj g ≫ vx.coneNatTrans y' =
      vx.coneNatTrans y ≫ (ihom v).map (eHomWhiskerLeft V x g) := by
  apply uncurry_injective
  rw [uncurry_natural_right, Pretensor.uncurry_coneNatTrans,
    uncurry_natural_left, Pretensor.uncurry_coneNatTrans,
    Category.assoc, eComp_eHomWhiskerLeft, ← whisker_exchange_assoc]

/-- The tensor `v ⊗ X` represents `V(v, X ⟶[V] -)`, naturally in the second argument. -/
noncomputable def tensorHomEquiv (v : V) (X Y : C) :
    ((tensor v X).obj ⟶ Y) ≃ (v ⟶ (X ⟶[V] Y)) :=
  (eHomEquiv V).trans <|
    (asIso ((tensor v X).coneNatTrans Y)).homToEquiv.trans <|
      ((ihom.adjunction v).homEquiv (𝟙_ V) (X ⟶[V] Y)).symm.trans (ρ_ v).homFromEquiv

@[simp]
lemma tensorHomEquiv_naturality (v : V) (X : C) {Y Y' : C} (f : (tensor v X).obj ⟶ Y)
    (g : Y ⟶ Y') :
    tensorHomEquiv V v X Y' (f ≫ g) =
      tensorHomEquiv V v X Y f ≫ eHomWhiskerLeft V X g := by
  simp only [tensorHomEquiv, Equiv.trans_apply]
  rw [eHomEquiv_naturality]
  rw [show (asIso ((tensor v X).coneNatTrans Y')).homToEquiv
        (eHomEquiv V f ≫ eHomWhiskerLeft V (tensor v X).obj g) =
      (asIso ((tensor v X).coneNatTrans Y)).homToEquiv (eHomEquiv V f) ≫
        (ihom v).map (eHomWhiskerLeft V X g) from by
    simp only [Iso.homToEquiv, Equiv.coe_fn_mk, asIso_hom, Category.assoc,
      coneNatTrans_naturality]]
  rw [Adjunction.homEquiv_naturality_right_symm]
  simp only [Iso.homFromEquiv, Equiv.coe_fn_mk, Category.assoc]

variable {J : Type u₁} [Category.{v₁} J]

/-- `(X ⟶[V] -)` preserves any limit that exists in the underlying category of `C`.

The tensor represents each `(v ⟶[V] -)`-valued cone: given a cone `s` over `F ⋙ (X ⟶[V] -)`
with vertex `v`, `tensorHomEquiv` turns it into a cone over `F` with vertex `v ⊗ X`, whose
lift against `c` (already a limit in `C`) transports back to the lift `s` needs. -/
instance preservesLimit_eCoyoneda_of_tensoredCategory (F : J ⥤ C) (X : C) :
    PreservesLimit F (eCoyoneda V X) where
  preserves {c} hc := by
    -- `s.π.app j` is well typed against `X ⟶[V] F.obj j` only up to the defeq unfolding
    -- `(F ⋙ eCoyoneda V X).obj j = (X ⟶[V] F.obj j)`, which `rw`/`simp` will not cross. `π'`
    -- restates it at that friendlier type, so every later step sees it directly.
    let π' : ∀ (s : Cone (F ⋙ eCoyoneda V X)) (j : J), s.pt ⟶ (X ⟶[V] F.obj j) := fun s j =>
      s.π.app j
    have π'_natural : ∀ (s : Cone (F ⋙ eCoyoneda V X)) {j j' : J} (f : j ⟶ j'),
        π' s j ≫ eHomWhiskerLeft V X (F.map f) = π' s j' := fun s _ _ f => s.w f
    let auxCone : Cone (F ⋙ eCoyoneda V X) → Cone F := fun s =>
      { pt := (tensor s.pt X).obj,
        π := { app := fun j => (tensorHomEquiv V s.pt X (F.obj j)).symm (π' s j),
               naturality := fun j j' f => by
                 simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
                 apply (tensorHomEquiv V s.pt X (F.obj j')).injective
                 rw [tensorHomEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
                 exact (π'_natural s f).symm } }
    refine ⟨{
      lift := fun s => tensorHomEquiv V s.pt X c.pt (hc.lift (auxCone s)),
      fac := fun s j => ?_,
      uniq := fun s m hm => ?_ }⟩
    · show tensorHomEquiv V s.pt X c.pt (hc.lift (auxCone s)) ≫ eHomWhiskerLeft V X (c.π.app j) =
        π' s j
      rw [← tensorHomEquiv_naturality, hc.fac (auxCone s) j, Equiv.apply_symm_apply]
    · let m' : s.pt ⟶ (X ⟶[V] c.pt) := m
      have hm' : ∀ j, m' ≫ eHomWhiskerLeft V X (c.π.app j) = π' s j := hm
      show m' = tensorHomEquiv V s.pt X c.pt (hc.lift (auxCone s))
      apply (tensorHomEquiv V s.pt X c.pt).symm.injective
      rw [Equiv.symm_apply_apply]
      refine hc.uniq (auxCone s) _ fun j => ?_
      show (tensorHomEquiv V s.pt X c.pt).symm m' ≫ c.π.app j =
        (tensorHomEquiv V s.pt X (F.obj j)).symm (π' s j)
      apply (tensorHomEquiv V s.pt X (F.obj j)).injective
      rw [tensorHomEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hm' j

/-- If a `V`-enriched ordinary category `C` is tensored over `V`, every limit that exists in
the underlying ordinary category of `C` is already a conical limit. -/
lemma HasConicalLimit.ofTensoredCategory (F : J ⥤ C) [HasLimit F] : HasConicalLimit V F where
  preservesLimit_eCoyoneda _ := inferInstance

end CategoryTheory.Enriched
