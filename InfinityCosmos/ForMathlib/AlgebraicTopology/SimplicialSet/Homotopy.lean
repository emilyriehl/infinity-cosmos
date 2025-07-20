/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

universe u v w

namespace SSet

open CategoryTheory Simplicial SimplicialCategory Limits

/-- An interval is a simplicial set equipped with two endpoints.-/
class Interval (I : SSet.{u}) : Type u where
  src : Δ[0] ⟶ I
  tgt : Δ[0] ⟶ I

/-- The interval relevant to the theory of Kan complexes.-/
instance arrowInterval : Interval Δ[1] where
  src := stdSimplex.δ (n := 0) (1)
  tgt := stdSimplex.δ (n := 0) (0)

/-- The interval relevant to the theory of quasi-categories. -/
instance isoInterval : Interval coherentIso where
  src := coherentIso.pt WalkingIso.zero
  tgt := coherentIso.pt WalkingIso.one

open MonoidalCategory
noncomputable def pointIsUnit : Δ[0] ≅ (𝟙_ SSet) :=
  IsTerminal.uniqueUpToIso isTerminalDeltaZero (IsTerminal.ofUnique (𝟙_ SSet))

noncomputable def expUnitNatIso : ihom (𝟙_ SSet) ≅ 𝟭 SSet :=
  MonoidalClosed.unitNatIso.symm

noncomputable def expPointNatIso : ihom Δ[0] ≅ 𝟭 SSet := by
  refine ?_ ≪≫ expUnitNatIso
  exact {
    hom := MonoidalClosed.pre pointIsUnit.inv
    inv := MonoidalClosed.pre pointIsUnit.hom
    hom_inv_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.hom_inv_id]
      exact MonoidalClosed.pre_id _
    inv_hom_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.inv_hom_id]
      exact MonoidalClosed.pre_id _
  }

noncomputable def expPointIsoSelf (X : SSet) : sHom Δ[0] X ≅ X := expPointNatIso.app X
section

variable {I : SSet.{u}} [Interval I]

noncomputable def pathSpace {I : SSet.{u}} [Interval I] (X : SSet.{u}) : SSet.{u} := sHom I X

open MonoidalClosed

noncomputable def pathSpace.src (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.src).app X ≫ X.expPointIsoSelf.hom)

noncomputable def pathSpace.tgt (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.tgt).app X ≫ X.expPointIsoSelf.hom)

lemma curry_snd_unitNatIso_inv_app {X Y : SSet.{u}} (f : X ⟶ Y) :
    curry (CartesianMonoidalCategory.snd (𝟙_ SSet) X ≫ f) ≫ unitNatIso.inv.app Y = f := by
  rw [← Iso.app_inv, Iso.comp_inv_eq, Iso.app_hom, unitNatIso]
  simp only [Functor.id_obj, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    curriedTensor_obj_obj, ihom.ihom_adjunction_unit, leftUnitorNatIso_hom_app,
    ihom.coev_naturality_assoc, id_whiskerLeft, Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id_assoc]
  rfl

lemma pathSpace.curry_snd_src {A B : SSet.{u}} (f : A ⟶ B) :
    curry (CartesianMonoidalCategory.snd I A ≫ f) ≫ src B = f := by
  rw [pathSpace.src, curry_pre_app_assoc, CartesianMonoidalCategory.whiskerRight_snd_assoc,
    expPointIsoSelf, Iso.app_hom, expPointNatIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.id_obj, curry_pre_app_assoc,
    CartesianMonoidalCategory.whiskerRight_snd_assoc]
  rw [expUnitNatIso, Iso.symm_hom, curry_snd_unitNatIso_inv_app f]

lemma pathSpace.curry_snd_tgt {A B : SSet.{u}} (f : A ⟶ B) :
    curry (CartesianMonoidalCategory.snd I A ≫ f) ≫ tgt B = f := by
  rw [pathSpace.tgt, curry_pre_app_assoc, CartesianMonoidalCategory.whiskerRight_snd_assoc,
    expPointIsoSelf, Iso.app_hom, expPointNatIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.id_obj, curry_pre_app_assoc,
    CartesianMonoidalCategory.whiskerRight_snd_assoc]
  rw [expUnitNatIso, Iso.symm_hom, curry_snd_unitNatIso_inv_app f]

/-- TODO: Figure out how to allow `I` to be an a different universe from `A` and `B`?-/
structure Homotopy {A B : SSet.{u}} (f g : A ⟶ B) : Type u
    where
  homotopy : A ⟶ sHom I B
  source_eq : homotopy ≫ pathSpace.src B = f
  target_eq : homotopy ≫ pathSpace.tgt B = g

@[refl]
noncomputable def Homotopy.refl {A B : SSet.{u}} (f : A ⟶ B) : Homotopy (I := I) f f where
  homotopy := curry <| CartesianMonoidalCategory.snd I A ≫ f
  source_eq := pathSpace.curry_snd_src f
  target_eq := pathSpace.curry_snd_tgt f

def Homotopy.hoFunctorIso {A B : SSet.{u}} {f g : A ⟶ B} (h : Homotopy (I := I) f g) :
    hoFunctor.map f ≅ hoFunctor.map g := by
  dsimp [hoFunctor]
  simp_rw [← h.source_eq, ← h.target_eq]
  simp only [Functor.map_comp]
  -- Joël: You should probably use NatIso.ofComponents: for each 0-simplex, the homotopy gives a
  -- "double-sided path" between the images by both f and g (which should give an iso in the
  -- homotopy category), and then you need to check it is natural.
  sorry

/-- For the correct interval, this defines a good notion of equivalences for both Kan complexes and quasi-categories.-/
structure Equiv (A B : SSet.{u}) : Type u where
  toFun : A ⟶ B
  invFun : B ⟶ A
  left_inv : Homotopy (I := I) (toFun ≫ invFun) (𝟙 A)
  right_inv : Homotopy (I := I) (invFun ≫ toFun) (𝟙 B)

@[refl]
noncomputable def Equiv.refl {A : SSet} : Equiv (I := I) A A :=
  ⟨𝟙 A, 𝟙 A, Category.comp_id (𝟙 A) ▸ Homotopy.refl _, Category.comp_id (𝟙 A) ▸ Homotopy.refl _⟩

@[symm]
def Equiv.symm {A B : SSet.{u}} (e : Equiv (I := I) A B) : Equiv (I := I) B A :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

end

end SSet

namespace Kan

open SSet Simplicial

/-- Equivalence of Kan Complexes. -/
def Equiv (A B : SSet.{u}) [KanComplex A] [KanComplex B] :=
    SSet.Equiv (I := Δ[1]) A B

end Kan

namespace QCat

open SSet

/-- Equivalence of quasi-categories. -/
def Equiv (A B : SSet.{u}) [Quasicategory A] [Quasicategory B] :=
    SSet.Equiv (I := coherentIso) A B

end QCat


namespace SSet
section

open CategoryTheory Simplicial SimplexCategory

variable {A : SSet.{u}} (f g : A _⦋1⦌)

structure HomotopyL where
  simplex : A _⦋2⦌
  δ₀_eq : A.δ 0 simplex = A.σ 0 (A.δ 0 f)
  δ₁_eq : A.δ 1 simplex = g
  δ₂_eq : A.δ 2 simplex = f

structure HomotopyR where
  simplex : A _⦋2⦌
  δ₀_eq : A.δ 0 simplex = f
  δ₁_eq : A.δ 1 simplex = g
  δ₂_eq : A.δ 2 simplex = A.σ 0 (A.δ 1 f)

def HomotopicL : Prop :=
    Nonempty (HomotopyL f g)

def HomotopicR : Prop :=
    Nonempty (HomotopyR f g)

def HomotopyL.refl : HomotopyL f f where
  simplex := A.σ 1 f
  δ₀_eq := by
    change _ = (A.δ 0 ≫ A.σ 0) _
    rw [← A.δ_comp_σ_of_le (by simp)]; simp
  δ₁_eq := by
    change (A.σ 1 ≫ A.δ 1) _ = _
    rw [A.δ_comp_σ_self' (by simp)]; simp
  δ₂_eq := by
    change (A.σ 1 ≫ A.δ 2) _ = _
    rw [A.δ_comp_σ_succ' (by simp)]
    rfl

-- -- need a better name
-- noncomputable def HomotopyL.ofHomotopyLOfHomotopyL {f g h : A _⦋1⦌}
--   (H₁ : HomotopyL f g) (H₂ : HomotopyL f h) :
--     HomotopyL g h := by
--   let σ : (Λ[3, 1] : SSet.{u}) ⟶ A := sorry
--   let τ : A _⦋3⦌ := sorry
--     -- BUILD FAILS:
--     -- A.yonedaEquiv _ (Classical.choose $ Quasicategory.hornFilling
--     --   (by simp) (by simp [Fin.lt_iff_val_lt_val]) σ)
--   have τ₀ : A.δ 0 τ = (A.δ 0 ≫ A.σ 0≫ A.σ 0) g := sorry
--   have τ₂ : A.δ 2 τ = H₂.simplex := sorry
--   have τ₃ : A.δ 3 τ = H₁.simplex := sorry
--   use A.δ 1 τ
--   . change (A.δ 1 ≫ A.δ 0) _ = _
--     rw [A.δ_comp_δ' (by simp)]; simp [τ₀]
--     change (A.σ 0 ≫ A.δ 0) _ = _
--     rw [A.δ_comp_σ_self' (by simp)]; simp
--   . rw [← H₂.δ₁_eq, ← τ₂]
--     change _ = (A.δ 2 ≫ A.δ 1) _
--     rw [A.δ_comp_δ' (by simp)]; rfl
--   . rw [← H₁.δ₁_eq, ← τ₃]
--     change _ = (A.δ 3 ≫ A.δ 1) _
--     rw [A.δ_comp_δ' (by simp)]; rfl

-- lemma HomotopyL.equiv :
--     Equivalence (fun f g : A _⦋1⦌ ↦ HomotopicL f g) where
--   refl f := ⟨HomotopyL.refl f⟩
--   symm := by
--     intro f g ⟨H⟩
--     exact ⟨H.ofHomotopyLOfHomotopyL (HomotopyL.refl f)⟩
--   trans := by
--     intro f g h ⟨H₁⟩ ⟨H₂⟩
--     exact ⟨(H₁.ofHomotopyLOfHomotopyL (HomotopyL.refl f)).ofHomotopyLOfHomotopyL H₂⟩

-- lemma homotopicL_iff_homotopicR [Quasicategory A] :
--     HomotopicL f g ↔ HomotopicR f g := sorry

-- lemma HomotopyR.equiv [Quasicategory A] :
--     Equivalence (fun f g : A _⦋1⦌ ↦ HomotopicR f g) := by
--   simp [← homotopicL_iff_homotopicR, HomotopyL.equiv]

end

end SSet

namespace SSet

open CategoryTheory

/-- `hoFunctor` applied to a nerve of a category is isomorphic to that category. -/
noncomputable def hoFunctor_nerve_iso (C : Cat) :
    hoFunctor.obj (nerve C) ≅ C := by
  rw [show nerve C = nerveFunctor.obj C by rfl, ← Functor.comp_obj]
  exact CategoryTheory.nerveFunctorCompHoFunctorIso.app C

/-- `hoFunctor` applied to `coherentIso` is isomorphic to `WalkingIso`. -/
noncomputable def hoFunctor_coherentIso_equiv :
    hoFunctor.obj coherentIso ≅ Cat.of WalkingIso :=
  hoFunctor_nerve_iso <| Cat.of WalkingIso

def WalkingIso.swap : WalkingIso ⟶ WalkingIso
| WalkingIso.zero => WalkingIso.one
| WalkingIso.one => WalkingIso.zero

def WalkingIso.swapFunctor : WalkingIso ⥤ WalkingIso where
  obj := WalkingIso.swap
  map := id

def coherentIso.swap : coherentIso ⟶ coherentIso :=
  nerveMap WalkingIso.swapFunctor

@[simp]
lemma src_swap_eq_tgt : Interval.src ≫ coherentIso.swap = Interval.tgt :=
  rfl

@[simp]
lemma tgt_swap_eq_src : Interval.tgt ≫ coherentIso.swap = Interval.src :=
  rfl

@[symm]
noncomputable def Homotopy.coherentIso_symm {A B : SSet.{u}} {f g : A ⟶ B}
    (h : Homotopy (I := coherentIso) f g) :
    Homotopy (I := coherentIso) g f where
  homotopy := h.homotopy ≫ (MonoidalClosed.pre coherentIso.swap).app B
  source_eq := by
    simp_rw [← h.target_eq, Category.assoc]
    rfl
  target_eq := by
    simp_rw [← h.source_eq, Category.assoc]
    rfl

/--
`hoFunctor` sends equivalences `Equiv A B` to equivalences of categories `F.obj A ≌ F.obj B`.
-/
noncomputable def hoFunctor.mapEquiv (A B : SSet.{u}) (f : SSet.Equiv (I := coherentIso) A B) :
    hoFunctor.obj A ≌ hoFunctor.obj B where
  functor := hoFunctor.map f.toFun
  inverse := hoFunctor.map f.invFun
  unitIso := by
    rw [← Cat.id_eq_id]
    have :
        hoFunctor.map f.toFun ⋙ hoFunctor.map f.invFun = hoFunctor.map (f.toFun ≫ f.invFun) := by
      rw [Functor.map_comp]
      rfl
    rw [this, ← hoFunctor.map_id A]
    apply Homotopy.hoFunctorIso (I := coherentIso)
    exact f.left_inv.coherentIso_symm
  counitIso := by
    rw [← Cat.id_eq_id]
    have :
        hoFunctor.map f.invFun ⋙ hoFunctor.map f.toFun = hoFunctor.map (f.invFun ≫ f.toFun) := by
      rw [Functor.map_comp]
      rfl
    rw [this, ← hoFunctor.map_id B]
    apply Homotopy.hoFunctorIso (I := coherentIso)
    exact f.right_inv
  functor_unitIso_comp := sorry

end SSet
