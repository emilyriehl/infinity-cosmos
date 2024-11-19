import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Cotensors
import Mathlib.CategoryTheory.Closed.Cartesian

namespace CategoryTheory

open SimplicialCategory MonoidalCategory BraidedCategory

universe v v₁ v₂ u u₁ u₂

-- This section specializes the general notion of cotensors to simplicial categories.
section specialization

namespace SimplicialCategory
variable {K : Type u}[Category.{v} K][SimplicialCategory K]

open Enriched

/-- A specialization of the enriched category cotensor.-/
abbrev Cotensor (U : SSet) (A : K) := Enriched.Cotensor U A

noncomputable section
-- Noncomputability because this depends on `SSet.instChosenFiniteProducts`.

def cotensorPostcompose {U : SSet} {A B : K} (ua : Cotensor U A) (ub : Cotensor U B) (f : A ⟶ B) :
    ua.obj ⟶ ub.obj :=
  (eHomEquiv SSet).symm (eHomEquiv SSet f ≫ Cotensor.postcompose _ ua ub)

def cotensorPrecompose {U V : SSet} {A : K} (ua : Cotensor U A) (va : Cotensor V A) (i : U ⟶ V) :
    va.obj ⟶ ua.obj :=
  (eHomEquiv SSet).symm (eHomEquiv SSet i ≫ Cotensor.EhomPrecompose _ ua va)

lemma cotensorPostcompose_homEquiv {U : SSet} {A B : K} (ua : Cotensor U A) (ub : Cotensor U B)
    (f : A ⟶ B) : eHomEquiv SSet (cotensorPostcompose ua ub f) =
      eHomEquiv SSet f ≫ Cotensor.postcompose _ ua ub := by
  unfold cotensorPostcompose; simp

lemma cotensorPrecompose_homEquiv {U V : SSet} {A : K} (ua : Cotensor U A) (va : Cotensor V A)
    (i : U ⟶ V) : eHomEquiv SSet (cotensorPrecompose ua va i) =
      eHomEquiv SSet i ≫ Cotensor.EhomPrecompose _ ua va  := by
  unfold cotensorPrecompose; simp

theorem cotensor_local_bifunctoriality {U V : SSet} {A B : K}
    (ua : Cotensor U A) (ub : Cotensor U B) (va : Cotensor V A) (vb : Cotensor V B)
    (i : U ⟶ V) (f : A ⟶ B) :
    (cotensorPostcompose va vb f) ≫ (cotensorPrecompose ub vb i) =
      (cotensorPrecompose ua va i) ≫ (cotensorPostcompose ua ub f) := by
  apply (eHomEquiv SSet).injective
  rw [eHomEquiv_comp, eHomEquiv_comp]
  have thm := Cotensor.post_pre_eq_pre_post _ ua ub va vb
  have compeq := whisker_eq ((λ_ _).inv ≫ (eHomEquiv SSet i ⊗ eHomEquiv SSet f)) thm
  rw [Category.assoc, ← tensor_comp_assoc] at compeq
  rw [← cotensorPostcompose_homEquiv, ← cotensorPrecompose_homEquiv] at compeq
  rw [compeq]
  slice_rhs 2 3 => rw [← tensor_comp, ← cotensorPostcompose_homEquiv, ← cotensorPrecompose_homEquiv]
  simp only [braiding_naturality, braiding_tensorUnit_right, Category.assoc,
    Iso.cancel_iso_inv_left]
  monoidal

end


/-- `HasCotensor U A` represents the mere existence of a simplicial cotensor. -/
class HasCotensor (U : SSet) (A : K) : Prop where mk' ::
  /-- There is some cotensor. -/
  exists_cotensor : Nonempty (Cotensor U A)

theorem HasCotensor.mk {U : SSet} {A : K} (c : Cotensor U A) : HasCotensor U A :=
  ⟨Nonempty.intro c⟩

/-- Use the axiom of choice to extract explicit `CotensorCone A X` from `HasCotensor A X`. -/
noncomputable def getCotensor (U : SSet) (A : K) [HasCotensor U A] : Cotensor U A :=
  Classical.choice <| HasCotensor.exists_cotensor

noncomputable section
-- Interface to the `HasCotensor` class.

/-- An arbitrary choice of cotensor obj. -/
def cotensor.obj (U : SSet) (A : K) [HasCotensor U A] : K := (getCotensor U A).obj

infixr:60 " ⋔ " => cotensor.obj

/-- The associated cotensor cone. -/
def cotensor.cone (U : SSet) (A : K) [HasCotensor U A] : U ⟶ sHom (U ⋔ A) A :=
  (getCotensor U A).cone

/-- The universal property of this cone.  -/
def cotensor.is_cotensor (U : SSet) (A : K) [HasCotensor U A] : Cotensor U A := getCotensor U A

/-- The natural isomorphism induced by a cotensor.-/
def cotensor.iso (U : SSet) (A : K) [HasCotensor U A] (X : K) :
    (sHom X (U ⋔ A)) ≅ ((ihom U).obj (sHom X A)) where
      hom := Precotensor.coneNatTrans _ _
      inv := (getCotensor U A).coneNatTransInv _
      hom_inv_id := (getCotensor U A).NatTrans_NatTransInv_eq _
      inv_hom_id := (getCotensor U A).NatTransInv_NatTrans_eq _

def cotensor.iso.underlying (U : SSet) (A : K) [HasCotensor U A] (X : K) :
  (X ⟶ (U ⋔ A)) ≃ (U ⟶ sHom X A) :=
  (SimplicialCategory.homEquiv' X (U ⋔ A)).trans <|
    (((evaluation SimplexCategoryᵒᵖ (Type _)).obj ⟨SimplexCategory.mk 0⟩).mapIso
      (cotensor.iso U A X)).toEquiv.trans
        (SimplicialCategory.homEquiv' U (sHom X A)).symm

end

variable (K) in
-- DC: CotensoredCategory
/-- `K` has simplicial cotensors when cotensors with any simplicial set exist. -/
class HasCotensors : Prop where
  /-- All `U : SSet` and `A : K` have a cotensor. -/
  has_cotensors : ∀ U : SSet, ∀ A : K, HasCotensor U A := by infer_instance

instance (priority := 100) hasCotensorsOfHasCotensors {K : Type u} [Category.{v} K]
[SimplicialCategory K] [HasCotensors K] (U : SSet) (A : K) : HasCotensor U A :=
  HasCotensors.has_cotensors U A

section
variable {K : Type u}[Category.{v} K][SimplicialCategory K][HasCotensors K]

-- ER: I don't remember why I was considering an alternate form of this.
noncomputable def cotensorCovMap (U : SSet) {A B : K} (f : A ⟶ B) : U ⋔ A ⟶ U ⋔ B :=
  cotensorPostcompose _ _ f
  -- (cotensor.iso.underlying U B (U ⋔ A)).symm ((cotensor.cone U A) ≫ (sHomWhiskerLeft (U ⋔ A) f))

-- ER: I don't remember why I was considering an alternate form of this.
noncomputable def cotensorContraMap {U V : SSet} (i : U ⟶ V) (A : K) : V ⋔ A ⟶ U ⋔ A :=
  cotensorPrecompose _ _ i
--  (cotensor.iso.underlying U A (V ⋔ A)).symm (i ≫ (cotensor.cone V A))

-- DC: post_pre_eq_pre_post
theorem cotensor_bifunctoriality {U V : SSet} (i : U ⟶ V) {A B : K} (f : A ⟶ B) :
    (cotensorCovMap V f) ≫ (cotensorContraMap i B) =
    (cotensorContraMap i A) ≫ (cotensorCovMap U f) := cotensor_local_bifunctoriality _ _ _ _ i f

end


end SimplicialCategory


end specialization


noncomputable section


variable (K : Type u) [Category.{v} K]

namespace SimplicialCategory
variable [SimplicialCategory K]
variable {K}

-- DC: In Enriched/Cotensors, this is Precotensor.coneNatTrans
def coneNatTrans {A : SSet} {AX X : K} (Y : K) (cone : A ⟶ sHom AX X) :
  -- The notation `A ⟶[SSet] sHom Y X` is ambiguous, could mean both `ihom` or the enriched hom...
  -- Here we mean `ihom` so we write that explicitly.
  -- These notations should probably be scoped.
    sHom Y AX ⟶ ((ihom A).obj (sHom Y X)) :=
  let map := ((sHom Y AX) ◁ cone) ≫ (sHomComp Y AX X)
  (MonoidalClosed.curry ((braiding A (sHom Y AX)).hom ≫ map))

structure IsCotensor {A : SSet} {X : K} (AX : K) (cone : A ⟶ sHom AX X) where
  uniq : ∀ (Y : K), (IsIso (coneNatTrans Y cone))

-- DC: structure Cotensor
structure CotensorCone (A : SSet) (X : K) where
  /-- The object -/
  obj : K
  /-- The cone itself -/
  cone : A ⟶ sHom obj X
  /-- The universal property of the limit cone -/
  is_cotensor : IsCotensor obj cone

-- ER: Duplicated above.
-- /-- `HasCotensor F` represents the mere existence of a simplicial cotensor. -/
-- class HasCotensor (A : SSet) (X : K) : Prop where mk' ::
--   /-- There is some limit cone for `F` -/
--   exists_cotensor : Nonempty (CotensorCone A X)

-- ER: Duplicated above.
-- theorem HasCotensor.mk {A : SSet} {X : K} (c : CotensorCone A X) : HasCotensor A X :=
--   ⟨Nonempty.intro c⟩

-- ER: Duplicated above.
-- /-- Use the axiom of choice to extract explicit `CotensorCone A X` from `HasCotensor A X`. -/
-- def getCotensorCone (A : SSet) (X : K) [HasCotensor A X] : CotensorCone A X :=
--   Classical.choice <| HasCotensor.exists_cotensor

-- ER: Duplicated above.
-- variable (K) in
-- -- DC: CotensoredCategory
-- /-- `K` has simplicial cotensors when cotensors with any simplicial set exist. -/
-- class HasCotensors : Prop where
--   /-- All `A : SSet` and `X : K` have a cotensor. -/
--   has_cotensors : ∀ A : SSet, ∀ X : K, HasCotensor A X := by infer_instance
-- ER: copied; not sure what this is.

-- instance (priority := 100) hasCotensorsOfHasCotensors {K : Type u} [Category.{v} K] [SimplicialCategory K] [HasCotensors K] (A : SSet) (X : K) : HasCotensor A X := HasCotensors.has_cotensors A X

-- ER: Duplicated above.
-- -- Interface to the `HasCotensor` class.
-- /-- An arbitrary choice of cotensor obj. -/
-- -- def cotensor.obj (A : SSet) (X : K) [HasCotensor A X] : K :=
-- --   (getCotensorCone A X).obj

-- -- infixr:60 " ⋔ " => cotensor.obj

-- /-- The associated cotensor cone. -/
-- def cotensor.cone (A : SSet) (X : K) [HasCotensor A X] : A ⟶ sHom (A ⋔ X) X :=
--   (getCotensorCone A X).cone

-- /-- The universal property of this cone.  -/
-- def cotensor.is_cotensor (A : SSet) (X : K) [HasCotensor A X] :
--     IsCotensor (A ⋔ X) (cotensor.cone A X) := (getCotensorCone' A X).is_cotensor

-- def cotensor.iso (A : SSet) (X : K) [HasCotensor A X] (Y : K) :
--     -- Again the notation `A ⟶[SSet] sHom Y X` is ambiguous.
--     (sHom Y (A ⋔ X)) ≅ ((ihom A).obj (sHom Y X)) := by
--   have := (cotensor.is_cotensor A X).uniq Y
--   exact asIso (coneNatTrans Y (cone A X))

-- def cotensor.iso.underlying (A : SSet) (X : K) [HasCotensor A X] (Y : K) :
--   (Y ⟶ (A ⋔ X)) ≃ (A ⟶ sHom Y X) :=
--   (SimplicialCategory.homEquiv' Y (A ⋔ X)).trans <|
--     (((evaluation SimplexCategoryᵒᵖ (Type _)).obj ⟨SimplexCategory.mk 0⟩).mapIso
--       (cotensor.iso A X Y)).toEquiv.trans
--         (SimplicialCategory.homEquiv' A (sHom Y X)).symm

-- -- DC: postcompose
-- def cotensorCovMap [HasCotensors K] (A : SSet) {X Y : K} (f : X ⟶ Y) : A ⋔ X ⟶ A ⋔ Y :=
--   (cotensor.iso.underlying A Y (A ⋔ X)).symm
--     ((cotensor.cone A X) ≫ (sHomWhiskerLeft (A ⋔ X) f))

-- -- DC: EhomPrecompose
-- def cotensorContraMap [HasCotensors K] {A B : SSet} (i : A ⟶ B) (X : K) : B ⋔ X ⟶ A ⋔ X :=
--   (cotensor.iso.underlying A X (B ⋔ X)).symm (i ≫ (cotensor.cone B X))

-- -- DC: post_pre_eq_pre_post
-- theorem cotensor_bifunctoriality [HasCotensors K] {A B : SSet} (i : A ⟶ B) {X Y : K} (f : X ⟶ Y) :
--     (cotensorCovMap B f) ≫ (cotensorContraMap i Y) =
--     (cotensorContraMap i X) ≫ (cotensorCovMap A f) := by sorry


end SimplicialCategory

end

end CategoryTheory
