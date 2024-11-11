import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.CategoryTheory.Closed.Cartesian

noncomputable section

namespace CategoryTheory

open SimplicialCategory MonoidalCategory BraidedCategory

universe v v₁ v₂ u u₁ u₂

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

/-- `HasCotensor F` represents the mere existence of a simplicial cotensor. -/
class HasCotensor (A : SSet) (X : K) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_cotensor : Nonempty (CotensorCone A X)

theorem HasCotensor.mk {A : SSet} {X : K} (c : CotensorCone A X) : HasCotensor A X :=
  ⟨Nonempty.intro c⟩

/-- Use the axiom of choice to extract explicit `CotensorCone A X` from `HasCotensor A X`. -/
def getCotensorCone (A : SSet) (X : K) [HasCotensor A X] : CotensorCone A X :=
  Classical.choice <| HasCotensor.exists_cotensor

variable (K) in
-- DC: CotensoredCategory
/-- `K` has simplicial cotensors when cotensors with any simplicial set exist. -/
class HasCotensors : Prop where
  /-- All `A : SSet` and `X : K` have a cotensor. -/
  has_cotensors : ∀ A : SSet, ∀ X : K, HasCotensor A X := by infer_instance -- ER: I don't get what this means.

-- ER: copied; not sure what this is.
instance (priority := 100) hasCotensorsOfHasCotensors {K : Type u} [Category.{v} K] [SimplicialCategory K] [HasCotensors K] (A : SSet) (X : K) : HasCotensor A X := HasCotensors.has_cotensors A X

-- Interface to the `HasCotensor` class.
/-- An arbitrary choice of cotensor obj. -/
def cotensor.obj (A : SSet) (X : K) [HasCotensor A X] : K :=
  (getCotensorCone A X).obj

infixr:60 " ⋔ " => cotensor.obj

/-- The associated cotensor cone. -/
def cotensor.cone (A : SSet) (X : K) [HasCotensor A X] : A ⟶ sHom (A ⋔ X) X :=
  (getCotensorCone A X).cone

/-- The universal property of this cone.  -/
def cotensor.is_cotensor (A : SSet) (X : K) [HasCotensor A X] :
    IsCotensor (A ⋔ X) (cotensor.cone A X) := (getCotensorCone A X).is_cotensor

def cotensor.iso (A : SSet) (X : K) [HasCotensor A X] (Y : K) :
    -- Again the notation `A ⟶[SSet] sHom Y X` is ambiguous.
    (sHom Y (A ⋔ X)) ≅ ((ihom A).obj (sHom Y X)) := by
  have := (cotensor.is_cotensor A X).uniq Y
  exact asIso (coneNatTrans Y (cone A X))

def cotensor.iso.underlying (A : SSet) (X : K) [HasCotensor A X] (Y : K) :
  (Y ⟶ (A ⋔ X)) ≃ (A ⟶ sHom Y X) :=
  (SimplicialCategory.homEquiv' Y (A ⋔ X)).trans <|
    (((evaluation SimplexCategoryᵒᵖ (Type _)).obj ⟨SimplexCategory.mk 0⟩).mapIso
      (cotensor.iso A X Y)).toEquiv.trans
        (SimplicialCategory.homEquiv' A (sHom Y X)).symm

-- DC: postcompose
def cotensorCovMap [HasCotensors K] (A : SSet) {X Y : K} (f : X ⟶ Y) : A ⋔ X ⟶ A ⋔ Y :=
  (cotensor.iso.underlying A Y (A ⋔ X)).symm
    ((cotensor.cone A X) ≫ (sHomWhiskerLeft (A ⋔ X) f))

-- DC: EhomPrecompose
def cotensorContraMap [HasCotensors K] {A B : SSet} (i : A ⟶ B) (X : K) : B ⋔ X ⟶ A ⋔ X :=
  (cotensor.iso.underlying A X (B ⋔ X)).symm (i ≫ (cotensor.cone B X))

-- DC: post_pre_eq_pre_post
theorem cotensor_bifunctoriality [HasCotensors K] {A B : SSet} (i : A ⟶ B) {X Y : K} (f : X ⟶ Y) :
    (cotensorCovMap B f) ≫ (cotensorContraMap i Y) =
    (cotensorContraMap i X) ≫ (cotensorCovMap A f) := by sorry

-- def cotensor [SimplicialCategory K] : SSetᵒᵖ ⥤ K ⥤ K := sorry

-- abbrev cotensorObj (A : SSet) (X : K) : K := (cotensor.obj (.op A)).obj X

-- infixr:60 " ⋔⋔ " => cotensorObj

end SimplicialCategory

end CategoryTheory

end
