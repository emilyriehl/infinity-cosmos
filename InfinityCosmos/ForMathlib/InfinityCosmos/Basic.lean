import InfinityCosmos.Mathlib.AlgebraicTopology.Quasicategory
import InfinityCosmos.Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Products.Basic

noncomputable section

namespace CategoryTheory
open Category Limits Functor MonoidalCategory BraidedCategory
universe v v₁ v₂ u u₁ u₂

variable (K : Type u) [Category.{v} K]

namespace SimplicialCategory
variable [SimplicialCategory K]
variable {K}

-- Dagur: we could deduce this from abstract nonsense, but we might want to define it explicitly
-- to get better definitional properties.
instance : MonoidalClosed SSet := sorry

instance : SymmetricCategory SSet := inferInstance
-- instance : HasBinaryProducts SSet := by infer_instance

-- def sComp (X Y Z : K) : (sHom X Y) ⊗ (sHom Y Z) ⟶ sHom X Z := sHomComp X Y Z

-- Dagur: I think it's a good idea to use the monoidal structure given by the
-- `ChosenFiniteProducts` instance on functor categories. It has good definitional properties, like
-- the following:
example (R S : SSet) (n : SimplexCategory) : (R ⊗ S).obj ⟨n⟩ = (R.obj ⟨n⟩ × S.obj ⟨n⟩) := rfl

def coneNatTrans {A : SSet} {AX X : K} (Y : K) (cone : A ⟶ sHom AX X) :
    sHom Y AX ⟶ (A ⟶[SSet] sHom Y X) :=
  let map := ((sHom Y AX) ◁ cone) ≫ (sHomComp Y AX X)
  (MonoidalClosed.curry ((braiding A (sHom Y AX)).hom ≫ map))

structure IsCotensor {A : SSet} {X : K} (AX : K) (cone : A ⟶ sHom AX X) where
  uniq : ∀ (Y : K), (IsIso (coneNatTrans Y cone))

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
    (sHom Y (A ⋔ X)) ≅ (A ⟶[SSet] sHom Y X) := by
  have := (cotensor.is_cotensor A X).uniq Y
  exact asIso (coneNatTrans Y (cone A X))

-- ER: Finish by applying a similar equivalence to `SimplicialCategory.homEquiv'` that calculates
-- the 0-simplicies in the cartesian closed structure.
def cotensor.iso.underlying (A : SSet) (X : K) [HasCotensor A X] (Y : K) :
  (Y ⟶ (A ⋔ X)) ≃ (A ⟶ sHom Y X) := by
  refine (SimplicialCategory.homEquiv' Y (A ⋔ X)).trans ?_
  refine (((evaluation _ _).obj ⟨SimplexCategory.mk 0⟩).mapIso
    (cotensor.iso A X Y)).toEquiv.trans ?_
  sorry -- need to define the cartesian/monoidal closed structure first


def cotensorCovMap [HasCotensors K] (A : SSet) {X Y : K} (f : X ⟶ Y) : A ⋔ X ⟶ A ⋔ Y :=
  (cotensor.iso.underlying A Y (A ⋔ X)).symm
    ((cotensor.cone A X) ≫ (sHomWhiskerLeft (A ⋔ X) f))

def cotensorContraMap [HasCotensors K] {A B : SSet} (i : A ⟶ B) (X : K) : B ⋔ X ⟶ A ⋔ X :=
  (cotensor.iso.underlying A X (B ⋔ X)).symm (i ≫ (cotensor.cone B X))

theorem cotensor_bifunctoriality [HasCotensors K] {A B : SSet} (i : A ⟶ B) {X Y : K} (f : X ⟶ Y) :
    (cotensorCovMap B f) ≫ (cotensorContraMap i Y) =
    (cotensorContraMap i X) ≫ (cotensorCovMap A f) := by sorry

-- noncomputable def cotensor [SimplicialCategory K] : SSetᵒᵖ ⥤ K ⥤ K := sorry

-- abbrev cotensorObj (A : SSet) (X : K) : K := (cotensor.obj (.op A)).obj X

-- infixr:60 " ⋔⋔ " => cotensorObj

-- def foo (X : K) : IsTerminal ((⊥_ SSet) ⋔⋔ X) := sorry


end SimplicialCategory

open SimplicialCategory

class InfinityCosmos extends SimplicialCategory K where
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  comp_isIsoFibration {X Y Z : K} {f : X ⟶ Y} {g : Y ⟶ Z} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (f ≫ g)
  iso_isIsoFibration {X Y : K} (e : X ≅ Y) : IsIsoFibration e.hom
  has_terminal : HasTerminal K
  all_objects_fibrant {X Y : K} (hY : IsTerminal Y) (f : X ⟶ Y) : IsIsoFibration f
  has_products : HasBinaryProducts K
  prod_map_fibrant {X Y X' Y' : K} {f : X ⟶ Y} {g : X' ⟶ Y'} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (prod.map f g)
  [has_isoFibration_pullbacks {X Y Z : K} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsIsoFibration g → HasPullback f g]
  pullback_is_isoFibration {X Y Z P : K} (f : X ⟶ Z) (g : Y ⟶ Z)
    (fst : P ⟶ X) (snd : P ⟶ Y) (h : IsPullback fst snd f g) :
    IsIsoFibration g → IsIsoFibration fst
  has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsoFibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasLimit F
  has_limits_of_towers_isIsoFibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsoFibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K] -- ER: Added
  -- leibniz_cotensor {X Y : K} (f : X ⟶ Y) (A B : SSet) (i : A ⟶ B) [Mono i]
  --   (hf : IsIsoFibration f) {P : K} (fst : P ⟶ B ⋔⋔ Y) (snd : P ⟶ A ⋔⋔ X)
  --   (h : IsPullback fst snd ((cotensor.map (.op i)).app Y) ((cotensor.obj (.op A)).map f)) :
  --   IsIsoFibration (h.isLimit.lift <|
  --     PullbackCone.mk ((cotensor.obj (.op B)).map f) ((cotensor.map (.op i)).app X) (by aesop_cat))
  leibniz_cotensor {X Y : K} (f : X ⟶ Y) (A B : SSet) (i : A ⟶ B) [Mono i]
    (hf : IsIsoFibration f) {P : K} (fst : P ⟶ B ⋔ Y) (snd : P ⟶ A ⋔ X)
    (h : IsPullback fst snd (cotensorContraMap i Y) (cotensorCovMap A f)) :
    IsIsoFibration (h.isLimit.lift <|
      PullbackCone.mk (cotensorCovMap B f) (cotensorContraMap i X) (cotensor_bifunctoriality i f))
  local_isoFibration {X Y Z : K} (f : Y ⟶ Z) (hf : IsIsoFibration f) :
    -- FIXME (V := SSet)
    ∀ (_ : MonoidalClosed.curry (EnrichedCategory.comp (V := SSet) X Y Z) = sorry), sorry
namespace InfinityCosmos
variable [InfinityCosmos.{v} K]

def IsoFibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsoFibration f}

infixr:25  " ↠ " => IsoFibration

end InfinityCosmos
