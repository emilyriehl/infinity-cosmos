import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Cotensors
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Limits
import Mathlib.AlgebraicTopology.SimplicialSet.Quasicategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

namespace CategoryTheory
open Category Limits Functor MonoidalCategory Simplicial SimplicialCategory SSet
universe v v₁ v₂ u u₁ u₂

variable (K : Type u) [Category.{v} K]
variable [SimplicialCategory K]

class InfinityCosmos extends SimplicialCategory K where
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  comp_isIsoFibration {X Y Z : K} {f : X ⟶ Y} {g : Y ⟶ Z} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (f ≫ g)
  iso_isIsoFibration {X Y : K} (e : X ≅ Y) : IsIsoFibration e.hom
  has_terminal : HasTerminal K
  all_objects_fibrant {X Y : K} (hY : IsTerminal Y) (f : X ⟶ Y) : IsIsoFibration f
  has_products : HasBinaryProducts K -- TODO: replace by HasConicalProducts
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

end CategoryTheory
