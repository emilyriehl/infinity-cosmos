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

variable {K} in
noncomputable def representableMap' {X A B : K} (f : 𝟙_ SSet ⟶ EnrichedCategory.Hom A B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ (EnrichedCategory.Hom X B) :=
  (ρ_ _).inv ≫ _ ◁ f ≫ EnrichedCategory.comp (V := SSet) X A B

variable {K} in
noncomputable def representableMap (X : K) {A B : K} (f : A ⟶ B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ (EnrichedCategory.Hom X B) :=
  representableMap' ((homEquiv A B) f)

def IsQCatIsoFibration {X Y : SSet} (f : X ⟶ Y) : Prop := sorry


/-- A `PreInfinityCosmos` is a simplicially enriched category whose hom-spaces are quasi-categories
and whose morphisms come equipped with a special class of isofibrations.-/
class PreInfinityCosmos extends SimplicialCategory K where
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop

namespace InfinityCosmos

open PreInfinityCosmos

variable {K : Type u} [Category.{v} K][SimplicialCategory K] [PreInfinityCosmos.{v} K]

/-- Common notation for the hom-spaces in a pre-∞-cosmos.-/
abbrev Fun (X Y : K) := EnrichedCategory.Hom (V := SSet) X Y

def IsoFibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsoFibration f}

infixr:25  " ↠ " => IsoFibration

variable (K) in
/-- Experimenting with some changes.-/
class InfinityCosmos' extends PreInfinityCosmos K where
  comp_isIsoFibration {X Y Z : K} (f : X ↠ Y) (g : Y ↠ Z) : IsIsoFibration (f.1 ≫ g.1)
  iso_isIsoFibration {X Y : K} (e : X ⟶ Y) [IsIso e] : IsIsoFibration e
  [has_terminal : HasTerminal K] -- TODO: we need to say that K has a simplicial terminal object.
  all_objects_fibrant {X Y : K} (hY : IsTerminal Y) (f : X ⟶ Y) : IsIsoFibration f
  [has_products : HasConicalProducts K] -- TODO: should be all products, not just binary, replace by HasConicalProducts
  prod_map_fibrant {X Y X' Y' : K} {f : X ⟶ Y} {g : X' ⟶ Y'} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (prod.map f g) -- TODO: extend to arbitrary products
  [has_isoFibration_pullbacks {X Y Z : K} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsIsoFibration g → HasPullback f g] -- TODO: make simplicially enriched
  pullback_is_isoFibration {X Y Z P : K} (f : X ⟶ Z) (g : Y ⟶ Z)
    (fst : P ⟶ X) (snd : P ⟶ Y) (h : IsPullback fst snd f g) :
    IsIsoFibration g → IsIsoFibration fst
  [has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsoFibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasLimit F] -- TODO: make conical
  has_limits_of_towers_isIsoFibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsoFibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K]
  leibniz_cotensor {X Y : K} (f : X ⟶ Y) {A B : SSet} (i : A ⟶ B) [Mono i]
    (hf : IsIsoFibration f) {P : K} (fst : P ⟶ B ⋔ Y) (snd : P ⟶ A ⋔ X)
    (h : IsPullback fst snd (cotensorContraMap i Y) (cotensorCovMap A f)) :
    IsIsoFibration (h.isLimit.lift <|
      PullbackCone.mk (cotensorCovMap B f) (cotensorContraMap i X) (cotensor_bifunctoriality i f))
  local_isoFibration {X A B : K} (f : A ⟶ B) (hf : IsIsoFibration f) :
  IsQCatIsoFibration (representableMap X f)

open InfinityCosmos'

-- def compIsofibration {hyp : InfinityCosmos' K} {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C := by
--   fconstructor
--   · exact (f.1 ≫ g.1)
--   · have := hyp.comp_isIsoFibration f g




end InfinityCosmos

class InfinityCosmos extends SimplicialCategory K where
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
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
  local_isoFibration {X A B : K} (f : A ⟶ B) (hf : IsIsoFibration f) :
  IsQCatIsoFibration (representableMap X f)
-- namespace InfinityCosmos
-- variable [InfinityCosmos.{v} K]

-- def IsoFibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsoFibration f}

-- infixr:25  " ↠ " => IsoFibration

-- end InfinityCosmos

end CategoryTheory
