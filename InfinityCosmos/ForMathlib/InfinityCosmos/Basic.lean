import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Cotensors
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Limits
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import Mathlib.AlgebraicTopology.SimplicialSet.Quasicategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

namespace CategoryTheory
open Category Limits Functor MonoidalCategory Simplicial SimplicialCategory SSet
universe w v v₁ v₂ u u₁ u₂

variable (K : Type u) [Category.{v} K]
variable [SimplicialCategory K]


/-- A `PreInfinityCosmos` is a simplicially enriched category whose hom-spaces are quasi-categories
and whose morphisms come equipped with a special class of isofibrations.-/
class PreInfinityCosmos extends SimplicialCategory K where
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  IsIsoFibration : MorphismProperty K

namespace InfinityCosmos

variable {K : Type u} [Category.{v} K] [PreInfinityCosmos.{v} K]

open PreInfinityCosmos

/-- Common notation for the hom-spaces in a pre-∞-cosmos.-/
def Fun (A B : K) : QCat where
  obj := EnrichedCategory.Hom A B
  property := PreInfinityCosmos.has_qcat_homs (X := A) (Y := B)

noncomputable def representableMap' {X A B : K} (f : 𝟙_ SSet ⟶ EnrichedCategory.Hom A B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ (EnrichedCategory.Hom X B) :=
  (ρ_ _).inv ≫ _ ◁ f ≫ EnrichedCategory.comp (V := SSet) X A B

noncomputable def representableMap (X : K) {A B : K} (f : A ⟶ B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ (EnrichedCategory.Hom X B) :=
  representableMap' (eHomEquiv SSet f)

noncomputable def toFunMap (X : K) {A B : K} (f : A ⟶ B) :
    Fun X A ⟶ Fun X B := representableMap X f

-- Arguments of this type have the form `⟨ f hf ⟩`
def IsoFibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsoFibration f}

-- Type with "\rr".
infixr:25  " ↠ " => IsoFibration

instance (A B : K) : Coe (A ↠ B) (A ⟶ B) := ⟨ λ f ↦ f.1 ⟩

end InfinityCosmos

open InfinityCosmos
variable (K : Type u) [Category.{v} K][SimplicialCategory K] [PreInfinityCosmos.{v} K]

/-- Experimenting with some changes.-/
class InfinityCosmos' extends PreInfinityCosmos K where
  comp_isIsoFibration {X Y Z : K} (f : X ↠ Y) (g : Y ↠ Z) : IsIsoFibration (f.1 ≫ g.1)
  iso_isIsoFibration {X Y : K} (e : X ⟶ Y) [IsIso e] : IsIsoFibration e
--  [has_terminal : HasConicalTerminal K] -- TODO: comment out and make instance
  all_objects_fibrant {X Y : K} (hY : IsTerminal Y) (f : X ⟶ Y) : IsIsoFibration f
  [has_products : HasConicalProducts K]
  prod_map_fibrant {γ : Type w} {A B : γ → K} (f : ∀ i, A i ↠ B i) :
    IsIsoFibration (Limits.Pi.map (λ i ↦ (f i).1))
  [has_isoFibration_pullbacks {A B E : K} (f : A ⟶ B) (g : E ↠ B) : HasConicalPullback f g.1]
  pullback_is_isoFibration {A B E P : K} (f : A ⟶ B) (g : E ↠ B)
    (fst : P ⟶ A) (snd : P ⟶ E) (h : IsPullback fst snd f g.1) : IsIsoFibration fst
  [has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsoFibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasConicalLimit F]
  has_limits_of_towers_isIsoFibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsoFibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K]
  leibniz_cotensor  {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) {P : K}
    (fst : P ⟶ V ⋔ B) (snd : P ⟶ U ⋔ A)
    (h : IsPullback fst snd (cotensorContraMap i B) (cotensorCovMap U f)) :
    IsIsoFibration (h.isLimit.lift <|
      PullbackCone.mk (cotensorCovMap V f.1) (cotensorContraMap i A)
        (cotensor_bifunctoriality i f.1))
  local_isoFibration {X A B : K} (f : A ↠ B) : IsoFibration (toFunMap X f.1)

open InfinityCosmos'

attribute [instance] has_products has_isoFibration_pullbacks has_limits_of_towers has_cotensors

section tests
variable {K : Type u} [Category.{v} K] [InfinityCosmos' K]

open InfinityCosmos PreInfinityCosmos

-- This only works because of `HasConicalProducts_hasConicalTerminal'` which has a sorry.
instance : HasConicalTerminal K := by infer_instance

instance : HasTerminal K := by infer_instance

instance : HasProducts K := by infer_instance

theorem binary_prod_map_fibrant {X Y X' Y' : K} {f : X ↠ Y} {g : X' ↠ Y'} :
    IsIsoFibration (prod.map f.1 g.1) := sorry

def compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C :=
  ⟨(f.1 ≫ g.1), comp_isIsoFibration f g⟩

end tests

class InfinityCosmos extends SimplicialCategory K where
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  IsIsoFibration {X Y : K} : (X ⟶ Y) → Prop
  comp_isIsoFibration {X Y Z : K} {f : X ⟶ Y} {g : Y ⟶ Z} :
    IsIsoFibration f → IsIsoFibration g → IsIsoFibration (f ≫ g)
  iso_isIsoFibration {X Y : K} (e : X ≅ Y) : IsIsoFibration e.hom
  --has_terminal : HasConicalTerminal K
  all_objects_fibrant {X Y : K} (hY : IsTerminal Y) (f : X ⟶ Y) : IsIsoFibration f -- TODO: replace by IsConicalTerminal?
  has_products : HasConicalProducts K
  prod_map_fibrant {γ : Type w} {A B : γ → K} (f : ∀ i, A i ⟶ B i) :
    (∀ i, IsIsoFibration (f i)) → IsIsoFibration (Limits.Pi.map f)
  [has_isoFibration_pullbacks {X Y Z : K} (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsIsoFibration g → HasConicalPullback f g]
  pullback_is_isoFibration {X Y Z P : K} (f : X ⟶ Z) (g : Y ⟶ Z)
    (fst : P ⟶ X) (snd : P ⟶ Y) (h : IsPullback fst snd f g) :
    IsIsoFibration g → IsIsoFibration fst
  has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsoFibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasConicalLimit F
  has_limits_of_towers_isIsoFibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsoFibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K]
  leibniz_cotensor {X Y : K} (f : X ⟶ Y) (A B : SSet) (i : A ⟶ B) [Mono i]
    (hf : IsIsoFibration f) {P : K} (fst : P ⟶ B ⋔ Y) (snd : P ⟶ A ⋔ X)
    (h : IsPullback fst snd (cotensorContraMap i Y) (cotensorCovMap A f)) :
    IsIsoFibration (h.isLimit.lift <|
      PullbackCone.mk (cotensorCovMap B f) (cotensorContraMap i X) (cotensor_bifunctoriality i f)) --TODO : Prove that these pullbacks exist.
  local_isoFibration {X A B : K} (f : A ⟶ B) (hf : IsIsoFibration f) : IsoFibration (toFunMap X f)

end CategoryTheory
