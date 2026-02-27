import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Cotensors
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.HasConicalTerminal
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.IsConicalTerminal
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalPullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

namespace CategoryTheory

open Category Limits MonoidalCategory SimplicialCategory EnrichedOrdinaryCategory Enriched SSet

universe w v u

variable (K : Type u) [Category.{v} K] [SimplicialCategory K]

/-- A `PreInfinityCosmos` is a simplicially enriched category whose hom-spaces are quasi-categories
and whose morphisms come equipped with a special class of isofibrations. -/
class PreInfinityCosmos extends SimplicialCategory K where
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  IsIsofibration : MorphismProperty K

namespace InfinityCosmos

variable {K : Type u} [Category.{v} K] [PreInfinityCosmos.{v} K]

open PreInfinityCosmos

/-- Common notation for the hom-spaces in a pre-∞-cosmos. -/
def Fun (A B : K) : QCat where
  obj := EnrichedCategory.Hom A B
  property := has_qcat_homs

noncomputable def representableMap' {X A B : K} (f : 𝟙_ SSet ⟶ EnrichedCategory.Hom A B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ EnrichedCategory.Hom X B :=
  (ρ_ _).inv ≫ _ ◁ f ≫ EnrichedCategory.comp (V := SSet) X A B

noncomputable def representableMap (X : K) {A B : K} (f : A ⟶ B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ EnrichedCategory.Hom X B :=
  representableMap' (eHomEquiv SSet f)

noncomputable def toFunMap (X : K) {A B : K} (f : A ⟶ B) : Fun X A ⟶ Fun X B :=
  representableMap X f

/-- The subtype of isofibrations. Arguments of this type have the form `⟨ f hf ⟩`. -/
def Isofibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsofibration f}

/-- Type with "\rr". -/
infixr:25 " ↠ " => Isofibration

instance (A B : K) : Coe (A ↠ B) (A ⟶ B) := ⟨fun f ↦ f.1⟩

end InfinityCosmos

open PreInfinityCosmos InfinityCosmos Enriched

variable (K : Type u) [Category.{v} K]

/-- An `InfinityCosmos` extends a `PreInfinityCosmos` with limit and isofibration axioms. -/
class InfinityCosmos extends PreInfinityCosmos K where
  comp_isIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : IsIsofibration (f.1 ≫ g.1)
  iso_isIsofibration {X Y : K} (e : X ⟶ Y) [IsIso e] : IsIsofibration e
  all_objects_fibrant {X Y : K} (hY : IsConicalTerminal SSet Y) (f : X ⟶ Y) : IsIsofibration f
  [has_products : HasConicalProducts SSet K]
  prod_map_fibrant {γ : Type w} {A B : γ → K} (f : ∀ i, A i ↠ B i) :
    IsIsofibration (Limits.Pi.map (fun i ↦ (f i).1))
  [has_isofibration_pullbacks {E B A : K} (p : E ↠ B) (f : A ⟶ B) :
    HasConicalPullback SSet p.1 f]
  pullback_isIsofibration {E B A P : K} (p : E ↠ B) (f : A ⟶ B)
    (fst : P ⟶ E) (snd : P ⟶ A) (h : IsPullback fst snd p.1 f) : IsIsofibration snd
  [has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsofibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasConicalLimit SSet F]
  has_limits_of_towers_isIsofibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsofibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K]
  leibniz_cotensor_isIsofibration {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B)
    {P : K} (fst : P ⟶ U ⋔ A) (snd : P ⟶ V ⋔ B)
    (h : IsPullback fst snd (cotensorCovMap U f.1) (cotensorContraMap i B)) :
    IsIsofibration (h.isLimit.lift <|
      PullbackCone.mk (cotensorContraMap i A) (cotensorCovMap V f.1)
        (cotensor_bifunctoriality i f.1))
  local_isoFibration {X A B : K} (f : A ↠ B) : Isofibration (toFunMap X f.1)

attribute [instance] has_products has_isofibration_pullbacks has_limits_of_towers has_cotensors

namespace InfinityCosmos

variable {K : Type u} [Category.{v} K] [InfinityCosmos K]

/-- An ∞-cosmos has a conical terminal object as `SSet`-enriched limit. -/
example : HasConicalTerminal SSet K := inferInstance

/-- An ∞-cosmos has a terminal object. -/
example : HasTerminal K := inferInstance

/-- An ∞-cosmos has cotensors. -/
example : HasCotensors K := inferInstance

/-- An ∞-cosmos has products. -/
example : HasProducts K := inferInstance

/-- An ∞-cosmos has pullbacks. -/
example {E B A : K} (p : E ↠ B) (f : A ⟶ B) : HasPullback p.1 f := inferInstance

end InfinityCosmos

end CategoryTheory
