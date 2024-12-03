import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Cotensors
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Limits
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

namespace CategoryTheory
open Category Limits Functor MonoidalCategory Simplicial SimplicialCategory SSet
universe w v v₁ v₂ u u₁ u₂

variable (K : Type u) [Category.{v} K] [SimplicialCategory K]

/-- A `PreInfinityCosmos` is a simplicially enriched category whose hom-spaces are quasi-categories
and whose morphisms come equipped with a special class of isofibrations.-/
class PreInfinityCosmos extends SimplicialCategory K where
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  IsIsofibration : MorphismProperty K

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
def Isofibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsofibration f}

-- Type with "\rr".
infixr:25  " ↠ " => Isofibration

instance (A B : K) : Coe (A ↠ B) (A ⟶ B) := ⟨ λ f ↦ f.1 ⟩

end InfinityCosmos

open PreInfinityCosmos InfinityCosmos
variable (K : Type u) [Category.{v} K][PreInfinityCosmos.{v} K]

/-- Experimenting with some changes.-/
class InfinityCosmos extends PreInfinityCosmos K where
  comp_isIsofibration {X Y Z : K} (f : X ↠ Y) (g : Y ↠ Z) : IsIsofibration (f.1 ≫ g.1)
  iso_isIsofibration {X Y : K} (e : X ⟶ Y) [IsIso e] : IsIsofibration e
  all_objects_fibrant {X Y : K} (hY : IsTerminal Y) (f : X ⟶ Y) : IsIsofibration f
        -- TODO: replace by IsConicalTerminal?
  [has_products : HasConicalProducts K]
  prod_map_fibrant {γ : Type w} {A B : γ → K} (f : ∀ i, A i ↠ B i) :
    IsIsofibration (Limits.Pi.map (λ i ↦ (f i).1))
  [has_isoFibration_pullbacks {A B E : K} (f : A ⟶ B) (g : E ↠ B) : HasConicalPullback f g.1]
  pullback_is_isoFibration {A B E P : K} (f : A ⟶ B) (g : E ↠ B)
    (fst : P ⟶ A) (snd : P ⟶ E) (h : IsPullback fst snd f g.1) : IsIsofibration fst
  [has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsofibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasConicalLimit F]
  has_limits_of_towers_isIsofibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsofibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K]
  leibniz_cotensor  {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) {P : K}
    (fst : P ⟶ V ⋔ B) (snd : P ⟶ U ⋔ A)
    (h : IsPullback fst snd (cotensorContraMap i B) (cotensorCovMap U f)) :
    IsIsofibration (h.isLimit.lift <|
      PullbackCone.mk (cotensorCovMap V f.1) (cotensorContraMap i A)
        (cotensor_bifunctoriality i f.1)) --TODO : Prove that these pullbacks exist.
  local_isoFibration {X A B : K} (f : A ↠ B) : Isofibration (toFunMap X f.1)


attribute [instance] has_products has_isoFibration_pullbacks has_limits_of_towers has_cotensors

namespace InfinityCosmos

variable {K : Type u} [Category.{v} K] [InfinityCosmos K]

open InfinityCosmos PreInfinityCosmos

instance : HasConicalTerminal K := by infer_instance

instance : HasCotensors K := by infer_instance

instance : HasTerminal K := by infer_instance

instance : HasProducts K := by infer_instance

theorem binary_prod_map_fibrant {X Y X' Y' : K} {f : X ↠ Y} {g : X' ↠ Y'} :
    IsIsofibration (prod.map f.1 g.1) := sorry

def compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C :=
  ⟨(f.1 ≫ g.1), comp_isIsofibration f g⟩

section pullbacks

lemma initialSquare_isPullback' (U : SSet.{v}) (B : K) :
    IsPullback  (cotensorContraMap (initial.to U) B) (𝟙 _)
    (𝟙 _) (cotensorContraMap (initial.to U) B) := IsPullback.of_id_snd

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.
noncomputable def cotensorInitialIso (A : K) : (⊥_ SSet ) ⋔ A ≅ ⊤_ K where
  hom := terminal.from ((⊥_ SSet) ⋔ A)
  inv := (cotensor.iso.underlying (⊥_ SSet) A (⊤_ K)).symm (initial.to (sHom (⊤_ K) A))
  hom_inv_id := (cotensor.iso.underlying (⊥_ SSet) A ((⊥_ SSet ) ⋔ A)).injective
    (initial.hom_ext _ _)
  inv_hom_id := terminal.hom_ext _ _

noncomputable instance cotensorInitial_isTerminal (A : K) : IsTerminal ((⊥_ SSet ) ⋔ A) :=
  terminalIsTerminal.ofIso (id (cotensorInitialIso A).symm)

noncomputable def initialSquare.snd (U : SSet.{v}) (A B : K) : U ⋔ B ⟶ (⊥_ SSet ) ⋔ A :=
  terminal.from (U ⋔ B) ≫ (cotensorInitialIso A).inv

lemma initialSquare_isIso {A B : K} (f : A ⟶ B) : IsIso (cotensorCovMap (⊥_ SSet) f) :=
  isIso_of_isTerminal (cotensorInitial_isTerminal A) (cotensorInitial_isTerminal B)
    (cotensorCovMap (⊥_ SSet) f)

lemma initialSquare_isPullback (U : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsPullback (𝟙 _) (initialSquare.snd U A B)
      (cotensorContraMap (initial.to U) B) (cotensorCovMap (⊥_ SSet) f.1) := by
  have := initialSquare_isIso f.1
  refine IsPullback.of_horiz_isIso ?_
  unfold initialSquare.snd
  constructor
  apply IsTerminal.hom_ext (cotensorInitial_isTerminal _)

theorem cotensorCovMap_fibrant (U : SSet.{v}) {A B : K} (f : A ↠ B) :
    IsIsofibration (cotensorCovMap U f.1) := by
  let map : ⊥_ SSet ⟶ U := initial.to U
  have hyp : Mono map := Initial.mono_to U
  have := leibniz_cotensor (initial.to U) f _ _ (initialSquare_isPullback U f)
  have := IsPullback.lift_fst (initialSquare_isPullback U f) (cotensorCovMap U f.1)
    (cotensorContraMap (initial.to U) A) (cotensor_bifunctoriality (initial.to U) f.1)
  simp only [comp_id] at this
  rw [← this]
  exact (leibniz_cotensor (initial.to U) f _ _ (initialSquare_isPullback U f))

end pullbacks

end InfinityCosmos

end CategoryTheory
