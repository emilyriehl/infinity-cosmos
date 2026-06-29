import Architect
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Cotensors
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.HasConicalTerminal
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.IsConicalTerminal
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalPullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

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

/-- Representable maps preserve identity morphisms. -/
lemma representableMap_id (X A : K) :
    representableMap X (𝟙 A) = 𝟙 (EnrichedCategory.Hom X A : SSet) := by
  change eHomWhiskerLeft SSet X (𝟙 A) = 𝟙 (EnrichedCategory.Hom X A : SSet)
  rw [eHomWhiskerLeft_id]

/-- Representable maps preserve composition. -/
lemma representableMap_comp {A B C : K} (X : K) (f : A ⟶ B) (g : B ⟶ C) :
    representableMap X (f ≫ g) = representableMap X f ≫ representableMap X g := by
  change eHomWhiskerLeft SSet X (f ≫ g) =
    eHomWhiskerLeft SSet X f ≫ eHomWhiskerLeft SSet X g
  rw [eHomWhiskerLeft_comp]

noncomputable def toFunMap (X : K) {A B : K} (f : A ⟶ B) : Fun X A ⟶ Fun X B :=
  ObjectProperty.homMk <| representableMap X f

/-- A morphism in a pre-∞-cosmos is an equivalence if every covariant representable sends it
to an equivalence of quasi-categories. -/
def Equivalence {A B : K} (f : A ⟶ B) : Prop :=
  ∀ X : K,
    ∃ e : @QCat.Equiv (Fun X A).obj (Fun X B).obj (Fun X A).property (Fun X B).property,
      e.toFun = (toFunMap X f).hom

/-- A morphism in a pre-∞-cosmos is a trivial fibration if it is both an isofibration and an
equivalence. -/
def TrivialFibration {A B : K} (f : A ⟶ B) : Prop :=
  IsIsofibration f ∧ Equivalence f

/-- A trivial fibration is an isofibration. -/
lemma TrivialFibration.isIsofibration {A B : K} {f : A ⟶ B} (hf : TrivialFibration f) :
    IsIsofibration f :=
  hf.1

/-- A trivial fibration is an equivalence. -/
lemma TrivialFibration.equivalence {A B : K} {f : A ⟶ B} (hf : TrivialFibration f) :
    Equivalence f :=
  hf.2

/-- The subtype of isofibrations. Arguments of this type have the form `⟨ f hf ⟩`. -/
def Isofibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsofibration f}

/-- Type with "\rr". -/
infixr:25 " ↠ " => Isofibration

instance (A B : K) : Coe (A ↠ B) (A ⟶ B) := ⟨fun f ↦ f.1⟩

end InfinityCosmos

open PreInfinityCosmos InfinityCosmos Enriched

variable (K : Type u) [Category.{v} K]

/-- An `InfinityCosmos` extends a `PreInfinityCosmos` with limit and isofibration axioms. -/
@[blueprint
  "defn:cosmos"
  (title := "$\\infty$-cosmos")
  (statement := /--
  An $\infty$-\textbf{cosmos} $\cK$ is a category that is enriched over
  quasi-categories,\footnote{This is to say $\cK$ is a simplicially enriched category (see
  Definition \ref{defn:simplicial-category}) whose hom spaces are all quasi-categories.} meaning in
  particular that\begin{itemize}
  \item its morphisms $f \colon A \to B$ define the vertices of a quasi-category denoted $\Fun(A,B)$
  and referred to as a \textbf{functor space},
  \end{itemize}
  that is also equipped with a specified collection of maps that we call \textbf{isofibrations} and
  denote by ``$\fib$'' satisfying the following two axioms:
  \begin{enumerate}
  \item\label{itm:cosmos-limits} (completeness) The quasi-categorically enriched category $\cK$
  pos\-sess\-es a terminal object, small products, pullbacks of isofibrations, limits of countable
  towers of isofibrations, and cotensors with simplicial sets, each of these limit notions
  satisfying a universal property that is enriched over simplicial sets.\footnote{This is to say,
  these are simplicially enriched limit notions, in the sense described in Definitions
  \ref{defn:simplicial-cotensor} and \ref{defn:simplicial-conical-limit}.}
  \item\label{itm:cosmos-isofib} (isofibrations) The isofibrations contain all isomorphisms and any
  map whose codomain is the terminal object; are closed under composition, product, pullback,
  forming inverse limits of towers, and Leibniz cotensors with monomorphisms of simplicial sets; and
  have the property that if $f \colon A \fib B$ is an isofibration and $X$ is any object then
  $\Fun(X,A) \fib \Fun(X,B)$ is an isofibration of quasi-categories.
  \end{enumerate}
  -/)]
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
  has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsofibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasConicalLimit SSet F
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

attribute [instance] has_products has_isofibration_pullbacks has_cotensors

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

/-! ### The underlying category of an ∞-cosmos

The underlying category `K₀` of an ∞-cosmos `K` (blueprint `defn:underlying-cat-of-cosmos`) has the
∞-categories of `K` as objects and the `0`-arrows as morphisms, where a `0`-arrow `A ⟶ B` is a
vertex of the functor space `Fun A B`. Since a simplicial category is formalized as an enriched
ordinary category, `K` already carries this `1`-category structure: the ambient `Category K`
instance is, by definition, the underlying category. The equivalence `homEquivFunVertex` records the
characterization requested in the blueprint, identifying the morphisms of this category with the
vertices of the functor spaces. -/

/-- The underlying category of an ∞-cosmos `K` is the ambient `1`-category structure on `K`. -/
example : Category K := inferInstance

/-- A morphism `A ⟶ B` in the underlying category of an ∞-cosmos is the same data as a `0`-arrow:
a vertex of the functor space `Fun A B`, i.e. a map from the monoidal unit `𝟙_ SSet` into it. -/
def homEquivFunVertex {A B : K} : (A ⟶ B) ≃ (𝟙_ SSet ⟶ (Fun A B).obj) :=
  eHomEquiv SSet

/-- Under the identification of morphisms with `0`-arrows, the identity morphism corresponds to the
enriched identity vertex. -/
lemma homEquivFunVertex_id (A : K) : homEquivFunVertex (𝟙 A) = eId SSet A :=
  eHomEquiv_id SSet A

end InfinityCosmos

end CategoryTheory
