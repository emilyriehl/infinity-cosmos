import Architect
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Cotensors

namespace CategoryTheory

open SimplicialCategory MonoidalCategory BraidedCategory MonoidalClosed

universe v v₁ v₂ u u₁ u₂

section specialization

namespace SimplicialCategory

variable {K : Type u} [Category.{v} K] [SimplicialCategory K]

open Enriched

/-- A specialization of the enriched category cotensor. -/
abbrev Cotensor (U : SSet) (A : K) := Enriched.Cotensor U A

noncomputable section

def cotensorPostcompose {U : SSet} {A B : K} (ua : Cotensor U A) (ub : Cotensor U B)
    (f : A ⟶ B) : ua.obj ⟶ ub.obj :=
  (eHomEquiv SSet).symm (eHomEquiv SSet f ≫ Cotensor.postcompose _ ua ub)

def cotensorPrecompose {U V : SSet} {A : K} (ua : Cotensor U A) (va : Cotensor V A)
    (i : U ⟶ V) : va.obj ⟶ ua.obj :=
  (eHomEquiv SSet).symm (eHomEquiv SSet i ≫ Cotensor.EhomPrecompose _ ua va)

lemma cotensorPostcompose_homEquiv {U : SSet} {A B : K} (ua : Cotensor U A) (ub : Cotensor U B)
    (f : A ⟶ B) : eHomEquiv SSet (cotensorPostcompose ua ub f) =
      eHomEquiv SSet f ≫ Cotensor.postcompose _ ua ub := by
  simp [cotensorPostcompose]

lemma cotensorPrecompose_homEquiv {U V : SSet} {A : K} (ua : Cotensor U A) (va : Cotensor V A)
    (i : U ⟶ V) : eHomEquiv SSet (cotensorPrecompose ua va i) =
      eHomEquiv SSet i ≫ Cotensor.EhomPrecompose _ ua va := by
  simp [cotensorPrecompose]

set_option backward.isDefEq.respectTransparency false in
theorem cotensor_local_bifunctoriality {U V : SSet} {A B : K}
    (ua : Cotensor U A) (ub : Cotensor U B) (va : Cotensor V A) (vb : Cotensor V B)
    (i : U ⟶ V) (f : A ⟶ B) :
    cotensorPrecompose ua va i ≫ cotensorPostcompose ua ub f =
      cotensorPostcompose va vb f ≫ cotensorPrecompose ub vb i := by
  apply (eHomEquiv SSet).injective
  rw [eHomEquiv_comp, eHomEquiv_comp]
  have thm := Cotensor.post_pre_eq_pre_post _ ua ub va vb
  have compeq := whisker_eq ((λ_ _).inv ≫ (eHomEquiv SSet i ⊗ₘ eHomEquiv SSet f)) thm
  rw [Category.assoc, tensorHom_comp_tensorHom_assoc] at compeq
  rw [← cotensorPostcompose_homEquiv, ← cotensorPrecompose_homEquiv] at compeq
  rw [compeq]
  slice_lhs 2 3 =>
    rw [tensorHom_comp_tensorHom, ← cotensorPostcompose_homEquiv, ← cotensorPrecompose_homEquiv]
  simp only [braiding_naturality, braiding_tensorUnit_right, Category.assoc,
    Iso.cancel_iso_inv_left]
  monoidal

end

/-- `HasCotensor U A` represents the mere existence of a simplicial cotensor. -/
@[blueprint
  "defn:simplicial-cotensor"
  (title := "simplicial cotensors")
  (statement := /--
  Let $\cA$ be a simplicial category. The \textbf{cotensor} of an object $A \in \cA$ by a simplicial
  set $U$ is given by the data of an object $A^U \in \cA$ together with a cone $U \to \cA(A^U,A)$ so
  that the induced map
  defines an isomorphism of simplicial sets:
  \begin{equation}\label{eq:cotensor-defn}
  \cA(X,A^U) \cong \cA(X,A)^U
  \end{equation}
  -/)]
class HasCotensor (U : SSet) (A : K) : Prop where mk' ::
  /-- There is some cotensor. -/
  exists_cotensor : Nonempty (Cotensor U A)

theorem HasCotensor.mk {U : SSet} {A : K} (c : Cotensor U A) : HasCotensor U A :=
  ⟨Nonempty.intro c⟩

/-- Use the axiom of choice to extract explicit `CotensorCone A X` from `HasCotensor A X`. -/
noncomputable def getCotensor (U : SSet) (A : K) [HasCotensor U A] : Cotensor U A :=
  Classical.choice HasCotensor.exists_cotensor

noncomputable section

/-- An arbitrary choice of cotensor obj. -/
def cotensor.obj (U : SSet) (A : K) [HasCotensor U A] : K := (getCotensor U A).obj

infixr:60 " ⋔ " => cotensor.obj

/-- The associated cotensor cone. -/
def cotensor.cone (U : SSet) (A : K) [HasCotensor U A] : U ⟶ sHom (U ⋔ A) A :=
  (getCotensor U A).cone

/-- The universal property of this cone. -/
def cotensor.is_cotensor (U : SSet) (A : K) [HasCotensor U A] : Cotensor U A := getCotensor U A

/-- The natural isomorphism induced by a cotensor. -/
def cotensor.iso (U : SSet) (A : K) [HasCotensor U A] (X : K) :
    sHom X (U ⋔ A) ≅ (ihom U).obj (sHom X A) where
  hom := Precotensor.coneNatTrans _ _
  inv := (getCotensor U A).coneNatTransInv _
  hom_inv_id := (getCotensor U A).NatTrans_NatTransInv_eq _
  inv_hom_id := (getCotensor U A).NatTransInv_NatTrans_eq _

def cotensor.iso.underlying (U : SSet) (A : K) [HasCotensor U A] (X : K) :
    (X ⟶ U ⋔ A) ≃ (U ⟶ sHom X A) :=
  (SimplicialCategory.homEquiv' X (U ⋔ A)).trans <|
    (((evaluation SimplexCategoryᵒᵖ (Type _)).obj ⟨SimplexCategory.mk 0⟩).mapIso
      (cotensor.iso U A X)).toEquiv.trans
        (SimplicialCategory.homEquiv' U (sHom X A)).symm

/-- Ordinary composition, transported to zero-simplices of the enriched hom. -/
lemma homEquiv'_comp {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv' X Z (f ≫ g) =
      ((sHomWhiskerRight f Z).app (Opposite.op (SimplexCategory.mk 0)))
        (homEquiv' Y Z g) := by
  simp [homEquiv', sHomWhiskerRight, eHomEquiv_comp, eHomWhiskerRight, SSet.unitHomEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary composition in the right variable, transported to enriched morphisms. -/
lemma eHomEquiv_comp_eHomWhiskerRight {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet g ≫ eHomWhiskerRight SSet f Z = eHomEquiv SSet (f ≫ g) := by
  apply (SSet.unitHomEquiv (sHom X Z)).injective
  change ((sHomWhiskerRight f Z).app (Opposite.op (SimplexCategory.mk 0)))
      (homEquiv' Y Z g) = homEquiv' X Z (f ≫ g)
  rw [homEquiv'_comp]

/-- The identity morphism, transported to zero-simplices of the enriched hom. -/
lemma homEquiv'_id (X : K) :
    homEquiv' X X (𝟙 X) = ((eId SSet X).app ⟨SimplexCategory.mk 0⟩) PUnit.unit := by
  simp [homEquiv', SSet.unitHomEquiv]

/-- The zero-simplex form of `cotensor.iso.underlying`. -/
lemma cotensor_underlying_homEquiv (U : SSet.{v}) (A X : K) [HasCotensor U A]
    (h : X ⟶ U ⋔ A) :
    homEquiv' U (sHom X A) ((cotensor.iso.underlying U A X) h) =
      (((evaluation SimplexCategoryᵒᵖ (Type v)).obj ⟨SimplexCategory.mk 0⟩).map
        (cotensor.iso U A X).hom) (homEquiv' X (U ⋔ A) h) := by
  change homEquiv' U (sHom X A)
      ((homEquiv' U (sHom X A)).symm
        ((((evaluation SimplexCategoryᵒᵖ (Type v)).obj ⟨SimplexCategory.mk 0⟩).mapIso
          (cotensor.iso U A X)).toEquiv (homEquiv' X (U ⋔ A) h))) =
      (((evaluation SimplexCategoryᵒᵖ (Type v)).obj ⟨SimplexCategory.mk 0⟩).map
        (cotensor.iso U A X).hom) (homEquiv' X (U ⋔ A) h)
  simp

/-- Composition in `SSet`, expressed through the closed structure. -/
lemma homEquiv'_comp_sset_ihom {U V W : SSet.{v}} (i : U ⟶ V) (f : V ⟶ W) :
    homEquiv' U W (i ≫ f) =
      ((eHomEquiv SSet i ≫ (ihom U).map f).app ⟨SimplexCategory.mk 0⟩) PUnit.unit := by
  change (((curry' (i ≫ f)).app ⟨SimplexCategory.mk 0⟩) PUnit.unit) =
    (((curry' i ≫ (ihom U).map f).app ⟨SimplexCategory.mk 0⟩) PUnit.unit)
  rw [curry'_ihom_map]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of a cotensor cone in the representing object. -/
lemma cotensor_coneNatTrans_naturality_left {U : SSet.{v}} {A X Y : K}
    (ux : Cotensor U A) (h : X ⟶ Y) :
    eHomWhiskerRight SSet h ux.obj ≫ ux.coneNatTrans X =
      ux.coneNatTrans Y ≫ (ihom U).map (eHomWhiskerRight SSet h A) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  rw [ux.coneNatTrans_eq, ux.coneNatTrans_eq]
  simp only [Category.assoc]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  rw [← eComp_eHomWhiskerRight]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating a cotensor cone at the identity of its representing object recovers the cone. -/
lemma cotensor_coneNatTrans_eId {U : SSet.{v}} {A : K} (ux : Cotensor U A) :
    eId SSet ux.obj ≫ ux.coneNatTrans ux.obj = curry' ux.cone := by
  apply uncurry'_injective
  change (ρ_ U).inv ≫ uncurry (eId SSet ux.obj ≫ ux.coneNatTrans ux.obj) = ux.cone
  rw [uncurry_natural_left, ux.coneNatTrans_eq]
  rw [braiding_naturality_right_assoc, braiding_tensorUnit_right_assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  rw [e_id_comp, Category.comp_id]

/-- The zero-simplex form of `cotensor_coneNatTrans_eId`. -/
lemma cotensor_coneNatTrans_id {U : SSet.{v}} (A : K) [HasCotensor U A] :
    ((getCotensor U A).coneNatTrans (U ⋔ A)).app ⟨SimplexCategory.mk 0⟩
      (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _)) =
    homEquiv' U (sHom (U ⋔ A) A) (getCotensor U A).cone := by
  rw [homEquiv'_id]
  change (((eId SSet (getCotensor U A).obj ≫
    (getCotensor U A).coneNatTrans (getCotensor U A).obj).app
    ⟨SimplexCategory.mk 0⟩) PUnit.unit) = _
  have h := congrArg (fun f : 𝟙_ SSet ⟶ (ihom U).obj (sHom (U ⋔ A) A) =>
      f.app ⟨SimplexCategory.mk 0⟩ PUnit.unit)
    (cotensor_coneNatTrans_eId (getCotensor U A))
  exact h.trans (by rfl)

/-- The underlying map of a cotensor isomorphism is represented by the chosen cotensor cone. -/
lemma cotensor_iso_underlying_eq_cone {U : SSet.{v}} (A X : K) [HasCotensor U A]
    (h : X ⟶ U ⋔ A) :
    (cotensor.iso.underlying U A X) h =
      (getCotensor U A).cone ≫ eHomWhiskerRight SSet h A := by
  apply (homEquiv' U (sHom X A)).injective
  rw [cotensor_underlying_homEquiv]
  change (((getCotensor U A).coneNatTrans X).app ⟨SimplexCategory.mk 0⟩
      (homEquiv' X (U ⋔ A) h)) =
    ((sHomWhiskerLeft U (eHomWhiskerRight SSet h A)).app ⟨SimplexCategory.mk 0⟩)
      (homEquiv' U (sHom (U ⋔ A) A) (getCotensor U A).cone)
  conv_lhs => rw [← Category.comp_id h, homEquiv'_comp]
  rw [← cotensor_coneNatTrans_id]
  have hn := congrArg
    (fun f : sHom (U ⋔ A) (U ⋔ A) ⟶ (ihom U).obj (sHom X A) =>
      f.app ⟨SimplexCategory.mk 0⟩ (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _)))
    (cotensor_coneNatTrans_naturality_left (getCotensor U A) h)
  change (((eHomWhiskerRight SSet h (getCotensor U A).obj ≫
      (getCotensor U A).coneNatTrans X).app ⟨SimplexCategory.mk 0⟩)
      (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _))) =
    (((getCotensor U A).coneNatTrans (U ⋔ A) ≫
      (ihom U).map (eHomWhiskerRight SSet h A)).app ⟨SimplexCategory.mk 0⟩)
      (homEquiv' (U ⋔ A) (U ⋔ A) (𝟙 _))
  exact hn

end

variable (K) in
/-- `K` has simplicial cotensors when cotensors with any simplicial set exist. -/
@[blueprint
  "defn:simplicial-cotensors"
  (title := "simplicial cotensors")
  (statement := /-- A simplicial category $\cA$ \textbf{has cotensors} when all cotensors exist. -/)]
class HasCotensors : Prop where
  /-- All `U : SSet` and `A : K` have a cotensor. -/
  has_cotensors : ∀ U : SSet, ∀ A : K, HasCotensor U A := by infer_instance

instance (priority := 100) hasCotensorsOfHasCotensors {K : Type u} [Category.{v} K]
    [SimplicialCategory K] [HasCotensors K] (U : SSet) (A : K) : HasCotensor U A :=
  HasCotensors.has_cotensors U A

section

variable {K : Type u} [Category.{v} K] [SimplicialCategory K] [HasCotensors K]

noncomputable def cotensorCovMap (U : SSet) {A B : K} (f : A ⟶ B) : U ⋔ A ⟶ U ⋔ B :=
  cotensorPostcompose _ _ f

noncomputable def cotensorContraMap {U V : SSet} (i : U ⟶ V) (A : K) : V ⋔ A ⟶ U ⋔ A :=
  cotensorPrecompose _ _ i

/-- The zero-simplex corresponding to a contravariant cotensor map. -/
lemma homEquiv'_cotensorContraMap {U V : SSet.{v}} (i : U ⟶ V) (A : K) :
    homEquiv' (V ⋔ A) (U ⋔ A) (cotensorContraMap i A) =
      ((eHomEquiv SSet i ≫
        Cotensor.EhomPrecompose SSet (getCotensor U A) (getCotensor V A)).app
        ⟨SimplexCategory.mk 0⟩) PUnit.unit := by
  change (((eHomEquiv SSet) (cotensorPrecompose (getCotensor U A)
    (getCotensor V A) i)).app ⟨SimplexCategory.mk 0⟩) PUnit.unit = _
  rw [cotensorPrecompose_homEquiv]

/-- The chosen cotensor cone is natural with respect to contravariant cotensor maps. -/
lemma cotensor_contraMap_cone {U V : SSet.{v}} (i : U ⟶ V) (A : K) :
    (getCotensor U A).cone ≫ eHomWhiskerRight SSet (cotensorContraMap i A) A =
      i ≫ (getCotensor V A).cone := by
  rw [← cotensor_iso_underlying_eq_cone]
  apply (homEquiv' U (sHom (V ⋔ A) A)).injective
  rw [cotensor_underlying_homEquiv]
  change (((getCotensor U A).coneNatTrans (V ⋔ A)).app ⟨SimplexCategory.mk 0⟩
      (homEquiv' (V ⋔ A) (U ⋔ A) (cotensorContraMap i A))) =
    homEquiv' U (sHom (V ⋔ A) A) (i ≫ (getCotensor V A).cone)
  rw [homEquiv'_comp_sset_ihom, homEquiv'_cotensorContraMap]
  change (((eHomEquiv SSet i ≫
      Cotensor.EhomPrecompose SSet (getCotensor U A) (getCotensor V A) ≫
      (getCotensor U A).coneNatTrans (V ⋔ A)).app ⟨SimplexCategory.mk 0⟩) PUnit.unit) = _
  have hpre : eHomEquiv SSet i ≫
      Cotensor.EhomPrecompose SSet (getCotensor U A) (getCotensor V A) ≫
      (getCotensor U A).coneNatTrans (V ⋔ A) =
      eHomEquiv SSet i ≫ (ihom U).map (getCotensor V A).cone :=
    (Category.assoc _ _ _).trans
      (whisker_eq (eHomEquiv SSet i)
        (Cotensor.EhomPrecompose_coneNatTrans_eq SSet (getCotensor U A) (getCotensor V A)))
  rw [hpre]
  rfl

/-- Naturality of `cotensor.iso.underlying` under precomposition in the simplicial-set variable. -/
lemma cotensor_iso_underlying_precompose {U V : SSet.{v}} (i : U ⟶ V) (A X : K)
    (g : X ⟶ V ⋔ A) :
    (cotensor.iso.underlying U A X) (g ≫ cotensorContraMap i A) =
      i ≫ (cotensor.iso.underlying V A X) g := by
  rw [cotensor_iso_underlying_eq_cone, cotensor_iso_underlying_eq_cone]
  rw [eHomWhiskerRight_comp]
  change (((getCotensor U A).cone ≫ eHomWhiskerRight SSet (cotensorContraMap i A) A) ≫
      eHomWhiskerRight SSet g A) =
    ((i ≫ (getCotensor V A).cone) ≫ eHomWhiskerRight SSet g A)
  exact congrArg (fun f => f ≫ eHomWhiskerRight SSet g A) (cotensor_contraMap_cone i A)


@[blueprint
  "lem:cotensor-bifunctor"
  (statement := /--
  Assuming such objects exist, the simplicial cotensor defines a bifunctor
  \begin{center}
  \begin{tikzcd}[row sep=tiny] s\mathcal{S}et\op \times \cA \arrow[r] & \cA \\
  (U,A) \arrow[r, maps to] & A^U
  \end{tikzcd}\end{center} in a unique way making the isomorphism \eqref{eq:cotensor-defn} natural
  in $U$ and $A$ as well.
  -/)
  (proof := /-- Functoriality in each variable follows from the universal property. -/)
  (latexEnv := "lemma")]
theorem cotensor_bifunctoriality {U V : SSet} (i : U ⟶ V) {A B : K} (f : A ⟶ B) :
    cotensorContraMap i A ≫ cotensorCovMap U f =
      cotensorCovMap V f ≫ cotensorContraMap i B :=
  cotensor_local_bifunctoriality _ _ _ _ i f

end

end SimplicialCategory

end specialization

noncomputable section

variable (K : Type u) [Category.{v} K]

namespace SimplicialCategory

variable [SimplicialCategory K] {K}

def coneNatTrans {A : SSet} {AX X : K} (Y : K) (cone : A ⟶ sHom AX X) :
    sHom Y AX ⟶ (ihom A).obj (sHom Y X) :=
  MonoidalClosed.curry ((braiding A (sHom Y AX)).hom ≫ (sHom Y AX ◁ cone) ≫ sHomComp Y AX X)

structure IsCotensor {A : SSet} {X : K} (AX : K) (cone : A ⟶ sHom AX X) where
  uniq : ∀ (Y : K), IsIso (coneNatTrans Y cone)

structure CotensorCone (A : SSet) (X : K) where
  /-- The object -/
  obj : K
  /-- The cone itself -/
  cone : A ⟶ sHom obj X
  /-- The universal property of the limit cone -/
  is_cotensor : IsCotensor obj cone

end SimplicialCategory

end

end CategoryTheory
