import Architect
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

open CategoryTheory

attribute [blueprint
  "defn:underlying-cat"
  (statement := /--
  The category $\cA_0$ of 0-arrows is the \textbf{underlying category} of the simplicial category
  $\cA$, which forgets the higher dimensional simplicial structure.
  -/)]
  categoryForgetEnrichment

attribute [blueprint
  "defn:lax-monoidal-functor"
  (statement := /--
   A \textbf{(lax) monoidal functor} between cartesian closed categories $\cV$ and $\cW$ is a
   functor $T \colon \cV \to \cW$ equipped with natural transformations
  \begin{center}
  \begin{tikzcd} \cV \times \cV \arrow[r, "T\times T"] \arrow[dr, phantom,
  "\scriptstyle\Downarrow\phi"] \arrow[d, "\times"'] & \cW \times \cW \arrow[d, "\times"] & \catone
  \arrow[r, "1"] \arrow[dr, "1"'] & \cV \arrow[d, "T"] \\ \cV \arrow[r, "T"'] & \cW  &\arrow[ur,
  phantom, "\scriptstyle\Uparrow\phi_0" pos=.85] & \cW
  \end{tikzcd}
  \end{center}
  so that the evident associativity and unit diagrams commute.
  -/)]
  LaxMonoidalFunctor

attribute [blueprint
  "prop:change-of-base"
  (statement := /--
  A finite-product-preserving functor $T \colon \cV \to \cW$ between cartesian closed categories
  induces a change-of-base 2-functor \begin{center} \begin{tikzcd} {\cV}\text{-}\mathcal{C}at
  \arrow[r, "T_*"] & {\cW}\text{-}\mathcal{C}at\, . \end{tikzcd}\end{center}
  -/)
  (proof := /--
      Let $\cC$ be a $\cV$-category and define a $\cW$-category $T_*\cC$ to have the same objects
      and to have mapping objects $T_*\cC(x,y) \coloneq T\cC(x,y)$. The composition and identity
      maps are given by the composites
  \begin{center}
  \begin{tikzcd}[column sep=small] T\cC(y,z)\times T\cC(x,y) \arrow[r, "\cong"] & T(\cC(y,z) \times
  \cC(x,y)) \arrow[r, "T\circ"] & T\cC(x,z) & 1 \arrow[r, "\cong"] & T1 \arrow[r, "T\id_x"] &
  T\cC(x,x)
  \end{tikzcd}
  \end{center}
  which make use of the inverses of the natural maps that arise when a finite-product-preserving
  functor is applied to a finite product. A straightforward diagram chase verifies that $T_*\cC$ is
  a $\cW$-category.

  If $F \colon \cC \to \cD$ is a $\cV$-functor, then we define a $\cW$-functor $T_*F \colon T_*\cC
  \to T_*\cD$ to act on objects by $c \in\cC \mapsto Fc \in \cD$ and with internal action on arrows
  defined by
  \begin{center} \begin{tikzcd} T\cC(x,y) \arrow[r, "TF_{x,y}"] & T\cD(Fx,Fy) \end{tikzcd}
  \end{center}
  Again, a straightforward diagram chase verifies that $T_*F$ is $\cW$-functorial. It is evident
  from this definition that $T_*(GF) = T_*G \cdot T_*F$.

  Finally, let $\alpha \colon F \To G$ be a $\cV$-natural transformation between $\cV$-functors $F,G
  \colon \cC\to \cD$ and define a $\cW$-natural transformation $T_*\alpha \colon T_* F \To T_*G$ to
  have components
  \begin{center}
  \begin{tikzcd} 1 \arrow[r, "\cong"] & T1 \arrow[r, "T\alpha_c"] & T\cD(Fc, Gc)\end{tikzcd}
  \end{center}
  Another straightforward diagram chase verifies that $T_*\alpha$ is $\cW$-natural.

  It remains to verify this assignment is functorial for both horizontal and vertical composition of
  enriched natural transformations. %Consulting Definition \ref{defn:V-cat-2-cat}, we see that
  The component of $T_*(\beta\cdot\alpha)$ is defined by the top-horizontal composite below while
  the component of the vertical composite of $T_*\alpha$ with $T_*\beta \colon T_*G \To T_*H$ is
  defined by the bottom composite: \begin{center}
  \begin{tikzcd} 1 \arrow[r, "\cong"] \arrow[dr, "\cong"'] & T1 \arrow[r, "T(\beta_c\times
  \alpha_c)"] & T(\cD(Gc, Hc) \times \cD(Fc, Gc)) \arrow[r, "T\circ"] & T\cD(Fc,Hc) \\ & T1 \times
  T1 \arrow[u, "\cong"'] \arrow[r, "T\beta_c \times T\alpha_c"'] & T\cD(Gc,Hc) \times T\cD(Fc,Gc)
  \arrow[u, "\cong"']  \end{tikzcd}
  \end{center}
  The square commutates by the naturality of the isomorphism $T(u \times v) \cong Tu \times Tv$,
  while the triangle commutes because 1 is terminal, so the inverses of the displayed isomorphisms
  form a commutative triangle. The argument for functoriality of horizontal composites is similar.
  -/)
  (latexEnv := "proposition")]
  instEnrichedCategoryTransportEnrichment

noncomputable
section

open Limits MonoidalCategory MonoidalClosed BraidedCategory

variable {V : Type} [Category V] [MonoidalCategory V] [BraidedCategory V] [HasLimits V]
variable {C : Type} [EnrichedCategory V C]
variable {D : Type} [EnrichedCategory V D]

variable (F G : EnrichedFunctor V C D)

namespace enrichedNatTransObj

/- TODO: Upstream the @[ext] annotation -/
@[ext]
structure EnrichedNatTrans (F G : EnrichedFunctor V C D) where
  /-- The underlying natural transformation of an enriched transformation. -/
  out : F.forget ⟶ G.forget

def equalizerDom : V :=
  ∏ᶜ fun (X : C) ↦ F.obj X ⟶[V] G.obj X

def equalizerCodom : V :=
  ∏ᶜ fun (⟨X, Y, _⟩ : Σ (X : C) (Y : C), 𝟙_ V ⟶ X ⟶[V] Y) ↦ F.obj X ⟶[V] G.obj Y

def equalizerArrow₁ : equalizerDom F G ⟶ equalizerCodom F G :=
  Pi.lift (fun ⟨X, Y, f⟩ ↦
    (λ_ _).inv ≫
    (f ≫ F.map X Y ⊗ₘ Pi.π _ Y) ≫
    eComp _ _ (F.obj Y) _)

def equalizer_arrow₂ : equalizerDom F G ⟶ equalizerCodom F G :=
  Pi.lift (fun ⟨X, Y, f⟩ ↦
    (ρ_ _).inv ≫
    (Pi.π _ X ⊗ₘ f ≫ G.map X Y) ≫
    eComp _ _ (G.obj X) _)

def _root_.enrichedNatTransObj : V := equalizer (equalizerArrow₁ F G) (equalizer_arrow₂ F G)

def toFun.out (f : 𝟙_ V ⟶ enrichedNatTransObj F G) : F.forget ⟶ G.forget where
  app X₀ := by
    dsimp;
    exact ForgetEnrichment.homOf V (f ≫ equalizer.ι _ _ ≫ Pi.π _ (ForgetEnrichment.to _ X₀))
  naturality X₀ Y₀ g₀ := by
    dsimp
    rw [← ForgetEnrichment.homOf_comp, ← ForgetEnrichment.homOf_comp]
    apply congr_arg
    nth_rw 2 [unitors_inv_equal]
    rw [← whiskerLeft_comp_tensorHom_assoc _ f, ← whiskerRight_comp_tensorHom_assoc f]
    rw [← leftUnitor_inv_naturality_assoc, ← rightUnitor_inv_naturality_assoc]
    apply congr_arg
    rw [← whiskerLeft_comp_tensorHom_assoc, ← whiskerRight_comp_tensorHom_assoc (equalizer.ι _ _)]
    rw [← leftUnitor_inv_naturality_assoc, ← rightUnitor_inv_naturality_assoc]
    have H : equalizer.ι _ _ ≫ Pi.lift _ = equalizer.ι _ _ ≫ Pi.lift _ :=
      equalizer.condition (equalizerArrow₁ F G) (equalizer_arrow₂ F G)
    rw [Pi.hom_ext_iff] at H
    specialize H ⟨ForgetEnrichment.to _ X₀, ForgetEnrichment.to _ Y₀, ForgetEnrichment.homTo _ g₀⟩
    rw [Category.assoc, Category.assoc] at H
    rw [Pi.lift_π, Pi.lift_π] at H
    dsimp at H
    exact H

def toFun (f : 𝟙_ V ⟶ enrichedNatTransObj F G) : EnrichedNatTrans F G := .mk (toFun.out F G f)

def invFun (α : EnrichedNatTrans F G) :
    𝟙_ V ⟶ enrichedNatTransObj F G := by
  apply equalizer.lift _ _
  · apply Pi.lift
    intro X
    apply ForgetEnrichment.homTo
    exact α.out.app (ForgetEnrichment.of _ X)
  · dsimp [equalizerArrow₁, equalizer_arrow₂]
    apply Pi.hom_ext
    rintro ⟨X, Y, f⟩
    rw [Category.assoc, Category.assoc]
    rw [Pi.lift_π, Pi.lift_π]
    dsimp
    rw [leftUnitor_inv_naturality_assoc, rightUnitor_inv_naturality_assoc]
    rw [whiskerLeft_comp_tensorHom_assoc, whiskerRight_comp_tensorHom_assoc]
    rw [Pi.lift_π, Pi.lift_π]
    rw [← unitors_inv_equal]
    rw [← ForgetEnrichment.homTo_homOf _ (f ≫ F.map X Y),
      ← ForgetEnrichment.homTo_homOf _ (f ≫ G.map X Y)]
    rw [← Category.assoc, ← Category.assoc]
    apply Eq.trans (ForgetEnrichment.homTo_comp _ _ _).symm
    apply Eq.trans _ (ForgetEnrichment.homTo_comp _ _ _)
    apply congr_arg
    exact α.out.naturality (ForgetEnrichment.homOf _ f)

def globalElementsEquivalence :
    (𝟙_ V ⟶ enrichedNatTransObj F G) ≃ EnrichedNatTrans F G where
  toFun := toFun F G
  invFun := invFun F G
  left_inv f := by
    apply equalizer.hom_ext
    dsimp [toFun, toFun.out, invFun]
    rw [equalizer.lift_ι]
    apply Pi.hom_ext
    intro Y
    rw [Category.assoc f]
    rw [Pi.lift_π]
  right_inv f := by
    ext X₀
    dsimp [toFun, toFun.out, invFun]
    rw [equalizer.lift_ι_assoc]
    rw [Pi.lift_π]
    apply ForgetEnrichment.homOf_homTo

end enrichedNatTransObj

namespace gradedNatTransObj

variable [MonoidalClosed V]

def equalizerDom : V :=
  ∏ᶜ fun (X : C) ↦ F.obj X ⟶[V] G.obj X

def equalizerCodom : V :=
  ∏ᶜ fun (⟨X, Y⟩ : C × C) ↦ (ihom (X ⟶[V] Y)).obj (F.obj X ⟶[V] G.obj Y)

def equalizerArrow₁ : equalizerDom F G ⟶ equalizerCodom F G :=
  Pi.lift (fun ⟨X, Y⟩ ↦
    Pi.π _ Y ≫
    curry (
      (F.map X Y ▷ _) ≫
      eComp _ (F.obj X) (F.obj Y) (G.obj Y)))

def equalizerArrow₂ : equalizerDom F G ⟶ equalizerCodom F G :=
  Pi.lift (fun ⟨X, Y⟩ ↦
    Pi.π _ X ≫
    curry (
      (β_ _ _ ).hom ≫
      (_ ◁ G.map X Y) ≫
      eComp _ (F.obj X) (G.obj X) (G.obj Y)))

def _root_.gradedNatTransObj : V := equalizer (equalizerArrow₁ F G) (equalizerArrow₂ F G)

def invFun (α : GradedNatTrans (Center.tensorUnit) F G) :
    𝟙_ V ⟶ gradedNatTransObj F G := by
  apply equalizer.lift _ _
  · apply Pi.lift
    intro X
    exact α.app X
  · dsimp [equalizerArrow₁, equalizerArrow₂]
    apply Pi.hom_ext
    rintro ⟨X, Y⟩
    rw [Category.assoc, Category.assoc]
    rw [Pi.lift_π, Pi.lift_π]
    rw [← Category.assoc, ← Category.assoc]
    rw [Pi.lift_π, Pi.lift_π]
    rw [← curry_natural_left, ← curry_natural_left]
    apply congr_arg
    rw [BraidedCategory.braiding_naturality_right_assoc]
    rw [← Iso.inv_comp_eq]
    rw [← tensorHom_def'_assoc, ← tensorHom_def_assoc]
    rw [braiding_inv_tensorUnit_right]
    exact α.naturality X Y

def toFun (f : 𝟙_ V ⟶ gradedNatTransObj F G) :
    GradedNatTrans (Center.tensorUnit) F G where
  app X := f ≫ equalizer.ι _ _ ≫ Pi.π _ X
  naturality X Y := by
    dsimp
    /- Turn the LHS half braids into braiding on the RHS. -/
    rw [← braiding_inv_tensorUnit_right]
    rw [Iso.inv_comp_eq]
    /- Factor out f from both sides and remove it from the goal. -/
    rw [tensorHom_def'_assoc (F.map X Y), tensorHom_def_assoc _ (G.map X Y)]
    rw [whiskerLeft_comp_assoc, comp_whiskerRight_assoc]
    rw [← braiding_naturality_right_assoc (X ⟶[V] Y) f]
    apply congr_arg
    /- Introduce currying and expel the left whiskers from the curried term. -/
    apply curry_injective
    rw [← braiding_naturality_right_assoc]
    rw [whiskerLeft_comp_assoc, whiskerLeft_comp_assoc]
    repeat rw [curry_natural_left]
    /- Use the universal property of the equalizer, specialized to one factor of the codomain. -/
    have H : equalizer.ι _ _ ≫ Pi.lift _ = equalizer.ι _ _ ≫ Pi.lift _ :=
      equalizer.condition (equalizerArrow₁ F G) (equalizerArrow₂ F G)
    rw [Pi.hom_ext_iff] at H
    specialize H ⟨X, Y⟩
    rw [Category.assoc, Category.assoc] at H
    rw [Pi.lift_π, Pi.lift_π] at H
    exact H

  def globalElementsEquivalence :
      (𝟙_ V ⟶ gradedNatTransObj F G) ≃ (GradedNatTrans (Center.tensorUnit) F G) where
    toFun := toFun F G
    invFun := invFun F G
    left_inv f := by
      apply equalizer.hom_ext
      dsimp [toFun, invFun]
      rw [equalizer.lift_ι]
      apply Pi.hom_ext
      intro Y
      rw [Category.assoc]
      rw [Pi.lift_π]
    right_inv f := by
      ext X
      dsimp [toFun, invFun]
      rw [equalizer.lift_ι_assoc]
      apply Pi.lift_π

end gradedNatTransObj

end
