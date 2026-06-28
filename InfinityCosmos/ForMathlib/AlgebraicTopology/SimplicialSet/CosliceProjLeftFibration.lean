import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.FibrationConservative
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CosliceUnder
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.JoyalLeftAnodyneJoinMono
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeibnizJoinCore
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# The coslice projection is a left fibration, and the conservative θ-layer

Feeds the Joyal pushout-product (`joyal_leftAnodyne_join_mono`) through the coslice projection to
obtain the structural facts behind the `i = last` special-outer-horn filler. Shows the coslice
projection is a left fibration (`leftFibration_cosliceProj`) and that the coslice of a
quasicategory is again a quasicategory (`quasicategory_cosliceUnder`); records that a left
fibration of quasicategories is an isofibration on its base (`leftFibration_isofibration_target`);
and builds the relative projection `thetaMap` with its left-fibration and conservativity facts
(`leftFibration_thetaMap`, `thetaMap_conservative`). Conservativity rests on the iso-edge
2-out-of-3 for quasicategories.
-/

section
open CategoryTheory Simplicial
universe u
namespace SSet
variable {X S : SSet.{u}}

/-- Strict TARGET-vertex isofibration lift for a LEFT fibration.  Given the TARGET vertex
`x₁` of an invertible base edge `e : Edge s₀ (ρ x₁)`, produce a strict invertible lift
`e' : Edge x₀ x₁` with `ρ(e') = e` on the nose.  Dual orientation to
`leftFibration_isofibration`, with NO right fibration needed: lift `e⁻¹` from its source `x₁`,
then close the `Λ²₀` filler against the identity with `m := e`, which forces strictness. -/
theorem leftFibration_isofibration_target {ρ : X ⟶ S} [Quasicategory X] [LeftFibration ρ]
    {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌} (e : Edge s₀ (ρ.app _ x₁)) (he : Nonempty e.IsIso) :
    ∃ (x₀ : X _⦋0⦌) (e' : Edge x₀ x₁),
      ρ.app _ x₀ = s₀ ∧ (e'.map ρ).edge = e.edge ∧ Nonempty e'.IsIso := by
  obtain ⟨he⟩ := he
  obtain ⟨xₘ, ee, hxₘ, hee⟩ :=
    leftLiftEdgeOfLeftFibration (p := ρ) (x₀ := x₁) (s₁ := s₀) he.inv
  let m : Edge (ρ.app _ xₘ) (ρ.app _ x₁) := e.ofEq hxₘ.symm rfl
  have hmedge : m.edge = e.edge := rfl
  have cs : Edge.CompStruct (ee.map ρ) m ((Edge.id x₁).map ρ) :=
    he.invHomId.ofEq hee.symm hmedge.symm (Edge.ext_iff.mp (Edge.map_id x₁ ρ)).symm
  obtain ⟨k, _, hk⟩ := leftFillTwoZeroOfLeftFibration ee (Edge.id x₁) cs
  refine ⟨xₘ, k, hxₘ, hk.trans hmedge, ?_⟩
  exact leftFibration_conservative k ⟨he.ofEq (hk.trans hmedge).symm⟩

end SSet
end

section
open CategoryTheory Simplicial MorphismProperty Limits
namespace SSet
universe u
noncomputable section

/-! ## Discharge the `joyal` hypothesis (Joyal pushout-product + corner iso) -/

/-- The Joyal pushout-product hypothesis required by `leftFibrations_cosliceProj`, supplied for a
monomorphism `jST` from `joyal_leftAnodyne_join_mono` and the corner isomorphism. -/
theorem joyal_discharge {S T : SSet.{u}} (jST : S ⟶ T) (hjST : Mono jST) :
    ∀ ⦃A B : SSet.{u}⦄ (g : A ⟶ B), leftAnodyneExtensions g →
        innerAnodyneExtensions (sqLeibCo jST g).ι := by
  intro A B g hg
  exact (innerAnodyneExtensions.arrow_mk_iso_iff (cornerIso jST g)).1
    (joyal_leftAnodyne_join_mono jST hjST g hg)

/-! ## `cosliceProj` is unconditionally a LEFT (hence inner) fibration -/

/-- For a monomorphism `jST` and an inner fibration `p`, the coslice projection
`cosliceProj jST σ p` is a left fibration. -/
instance leftFibration_cosliceProj {S T X Y : SSet.{u}} (jST : S ⟶ T) [hj : Mono jST]
    (σ : T ⟶ X) (p : X ⟶ Y) [InnerFibration p] :
    LeftFibration (cosliceProj jST σ p) :=
  ⟨leftFibrations_cosliceProj jST σ p (joyal_discharge jST hj)⟩

/-! ## The fiber product `E` -/

/-- The fiber product `E = C_{f0/} ×_{D_{(qf0)/}} D_{(qf)/}` (codomain of `cosliceProj`). -/
abbrev fiberProductE {S T X Y : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ X) (p : X ⟶ Y) : SSet.{u} :=
  pullback (cosliceMapTarget (p := jST ≫ σ) p)
    (cosliceMapBase jST (rfl : jST ≫ (σ ≫ p) = jST ≫ (σ ≫ p)))

end
end SSet
end

section
/-!
# Gateway: coslice quasicategory wrappers

`cosliceUnder` over a terminal target is terminal; `cosliceUnder (⊥→C) ≅ C`; and the
domain of `cosliceProj` over a quasicategory is a quasicategory.
-/

open CategoryTheory MonoidalCategory Simplicial Opposite Limits
namespace SSet
universe u
noncomputable section

/-! ## `cosliceUnder` over a terminal target is terminal -/

/-- The canonical map `Y ⟶ cosliceUnder g` into the coslice over a point. -/
def coTerminalHom {K : SSet.{u}} (g : K ⟶ (Δ[0] : SSet.{u})) (Y : SSet.{u}) :
    Y ⟶ cosliceUnder g where
  app n := ↾fun _ =>
    (⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩ :
      CoOverPt g (stdSimplex.obj n.unop))
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The coslice `cosliceUnder g` over a point is a terminal simplicial set. -/
def cosliceUnder_isTerminal {K : SSet.{u}} (g : K ⟶ (Δ[0] : SSet.{u})) :
    IsTerminal (cosliceUnder g) :=
  IsTerminal.ofUniqueHom (coTerminalHom g) (by
    intro Y m
    apply (cancel_epi (𝟙 Y)).mp
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    exact stdSimplex.isTerminalObj₀.hom_ext _ _)

/-! ## `cosliceUnder (⊥→C) ≅ C` -/

@[reassoc]
theorem joinInr_naturality_right (X : SSet.{u}) {Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    joinInr X Y ≫ (joinFunctor.obj X).map g = g ≫ joinInr X Y' := by
  change
    restrictAugmentedDay.map
          ((λ_ (augmentedDay.obj Y)).inv ≫ (augmentedDayUnitTo X) ▷ (augmentedDay.obj Y)) ≫
        restrictAugmentedDay.map ((augmentedDay.obj X) ◁ (augmentedDay.map g)) =
      restrictAugmentedDay.map (augmentedDay.map g) ≫
        restrictAugmentedDay.map
          ((λ_ (augmentedDay.obj Y')).inv ≫ (augmentedDayUnitTo X) ▷ (augmentedDay.obj Y'))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Category.assoc, ← whisker_exchange, ← Category.assoc, ← leftUnitor_inv_naturality,
    Category.assoc]

/-- Componentwise: `n`-simplices of `cosliceUnder (h : ⊥→C)` are `n`-simplices of `C`. -/
def botCoOverPtEquiv {C : SSet.{u}} (h : (⊥_ SSet.{u}) ⟶ C) (n : SimplexCategoryᵒᵖ) :
    CoOverPt h (stdSimplex.obj n.unop) ≃ C.obj n where
  toFun q := yonedaEquiv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop) ≫ q.1)
  invFun c :=
    ⟨(joinBotIso (stdSimplex.obj n.unop)).hom ≫ yonedaEquiv.symm c, initial.hom_ext _ _⟩
  left_inv q := by
    apply Subtype.ext
    show (joinBotIso (stdSimplex.obj n.unop)).hom ≫
        yonedaEquiv.symm (yonedaEquiv (joinInr _ _ ≫ q.1)) = q.1
    rw [Equiv.symm_apply_apply,
      show (joinBotIso (stdSimplex.obj n.unop)).hom
          = inv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop)) from rfl,
      IsIso.inv_hom_id_assoc]
  right_inv c := by
    show yonedaEquiv (joinInr _ _ ≫
        ((joinBotIso (stdSimplex.obj n.unop)).hom ≫ yonedaEquiv.symm c)) = c
    rw [show (joinBotIso (stdSimplex.obj n.unop)).hom
          = inv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop)) from rfl,
      ← Category.assoc, IsIso.hom_inv_id, Category.id_comp, Equiv.apply_symm_apply]

/-- `cosliceUnder (h : ⊥→C) ≅ C` for any `h` from the initial object. -/
def cosliceUnderBotIso {C : SSet.{u}} (h : (⊥_ SSet.{u}) ⟶ C) : cosliceUnder h ≅ C :=
  NatIso.ofComponents (fun n => Equiv.toIso (botCoOverPtEquiv h n)) (by
    intro n m f
    ext q
    show yonedaEquiv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj m.unop) ≫
        (joinFunctor.obj (⊥_ SSet.{u})).map (stdSimplex.map f.unop) ≫ q.1)
      = C.map f (yonedaEquiv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop) ≫ q.1))
    have hnat : C.map f (yonedaEquiv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop) ≫ q.1))
        = yonedaEquiv (stdSimplex.map f.unop ≫
            joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop) ≫ q.1) := by
      have hh := yonedaEquiv_symm_naturality (X := C) f.unop
        (yonedaEquiv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop) ≫ q.1))
      rw [Equiv.symm_apply_apply, Quiver.Hom.op_unop] at hh
      apply yonedaEquiv.symm.injective
      rw [Equiv.symm_apply_apply, hh]
    rw [hnat]
    congr 1
    rw [← Category.assoc, joinInr_naturality_right]
    exact Category.assoc _ _ _)

/-! ## `Quasicategory (cosliceUnder σ)` -/

instance innerFibration_of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] : InnerFibration f :=
  ⟨MorphismProperty.of_isIso innerFibrations f⟩

/-- The coslice of a quasicategory under a simplex is a quasicategory. -/
instance quasicategory_cosliceUnder {T C : SSet.{u}} (σ : T ⟶ C) [Quasicategory C] :
    Quasicategory (cosliceUnder σ) := by
  set q0 : C ⟶ (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.from C with hq0def
  haveI hq0 : InnerFibration q0 :=
    (quasicategory_iff_of_isTerminal q0 stdSimplex.isTerminalObj₀).mp inferInstance
  haveI : Mono (initial.to T) := inferInstance
  -- the two legs of the fiber product (named exactly as in `cosliceProj`'s codomain)
  set f₁ : cosliceUnder (initial.to T ≫ σ) ⟶ cosliceUnder ((initial.to T ≫ σ) ≫ q0) :=
    cosliceMapTarget (p := initial.to T ≫ σ) q0 with hf₁def
  set f₂ : cosliceUnder (σ ≫ q0) ⟶ cosliceUnder ((initial.to T ≫ σ) ≫ q0) :=
    cosliceMapBase (initial.to T) rfl with hf₂def
  -- `f₂` is an iso between terminal coslices
  haveI hf₂ : IsIso f₂ :=
    ⟨(cosliceUnder_isTerminal (σ ≫ q0)).from _,
      (cosliceUnder_isTerminal (σ ≫ q0)).hom_ext _ _,
      (cosliceUnder_isTerminal ((initial.to T ≫ σ) ≫ q0)).hom_ext _ _⟩
  haveI : IsIso (pullback.fst f₁ f₂) := pullback_fst_iso_of_right_iso f₁ f₂
  -- the `fst` leg lands in `cosliceUnder (⊥→C) ≅ C`, hence a quasicategory
  haveI : Quasicategory (cosliceUnder (initial.to T ≫ σ)) :=
    quasicategory_of_innerFibration (cosliceUnderBotIso (initial.to T ≫ σ)).hom
  haveI hPq : Quasicategory (pullback f₁ f₂) :=
    quasicategory_of_innerFibration (asIso (pullback.fst f₁ f₂)).hom
  haveI : InnerFibration (cosliceProj (initial.to T) σ q0) := inferInstance
  exact quasicategory_of_innerFibration (Y := pullback f₁ f₂) (cosliceProj (initial.to T) σ q0)

end
end SSet
end

section
/-!
# The θ layer: absolute coslice projection, θ, conservativity
-/

open CategoryTheory Simplicial Opposite Limits MorphismProperty
namespace SSet
universe u
noncomputable section

/-- `cosliceMapBase jST` (cone restriction along a mono) is a left fibration:
it equals `cosliceProj jST pT (C→Δ[0]) ≫ (iso)`. -/
theorem leftFibration_cosliceMapBase {S T C : SSet.{u}} (jST : S ⟶ T) [Mono jST]
    (pT : T ⟶ C) [Quasicategory C] :
    LeftFibration (cosliceMapBase jST (rfl : jST ≫ pT = jST ≫ pT)) := by
  set q0 : C ⟶ (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.from C with hq0def
  haveI : InnerFibration q0 :=
    (quasicategory_iff_of_isTerminal q0 stdSimplex.isTerminalObj₀).mp inferInstance
  set h1 : cosliceUnder (jST ≫ pT) ⟶ cosliceUnder ((jST ≫ pT) ≫ q0) :=
    cosliceMapTarget (p := jST ≫ pT) q0 with hh1def
  set h2 : cosliceUnder (pT ≫ q0) ⟶ cosliceUnder ((jST ≫ pT) ≫ q0) :=
    cosliceMapBase jST rfl with hh2def
  haveI : IsIso h2 :=
    ⟨(cosliceUnder_isTerminal (pT ≫ q0)).from _,
      (cosliceUnder_isTerminal (pT ≫ q0)).hom_ext _ _,
      (cosliceUnder_isTerminal ((jST ≫ pT) ≫ q0)).hom_ext _ _⟩
  haveI : IsIso (pullback.fst h1 h2) := pullback_fst_iso_of_right_iso h1 h2
  refine ⟨?_⟩
  rw [← cosliceProj_fst jST pT q0]
  exact leftFibrations.comp_mem _ _ (mem_leftFibrations _) (MorphismProperty.of_isIso _ _)

/-- The absolute coslice projection `C_{p/} → C`:
`cosliceMapBase (⊥→K) ≫ (cosliceUnder(⊥→C) ≅ C)`. -/
def cosliceAbsProj {K C : SSet.{u}} (p : K ⟶ C) : cosliceUnder p ⟶ C :=
  cosliceMapBase (initial.to K) (rfl : initial.to K ≫ p = initial.to K ≫ p) ≫
    (cosliceUnderBotIso (initial.to K ≫ p)).hom

instance leftFibration_cosliceAbsProj {K C : SSet.{u}} (p : K ⟶ C) [Quasicategory C] :
    LeftFibration (cosliceAbsProj p) := by
  haveI : LeftFibration
      (cosliceMapBase (initial.to K) (rfl : initial.to K ≫ p = initial.to K ≫ p)) :=
    leftFibration_cosliceMapBase (initial.to K) p
  refine ⟨leftFibrations.comp_mem _ _ (mem_leftFibrations _) (MorphismProperty.of_isIso _ _)⟩

/-! ## `θ : E → C` and `Quasicategory E` -/

/-- `θ : E → C := pullback.fst ≫ absProj`. -/
def thetaMap {S T C D : SSet.{u}} (jST : S ⟶ T) (σ : T ⟶ C) (q : C ⟶ D) :
    fiberProductE jST σ q ⟶ C :=
  pullback.fst _ _ ≫ cosliceAbsProj (jST ≫ σ)

/-- The relative coslice projection `θ` is a left fibration. -/
instance leftFibration_thetaMap {S T C D : SSet.{u}} (jST : S ⟶ T) [Mono jST]
    (σ : T ⟶ C) (q : C ⟶ D) [Quasicategory C] [Quasicategory D] [InnerFibration q] :
    LeftFibration (thetaMap jST σ q) := by
  set h1 : cosliceUnder (jST ≫ σ) ⟶ cosliceUnder ((jST ≫ σ) ≫ q) :=
    cosliceMapTarget (p := jST ≫ σ) q with hh1def
  set h2 : cosliceUnder (σ ≫ q) ⟶ cosliceUnder ((jST ≫ σ) ≫ q) :=
    cosliceMapBase jST rfl with hh2def
  haveI hh2lf : LeftFibration h2 := leftFibration_cosliceMapBase jST (σ ≫ q)
  haveI hfst : LeftFibration (pullback.fst h1 h2) :=
    ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback h1 h2).flip
      (mem_leftFibrations h2)⟩
  refine ⟨?_⟩
  show leftFibrations (pullback.fst h1 h2 ≫ cosliceAbsProj (jST ≫ σ))
  exact leftFibrations.comp_mem _ _ (mem_leftFibrations _) (mem_leftFibrations _)

instance quasicategory_fiberProductE {S T C D : SSet.{u}} (jST : S ⟶ T) [Mono jST]
    (σ : T ⟶ C) (q : C ⟶ D) [Quasicategory C] [Quasicategory D] [InnerFibration q] :
    Quasicategory (fiberProductE jST σ q) := by
  haveI := leftFibration_thetaMap jST σ q
  exact quasicategory_of_innerFibration (thetaMap jST σ q)

/-- `θ` reflects invertibility: if `θ(v)` is invertible in `C`, so is `v` in `E`. -/
theorem thetaMap_conservative {S T C D : SSet.{u}} (jST : S ⟶ T) [Mono jST]
    (σ : T ⟶ C) (q : C ⟶ D) [Quasicategory C] [Quasicategory D] [InnerFibration q]
    {x₀ x₁ : (fiberProductE jST σ q) _⦋0⦌} (v : Edge x₀ x₁)
    (hv : Nonempty (v.map (thetaMap jST σ q)).IsIso) :
    Nonempty v.IsIso := by
  haveI := leftFibration_thetaMap jST σ q
  exact leftFibration_conservative v hv

end
end SSet
end
