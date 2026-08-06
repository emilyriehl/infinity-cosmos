module

/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

public import Architect
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
public import InfinityCosmos.ForMathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Batteries.Tactic.Lint.Misc
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

@[expose] public section


universe u v w

namespace SSet

open CategoryTheory Simplicial SimplicialCategory Limits

/-- An interval is a simplicial set equipped with two endpoints.-/
class Interval (I : SSet.{u}) : Type u where
  src : Δ[0] ⟶ I
  tgt : Δ[0] ⟶ I

/-- The interval relevant to the theory of Kan complexes.-/
instance arrowInterval : Interval Δ[1] where
  src := stdSimplex.δ (n := 0) (1)
  tgt := stdSimplex.δ (n := 0) (0)

/-- The interval relevant to the theory of quasi-categories. -/
instance isoInterval : Interval coherentIso where
  src := yonedaEquiv.symm (coherentIso.x₀)
  tgt := yonedaEquiv.symm (coherentIso.x₁)

open MonoidalCategory
noncomputable def pointIsUnit : Δ[0] ≅ (𝟙_ SSet) :=
  IsTerminal.uniqueUpToIso isTerminalDeltaZero (IsTerminal.ofUnique (𝟙_ SSet))

noncomputable def expUnitNatIso : ihom (𝟙_ SSet) ≅ 𝟭 SSet :=
  (conjugateIsoEquiv (Adjunction.id (C := SSet)) (ihom.adjunction _)
    (leftUnitorNatIso _)).symm

noncomputable def expPointNatIso : ihom Δ[0] ≅ 𝟭 SSet := by
  refine ?_ ≪≫ expUnitNatIso
  exact {
    hom := MonoidalClosed.pre pointIsUnit.inv
    inv := MonoidalClosed.pre pointIsUnit.hom
    hom_inv_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.hom_inv_id]
      exact MonoidalClosed.pre_id _
    inv_hom_id := by
      rw [← MonoidalClosed.pre_map, pointIsUnit.inv_hom_id]
      exact MonoidalClosed.pre_id _
  }

noncomputable def expPointIsoSelf (X : SSet) : sHom Δ[0] X ≅ X := expPointNatIso.app X

/-- Evaluating a curried map out of `Δ[0]` agrees with precomposition by the canonical
`A ⟶ Δ[0] ⊗ A`. -/
lemma curry_expPointIsoSelf_hom {A B : SSet.{u}} (H : Δ[0] ⊗ A ⟶ B) :
    MonoidalClosed.curry H ≫ B.expPointIsoSelf.hom =
      (λ_ A).inv ≫ (SSet.pointIsUnit.inv ▷ A) ≫ H := by
  change MonoidalClosed.curry H ≫
      ((MonoidalClosed.pre SSet.pointIsUnit.inv).app B ≫
        (MonoidalClosed.unitIsoSelf (C := SSet.{u}) (X := B)).hom) =
      (λ_ A).inv ≫ (SSet.pointIsUnit.inv ▷ A) ≫ H
  slice_lhs 1 2 => rw [MonoidalClosed.curry_pre_app]
  exact MonoidalClosed.curry_unitIsoSelf_hom ((SSet.pointIsUnit.inv ▷ A) ≫ H)

/-- Evaluating a curried cylinder `I ⊗ A ⟶ B` at a chosen endpoint of `I` is precomposition by
that endpoint. This is what turns the endpoint conditions on an uncurried homotopy into the
`source_eq` and `target_eq` fields of a `Homotopy`. -/
lemma curry_endpoint_eval {I A B : SSet.{u}} (endpoint : Δ[0] ⟶ I) (H : I ⊗ A ⟶ B) :
    MonoidalClosed.curry H ≫ (MonoidalClosed.pre endpoint).app B ≫ B.expPointIsoSelf.hom =
      (λ_ A).inv ≫ (SSet.pointIsUnit.inv ≫ endpoint) ▷ A ≫ H := by
  rw [← Category.assoc]
  slice_lhs 1 2 => rw [MonoidalClosed.curry_pre_app]
  rw [curry_expPointIsoSelf_hom]
  rw [MonoidalCategory.comp_whiskerRight]
  rfl

section

variable {I : SSet.{u}} [Interval I]

@[nolint unusedArguments]
noncomputable def pathSpace {I : SSet.{u}} [Interval I] (X : SSet.{u}) : SSet.{u} := sHom I X

open MonoidalClosed

noncomputable def pathSpace.src (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.src).app X ≫ X.expPointIsoSelf.hom)

noncomputable def pathSpace.tgt (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.tgt).app X ≫ X.expPointIsoSelf.hom)


/-- TODO: Figure out how to allow `I` to be an a different universe from `A` and `B`?-/
structure Homotopy {A B : SSet.{u}} (f g : A ⟶ B) : Type u
    where
  homotopy : A ⟶ sHom I B
  source_eq : homotopy ≫ pathSpace.src B = f
  target_eq : homotopy ≫ pathSpace.tgt B = g

/-- The unique map to the point, obtained from the terminal object of `SSet`. -/
noncomputable def toPoint (X : SSet.{u}) : X ⟶ Δ[0] :=
  CartesianMonoidalCategory.toUnit X ≫ pointIsUnit.inv

@[simp]
lemma comp_toPoint {X : SSet.{u}} (f : Δ[0] ⟶ X) : f ≫ toPoint X = 𝟙 Δ[0] := by
  rw [toPoint, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (f ≫ CartesianMonoidalCategory.toUnit X)
      pointIsUnit.hom, pointIsUnit.hom_inv_id]

/-- The constant path on an object: the image of a point under the map that ignores the
interval coordinate. -/
noncomputable def constPath (B : SSet.{u}) : B ⟶ pathSpace (I := I) B :=
  B.expPointIsoSelf.inv ≫ (MonoidalClosed.pre (toPoint I)).app B

omit [Interval I] in
@[reassoc (attr := simp)]
lemma pre_toPoint_comp_pre (g : Δ[0] ⟶ I) (B : SSet.{u}) :
    (MonoidalClosed.pre (toPoint I)).app B ≫ (MonoidalClosed.pre g).app B = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, comp_toPoint, MonoidalClosed.pre_id,
    NatTrans.id_app]

@[simp]
lemma constPath_comp_src (B : SSet.{u}) :
    constPath (I := I) B ≫ pathSpace.src B = 𝟙 B := by
  rw [constPath, pathSpace.src]
  slice_lhs 2 3 => erw [pre_toPoint_comp_pre]
  erw [Category.id_comp]
  exact B.expPointIsoSelf.inv_hom_id

@[simp]
lemma constPath_comp_tgt (B : SSet.{u}) :
    constPath (I := I) B ≫ pathSpace.tgt B = 𝟙 B := by
  rw [constPath, pathSpace.tgt]
  slice_lhs 2 3 => erw [pre_toPoint_comp_pre]
  erw [Category.id_comp]
  exact B.expPointIsoSelf.inv_hom_id

/-- The constant homotopy from a map to itself. -/
noncomputable def Homotopy.refl {A B : SSet.{u}} (f : A ⟶ B) : Homotopy (I := I) f f where
  homotopy := f ≫ constPath (I := I) B
  source_eq := by
    show (f ≫ constPath (I := I) B) ≫ pathSpace.src (I := I) B = f
    rw [Category.assoc, constPath_comp_src, Category.comp_id]
  target_eq := by
    show (f ≫ constPath (I := I) B) ≫ pathSpace.tgt (I := I) B = f
    rw [Category.assoc, constPath_comp_tgt, Category.comp_id]

/-- For the correct interval, this defines a good notion of equivalences for both Kan complexes and quasi-categories.-/
structure Equiv (A B : SSet.{u}) : Type u where
  toFun : A ⟶ B
  invFun : B ⟶ A
  left_inv : Homotopy (I := I) (toFun ≫ invFun) (𝟙 A)
  right_inv : Homotopy (I := I) (invFun ≫ toFun) (𝟙 B)

end

end SSet

namespace Kan

open SSet Simplicial

attribute [blueprint
  "defn:kan-complex"
  (title := "Kan complex")
  (statement := /--
  A \textbf{Kan complex} is a simplicial set admitting extensions as in \eqref{eq:qcat-defn} along
  all horn inclusions $n \geq 1, 0 \leq k \leq n$.
  -/)]
  KanComplex

/-- Equivalence of Kan Complexes. -/
@[nolint unusedArguments]
def Equiv (A B : SSet.{u}) [KanComplex A] [KanComplex B] :=
    SSet.Equiv (I := Δ[1]) A B

end Kan

namespace QCat

open SSet

/-- Equivalence of quasi-categories. -/
@[nolint unusedArguments, blueprint
  "defn:qcat-equivalence"
  (title := "equivalences of quasi-categories")
  (statement := /--
  w=

    A map $f \colon A \to B$ between quasi-categories is an \textbf{equivalence} if it extends to
    the data of a ``homotopy equivalence'' with the free-living isomorphism $\iso$ serving as the
    interval: that is, if there exist maps $g \colon B \to A$,
    \begin{center}
    \begin{tikzcd} & A & &  & B \\ A \arrow[ur, equals] \arrow[dr, "gf"'] \arrow[r, "\alpha"] &
    A^\iso  \arrow[u, "\ev_0"'] \arrow[d, "\ev_1"] & \text{and} &  B \arrow[dr, equals] \arrow[r,
    "\beta"] \arrow[ur, "fg"] & B^\iso \arrow[u, "\ev_0"'] \arrow[d, "\ev_1"] \\ & A & &  & B
    \end{tikzcd}
    \end{center}
    We write ``$\we$'' to decorate equivalences and $A \simeq B$ to indicate the presence of an
    equivalence $A \we B$.
  -/)]
def Equiv (A B : SSet.{u}) [Quasicategory A] [Quasicategory B] :=
    SSet.Equiv (I := coherentIso) A B

end QCat


namespace SSet
section

open CategoryTheory Simplicial SimplexCategory

variable {A : SSet.{u}} (f g : A _⦋1⦌)

structure HomotopyL where
  simplex : A _⦋2⦌
  δ₀_eq : A.δ 0 simplex = A.σ 0 (A.δ 0 f)
  δ₁_eq : A.δ 1 simplex = g
  δ₂_eq : A.δ 2 simplex = f

structure HomotopyR where
  simplex : A _⦋2⦌
  δ₀_eq : A.δ 0 simplex = f
  δ₁_eq : A.δ 1 simplex = g
  δ₂_eq : A.δ 2 simplex = A.σ 0 (A.δ 1 f)

def HomotopicL : Prop :=
    Nonempty (HomotopyL f g)

def HomotopicR : Prop :=
    Nonempty (HomotopyR f g)

def HomotopyL.refl : HomotopyL f f where
  simplex := A.σ 1 f
  δ₀_eq := by
    change _ = (A.δ 0 ≫ A.σ 0) _
    rw [← A.δ_comp_σ_of_le (by simp)]; simp
  δ₁_eq := by
    change (A.σ 1 ≫ A.δ 1) _ = _
    rw [A.δ_comp_σ_self' (by simp)]; simp
  δ₂_eq := by
    change (A.σ 1 ≫ A.δ 2) _ = _
    rw [A.δ_comp_σ_succ' (by simp)]
    rfl

-- -- need a better name
-- noncomputable def HomotopyL.ofHomotopyLOfHomotopyL {f g h : A _⦋1⦌}
--   (H₁ : HomotopyL f g) (H₂ : HomotopyL f h) :
--     HomotopyL g h := by
--   let σ : (Λ[3, 1] : SSet.{u}) ⟶ A := sorry
--   let τ : A _⦋3⦌ := sorry
--     -- BUILD FAILS:
--     -- A.yonedaEquiv _ (Classical.choose $ Quasicategory.hornFilling
--     --   (by simp) (by simp [Fin.lt_iff_val_lt_val]) σ)
--   have τ₀ : A.δ 0 τ = (A.δ 0 ≫ A.σ 0≫ A.σ 0) g := sorry
--   have τ₂ : A.δ 2 τ = H₂.simplex := sorry
--   have τ₃ : A.δ 3 τ = H₁.simplex := sorry
--   use A.δ 1 τ
--   . change (A.δ 1 ≫ A.δ 0) _ = _
--     rw [A.δ_comp_δ' (by simp)]; simp [τ₀]
--     change (A.σ 0 ≫ A.δ 0) _ = _
--     rw [A.δ_comp_σ_self' (by simp)]; simp
--   . rw [← H₂.δ₁_eq, ← τ₂]
--     change _ = (A.δ 2 ≫ A.δ 1) _
--     rw [A.δ_comp_δ' (by simp)]; rfl
--   . rw [← H₁.δ₁_eq, ← τ₃]
--     change _ = (A.δ 3 ≫ A.δ 1) _
--     rw [A.δ_comp_δ' (by simp)]; rfl

-- lemma HomotopyL.equiv :
--     Equivalence (fun f g : A _⦋1⦌ ↦ HomotopicL f g) where
--   refl f := ⟨HomotopyL.refl f⟩
--   symm := by
--     intro f g ⟨H⟩
--     exact ⟨H.ofHomotopyLOfHomotopyL (HomotopyL.refl f)⟩
--   trans := by
--     intro f g h ⟨H₁⟩ ⟨H₂⟩
--     exact ⟨(H₁.ofHomotopyLOfHomotopyL (HomotopyL.refl f)).ofHomotopyLOfHomotopyL H₂⟩

-- lemma homotopicL_iff_homotopicR [Quasicategory A] :
--     HomotopicL f g ↔ HomotopicR f g := sorry

-- lemma HomotopyR.equiv [Quasicategory A] :
--     Equivalence (fun f g : A _⦋1⦌ ↦ HomotopicR f g) := by
--   simp [← homotopicL_iff_homotopicR, HomotopyL.equiv]

end

end SSet
