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

end

end SSet
