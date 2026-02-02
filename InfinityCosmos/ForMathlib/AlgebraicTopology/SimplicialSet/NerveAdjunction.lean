import Architect
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

open CategoryTheory SSet

attribute [blueprint
  "prop:ho-nerve-adjunction"
  (statement := /--
   The nerve embedding admits a left adjoint, namely the functor which sends a simplicial set to its
   homotopy category:
  \begin{center}
  \begin{tikzcd}[column sep=huge]
    \mathcal{C}at \arrow[r, start anchor=353, end anchor=190, bend right, hook'] \arrow[r, phantom,
    "\bot"] & s\mathcal{S}et \arrow[l, start anchor=170, end anchor=7, bend right, "\ho"' pos=.48]
  \end{tikzcd}
  \end{center}
  -/)
  (proof := /--
  For any simplicial set $X$, there is a natural map from $X$ to the nerve of its homotopy category
  $\ho{X}$; since nerves are 2-coskeletal, it suffices to define the map $\sk_2X \to \ho{X}$, and
  this is given immediately by the construction of Definition \ref{defn:homotopy-cat}. Note that the
  quotient map $X \to \ho{X}$ becomes an isomorphism upon applying the homotopy category functor and
  is already an isomorphism whenever $X$ is the nerve of a category. Thus the adjointness follows
  %from Lemma \ref{lem:RARI-construction} or
  by direct verification of the triangle equalities.
  -/)
  (latexEnv := "proposition")]
  nerveAdjunction

attribute [blueprint
  "prop:nerve-fully-faithful"
  (statement := /-- The nerve functor is fully faithful. -/)
  (proof := /-- This has been formalized and is now in Mathlib. -/)
  (latexEnv := "proposition")]
  nerveFunctor.fullyfaithful

attribute [blueprint
  "prop:nerve-reflective"
  (statement := /--
  The homotopy category of the nerve of a 1-category is isomorphic to the original category, as the
  2-simplices in the nerve witness all of the composition relations satisfied by the arrows in the
  underlying reflexive directed graph.
  -/)
  (proof := /-- This has been formalized and is now in Mathlib. -/)
  (latexEnv := "proposition")]
  nerveFunctorCompHoFunctorIso

attribute [blueprint
  "lem:ho-preserves-finite-products"
  (statement := /-- The functor $\ho \colon \sSet \to \Cat$ preserves finite products. -/)
  (proof := /--
  Preservation of the terminal object is by direct calculation. By Proposition
  \ref{prop:nerve-reflective}, preservation of binary products is equivalent to the statement that
  the canonical map $N(\cD^\cC) \to N(\cD)^{N\cC}$ involving nerves of categories is an isomorphism.
  On $n$-simplices, this is defined by uncurrying, which is bijection since $\Cat$ is cartesian
  closed.
  -/)
  (latexEnv := "lemma")]
  hoFunctor.preservesFiniteProducts
