import Architect
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

open CategoryTheory

attribute [blueprint
  "defn:nerve"
  (title := "nerve")
  (statement := /--
  The category $\Cat$ of 1-categories embeds fully faithfully into the category of simplicial sets
  via the \textbf{nerve} functor. An $n$-simplex in the nerve of a 1-category $C$ is a sequence of
  $n$ composable arrows in $C$, or equally a functor $\catnone \to C$ from the ordinal category
  $\catnone$ with objects $0,\ldots, n$ and a unique arrow $i \to j$ just when $i \leq j$.
  -/)]
  nerve

attribute [blueprint
  "defn:nerve-functor"
  (title := "nerve functor")
  (statement := /--
  The map $[n] \mapsto \catnone$ defines a fully faithful embedding $\Del\inc\Cat$. From this point
  of view, the nerve functor can be described as a ``restricted Yoneda embedding'' which carries a
  category $C$ to the restriction of the representable functor $\hom(-,C)$ to the image of this
  inclusion.
  -/)]
  nerveFunctor
