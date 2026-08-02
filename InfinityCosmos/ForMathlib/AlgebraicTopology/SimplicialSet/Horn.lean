module

public import Architect
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

@[expose] public section


open Simplicial SSet CategoryTheory Subcomplex

namespace SSet

attribute [blueprint
  "defn:simplicial-horn"
  (title := "simplicial horn")
  (statement := /--
  We write $\Lambda^k[n] \subset \Delta[n]$ for the $k$-\textbf{horn} in the $n$-simplex. The horn
  $\Lambda^k[n]$ is the further simplicial subset of $\partial\Delta[n]$ that omits the face
  opposite the vertex $k$, but it is defined as a subset of $\Delta[n]$.
  -/)]
  horn

end SSet
