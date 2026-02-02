import Architect
import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal

open CategoryTheory

attribute [blueprint
  "prop:nerve-2-coskeletal"
  (statement := /--
  The nerve of a category $C$ is \textbf{2-coskeletal} as a simplicial set, meaning that every
  sphere $\partial\Delta[n] \to C$ with $n \geq 3$ is filled uniquely by an $n$-simplex in $C$, or
  equivalently that the nerve is canonically isomorphic to the right Kan extension of its
  restriction to 2-truncated simplicial sets.\footnote{The equivalence between these two
  perspectives is non-obvious and makes use of Reedy category theory (see \cite[\S
  C.4-5]{RiehlVerity:2022eo}), which does not currently exist in Mathlib.}% (see Definition
  % \ref{defn:sk-cosk}).
  -/)
  (proof := /--
  Note a sphere $\partial\Delta[2] \to C$ extends to a 2-simplex if and only if that arrow along its
  diagonal edge is the composite of the arrows along the edges in the inner horn $\Lambda^1[2]
  \subset \partial\Delta[2] \to C$. The simplices in dimension 3 and above witness the associativity
  of the composition of the path of composable arrows found along their  \textbf{spine}, the
  1-skeletal simplicial subset formed by the edges connecting adjacent vertices. In fact, as
  suggested by the proof of Proposition \ref{prop:nerve-qcat}, any simplicial set in which inner
  horns admit \emph{unique} fillers is isomorphic to the nerve of a 1-category. This
  characterization of nerves is not yet in Mathlib, however, we have proven the one-way result,
  namely that nerves of categories satisfy the ``strict Segal condition'' and this is used in the
  proof of 2-coskeletality.
  -/)
  (latexEnv := "proposition")]
  CategoryTheory.Nerve.cosk₂Iso
