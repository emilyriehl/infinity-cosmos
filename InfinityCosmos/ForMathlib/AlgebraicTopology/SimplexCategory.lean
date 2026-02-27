import Architect
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory Simplicial SimplexCategory Limits

namespace SimplexCategory

attribute [blueprint
  "defn:simplex-category"
  (title := "the simplex category")
  (statement := /--
  Let $\Del$ denote the \textbf{simplex category} of finite nonempty ordinals $[n] = \{0 <1 <\cdots
  < n\}$ and order-preserving maps.
  -/)]
  smallCategory

attribute [blueprint
  "defn:face-map"
  (title := "elementary face maps")
  (statement := /--
  The \textbf{elementary~face~operators} are the maps
  \begin{center}
  \begin{tikzcd}[row sep=tiny, column sep=small]
     {[n-1]} \arrow[r, tail, "{\face^i}"] & {[n]}  & {0 \leq i \leq n}
  \end{tikzcd}
  \end{center}
  whose images omit the element $i \in [n]$.
  -/)]
  δ

attribute [blueprint
  "defn:degeneracy-map"
  (title := "elementary degeneracy maps")
  (statement := /--
    The \textbf{elementary~degeneracy~operators} are the maps
  \begin{center}
  \begin{tikzcd}[row sep=tiny, column sep=small]
   {[n+1]} \arrow[r, two heads, "{\degen^i}"] & {[n]} & {0 \leq i \leq n }
  \end{tikzcd}
  \end{center}
  whose images  double up on the element $i \in [n]$.
  -/)]
  σ

attribute [blueprint
  "prop:simplex-cat-factorization"
  (statement := /--
  Every morphism in $\Del$ factors uniquely as an epimorphism followed by a monomorphism; these
  epimorphisms, the \textbf{degeneracy operators}, decompose as composites of elementary degeneracy
  operators, while the monomorphisms, the \textbf{face operators}, decompose as composites of
  elementary face operators.
  -/)
  (proof := /--
  The image factorizations have been formalized but the canonical decompositions into elementary
  face and degeneracy operators remain to be done.
  -/)
  (latexEnv := "proposition")]
  SimplexCategory.instHasStrongEpiImages

def δ_zero_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 0 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) j := by
  ext x
  fin_cases x
  aesop

def δ_one_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 1 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) i := by
  ext x
  fin_cases x
  aesop

end SimplexCategory
