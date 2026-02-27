import Architect
import Mathlib.AlgebraicTopology.Quasicategory.Basic

open SSet

attribute [blueprint
  "defn:quasi-category"
  (title := "quasi-category")
  (statement := /--
     A \textbf{quasi-category} is a simplicial set $A$ in which any \textbf{inner horn} can be
     extended to a simplex, solving the displayed lifting problem:
    \begin{figure}\label{eq:qcat-defn}
    \begin{tikzcd}
    \Lambda^k[n] \arrow[r] \arrow[d, hook] & A  \\ \Delta[n] \arrow[ur, dashed]
    \end{tikzcd} \qquad  \text{for}\ \ n \geq 2,\ 0 < k < n.
  \end{figure}
  -/)]
  Quasicategory
