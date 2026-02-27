import Architect
import Mathlib.CategoryTheory.Enriched.Basic

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
