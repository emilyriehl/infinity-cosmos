import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Join
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Slices of simplicial sets via the join

This file starts the join-slice adjunction API.  The join functor is valued in
the coslice `Under K` using the right-factor inclusion `K ⟶ Y ⋆ K`; this is the
relative setting where the empty-colimit obstruction for the plain functor
`Y ↦ Y ⋆ K` disappears.
-/

open CategoryTheory Simplicial Opposite Limits
open scoped Simplicial

universe u

namespace SSet

noncomputable section

/-- The plain fixed-right join functor does not preserve the empty colimit. -/
theorem joinFlip_not_preservesInitial :
    ¬ PreservesColimitsOfShape (Discrete PEmpty.{1})
        (joinFunctor.flip.obj (Δ[0] : SSet.{u})) := by
  intro h
  haveI : PreservesColimit (Functor.empty.{0} SSet.{u})
      (joinFunctor.flip.obj (Δ[0] : SSet.{u})) := by
    exact PreservesColimitsOfShape.preservesColimit
  let bad : Δ[0] ⟶ (⊥_ SSet.{u}) :=
    joinInr (⊥_ SSet.{u}) (Δ[0] : SSet.{u}) ≫
      (PreservesInitial.iso (joinFunctor.flip.obj (Δ[0] : SSet.{u}))).hom
  let x := (bad.app (op ⦋0⦌)) (yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  have hInitial : IsInitial ((⊥_ SSet.{u}) _⦋0⦌) := by
    haveI : PreservesColimit (Functor.empty.{0} SSet.{u})
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) :=
      inferInstance
    exact initialIsInitial.isInitialObj
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) (⊥_ SSet.{u})
  haveI : IsEmpty ((⊥_ SSet.{u}) _⦋0⦌) :=
    (Types.initial_iff_empty ((⊥_ SSet.{u}) _⦋0⦌)).mp ⟨hInitial⟩
  exact IsEmpty.false x

/-- The fixed-right join functor lifted to the coslice under the right factor. -/
def joinUnder (K : SSet.{u}) : SSet.{u} ⥤ Under K where
  obj Y := Under.mk (joinInr Y K)
  map {Y Y'} f := Under.homMk ((joinFunctor.map f).app K) (joinInr_naturality_left f K)
  map_id Y := by
    apply Under.UnderMorphism.ext
    show (joinFunctor.map (𝟙 Y)).app K = 𝟙 _
    rw [joinFunctor.map_id]
    rfl
  map_comp {Y Y' Y''} f g := by
    apply Under.UnderMorphism.ext
    show (joinFunctor.map (f ≫ g)).app K =
      (joinFunctor.map f).app K ≫ (joinFunctor.map g).app K
    rw [joinFunctor.map_comp]
    rfl

@[simp]
theorem joinUnder_forget (K : SSet.{u}) :
    joinUnder K ⋙ Under.forget K = joinFunctor.flip.obj K :=
  rfl

/-- Maps out of `joinUnder K` are exactly maps `Y ⋆ K ⟶ C` restricting to `p` on `K`. -/
def overPtEquivUnderHom {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) :
    { q : Y ⋆ K ⟶ C // joinInr Y K ≫ q = p } ≃ ((joinUnder K).obj Y ⟶ Under.mk p) where
  toFun q := Under.homMk q.1 q.2
  invFun g := ⟨g.right, Under.w g⟩
  left_inv q := by
    cases q
    rfl
  right_inv g := by
    ext
    rfl

/-- The set of maps `Y ⋆ K ⟶ C` restricting to `p` on the right factor. -/
abbrev OverPt {K C : SSet.{u}} (p : K ⟶ C) (Y : SSet.{u}) : Type u :=
  { q : Y ⋆ K ⟶ C // joinInr Y K ≫ q = p }

/-- The slice simplicial set `C_{/p}`.  Its `n`-simplices are maps
`Δ[n] ⋆ K ⟶ C` restricting to `p` on the right factor. -/
def sliceOver {K C : SSet.{u}} (p : K ⟶ C) : SSet.{u} where
  obj n := OverPt p (stdSimplex.obj n.unop)
  map {n m} f :=
    ↾fun q =>
      (⟨(joinFunctor.map (stdSimplex.map f.unop)).app K ≫ q.1, by
        rw [← Category.assoc, joinInr_naturality_left]
        exact q.2⟩ : OverPt p (stdSimplex.obj m.unop))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show (joinFunctor.map (stdSimplex.map (𝟙 n).unop)).app K ≫ q.1 = q.1
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    show (joinFunctor.map (stdSimplex.map (f ≫ g).unop)).app K ≫ q.1 =
      (joinFunctor.map (stdSimplex.map g.unop)).app K ≫
        (joinFunctor.map (stdSimplex.map f.unop)).app K ≫ q.1
    simp only [unop_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- The representable case of the join-slice universal property. -/
def sliceHomEquivStdSimplex {K C : SSet.{u}} (p : K ⟶ C) (m : SimplexCategory) :
    (stdSimplex.obj m ⟶ sliceOver p) ≃ OverPt p (stdSimplex.obj m) :=
  yonedaEquiv

end

end SSet
