import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCore

open CategoryTheory Simplicial

namespace SSet

/-- Inner-horn filler interface for `isoCore A`.  This is the inner-horn half of the
Kan-complex proof for `isoCore A`; outer horns are supplied separately. -/
theorem isoCore_innerHornFiller {A : SSet} [Quasicategory A]
    {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n)
    (τ : (Λ[n, i] : SSet) ⟶ (isoCore A : SSet)) :
    ∃ σ : Δ[n] ⟶ (isoCore A : SSet), τ = Λ[n, i].ι ≫ σ := by
  obtain ⟨g, hg⟩ := Quasicategory.hornFilling h0 hn (τ ≫ (isoCore A).ι)
  have hg' : τ ≫ (isoCore A).ι = Λ[n, i].ι ≫ g := hg
  refine ⟨Subcomplex.lift g ?_, ?_⟩
  · intro m y hy
    rcases hy with ⟨x, rfl⟩
    change g.app m x ∈ (isoCore A).obj m
    have hval : A.map (stdSimplex.objEquiv x).op (yonedaEquiv g) = g.app m x := by
      rw [stdSimplex.map_objEquiv_op_apply, Equiv.symm_apply_apply]
    rw [← hval]
    exact (isoCore A).map (stdSimplex.objEquiv x).op (filler_mem_isoCore h0 hn hg')
  · apply (cancel_mono (isoCore A).ι).mp
    rw [Category.assoc, Subcomplex.lift_ι]
    exact hg'

end SSet
