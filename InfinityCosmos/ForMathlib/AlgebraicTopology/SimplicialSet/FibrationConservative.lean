import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCore
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.RightFibration
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

open CategoryTheory Simplicial

universe u

namespace SSet

variable {X S : SSet.{u}}

/-- The low-dimensional lift data used by the conservativity proof for left fibrations. -/
class LeftFibrationData (p : X ⟶ S) where
  liftEdge : ∀ {x₀ : X _⦋0⦌} {s₁ : S _⦋0⦌} (e : Edge (p.app _ x₀) s₁),
    ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁), p.app _ x₁ = s₁ ∧ (e'.map p).edge = e.edge
  fillTwoZero : ∀ {x₀ x₁ x₂ : X _⦋0⦌} (e : Edge x₀ x₁) (d : Edge x₀ x₂)
      {m : Edge (p.app _ x₁) (p.app _ x₂)}
      (_cs : Edge.CompStruct (e.map p) m (d.map p)),
    ∃ (k : Edge x₁ x₂), Nonempty (Edge.CompStruct e k d) ∧ (k.map p).edge = m.edge

/-- The low-dimensional lift data used by the conservativity proof for right fibrations. -/
class RightFibrationData (p : X ⟶ S) where
  liftEdge : ∀ {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌} (e : Edge s₀ (p.app _ x₁)),
    ∃ (x₀ : X _⦋0⦌) (e' : Edge x₀ x₁), p.app _ x₀ = s₀ ∧ (e'.map p).edge = e.edge
  fillTwoTwo : ∀ {x₀ x₁ x₂ : X _⦋0⦌} (d : Edge x₀ x₂) (e : Edge x₁ x₂)
      {m : Edge (p.app _ x₀) (p.app _ x₁)}
      (_cs : Edge.CompStruct m (e.map p) (d.map p)),
    ∃ (k : Edge x₀ x₁), Nonempty (Edge.CompStruct k e d) ∧ (k.map p).edge = m.edge

namespace fibrationData

noncomputable def leftEndpointTop {X : SSet.{u}} (x₀ : X _⦋0⦌) :
    (Λ[1, (0 : Fin 2)] : SSet.{u}) ⟶ X :=
  (show horn.IsCompatible (fun (j : Fin 2) (_ : j ≠ (0 : Fin 2)) =>
    yonedaEquiv.symm x₀) from by simp).desc

lemma leftEndpointTop_face {X : SSet.{u}} (x₀ : X _⦋0⦌) (h : (1 : Fin 2) ≠ 0) :
    horn.ι (0 : Fin 2) 1 h ≫ leftEndpointTop x₀ = yonedaEquiv.symm x₀ := by
  unfold leftEndpointTop
  rw [horn.IsCompatible.ι_desc]

lemma leftEndpointSq {p : X ⟶ S} {x₀ : X _⦋0⦌} {s₁ : S _⦋0⦌}
    (e : Edge (p.app _ x₀) s₁) :
    CommSq (leftEndpointTop x₀) (Λ[1, (0 : Fin 2)].ι) p (yonedaEquiv.symm e.edge) := by
  constructor
  apply horn.hom_ext'
  intro j hj
  fin_cases j
  · contradiction
  · have htop : horn.ι (0 : Fin 2) ⟨1, by omega⟩ hj ≫ leftEndpointTop x₀ =
        yonedaEquiv.symm x₀ :=
      leftEndpointTop_face x₀ hj
    have hface : horn.ι (0 : Fin 2) ⟨1, by omega⟩ hj ≫ Λ[1, (0 : Fin 2)].ι =
        stdSimplex.δ (1 : Fin 2) := by
      simpa using (horn.ι_ι (i := (0 : Fin 2)) (j := ⟨1, by omega⟩) (hij := hj))
    calc
      horn.ι 0 ⟨1, by omega⟩ hj ≫ leftEndpointTop x₀ ≫ p =
          yonedaEquiv.symm x₀ ≫ p := by rw [← Category.assoc, htop]
      _ = stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e.edge := by
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change p.app (Opposite.op ⦋0⦌) x₀ =
          S.map (SimplexCategory.δ (1 : Fin 2)).op e.edge
        exact e.src_eq.symm
      _ = horn.ι 0 ⟨1, by omega⟩ hj ≫ Λ[1, 0].ι ≫ yonedaEquiv.symm e.edge := by
        rw [← hface, Category.assoc]

noncomputable def rightEndpointTop {X : SSet.{u}} (x₁ : X _⦋0⦌) :
    (Λ[1, (1 : Fin 2)] : SSet.{u}) ⟶ X :=
  (show horn.IsCompatible (fun (j : Fin 2) (_ : j ≠ (1 : Fin 2)) =>
    yonedaEquiv.symm x₁) from by simp).desc

lemma rightEndpointTop_face {X : SSet.{u}} (x₁ : X _⦋0⦌) (h : (0 : Fin 2) ≠ 1) :
    horn.ι (1 : Fin 2) 0 h ≫ rightEndpointTop x₁ = yonedaEquiv.symm x₁ := by
  unfold rightEndpointTop
  rw [horn.IsCompatible.ι_desc]

lemma rightEndpointSq {p : X ⟶ S} {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌}
    (e : Edge s₀ (p.app _ x₁)) :
    CommSq (rightEndpointTop x₁) (Λ[1, (1 : Fin 2)].ι) p (yonedaEquiv.symm e.edge) := by
  constructor
  apply horn.hom_ext'
  intro j hj
  fin_cases j
  · have htop : horn.ι (1 : Fin 2) ⟨0, by omega⟩ hj ≫ rightEndpointTop x₁ =
        yonedaEquiv.symm x₁ :=
      rightEndpointTop_face x₁ hj
    have hface : horn.ι (1 : Fin 2) ⟨0, by omega⟩ hj ≫ Λ[1, (1 : Fin 2)].ι =
        stdSimplex.δ (0 : Fin 2) := by
      simpa using (horn.ι_ι (i := (1 : Fin 2)) (j := ⟨0, by omega⟩) (hij := hj))
    calc
      horn.ι 1 ⟨0, by omega⟩ hj ≫ rightEndpointTop x₁ ≫ p =
          yonedaEquiv.symm x₁ ≫ p := by rw [← Category.assoc, htop]
      _ = stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge := by
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change p.app (Opposite.op ⦋0⦌) x₁ =
          S.map (SimplexCategory.δ (0 : Fin 2)).op e.edge
        exact e.tgt_eq.symm
      _ = horn.ι 1 ⟨0, by omega⟩ hj ≫ Λ[1, 1].ι ≫ yonedaEquiv.symm e.edge := by
        rw [← hface, Category.assoc]
  · contradiction

noncomputable def leftTwoZeroTop {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    (e : Edge x₀ x₁) (d : Edge x₀ x₂) :
    (Λ[2, (0 : Fin 3)] : SSet.{u}) ⟶ X :=
  (show horn.IsCompatible (i := (0 : Fin 3))
      (fun (j : Fin 3) (_ : j ≠ (0 : Fin 3)) =>
        match j with
        | ⟨0, _⟩ => yonedaEquiv.symm e.edge
        | ⟨1, _⟩ => yonedaEquiv.symm d.edge
        | ⟨2, _⟩ => yonedaEquiv.symm e.edge) from by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp]
    change (ConcreteCategory.hom (SimplicialObject.δ X 1)) d.edge =
      (ConcreteCategory.hom (SimplicialObject.δ X 1)) e.edge
    rw [d.src_eq, e.src_eq]).desc

lemma leftTwoZeroSq {p : X ⟶ S} {x₀ x₁ x₂ : X _⦋0⦌}
    (e : Edge x₀ x₁) (d : Edge x₀ x₂)
    {m : Edge (p.app _ x₁) (p.app _ x₂)}
    (cs : Edge.CompStruct (e.map p) m (d.map p)) :
    CommSq (leftTwoZeroTop e d) (Λ[2, (0 : Fin 3)].ι) p
      (yonedaEquiv.symm cs.simplex) := by
  constructor
  apply horn.hom_ext'
  intro j hj
  fin_cases j
  · contradiction
  · have htop : horn.ι (0 : Fin 3) ⟨1, by omega⟩ hj ≫ leftTwoZeroTop e d =
        yonedaEquiv.symm d.edge := by
      unfold leftTwoZeroTop
      rw [horn.IsCompatible.ι_desc]
    have hface : horn.ι (0 : Fin 3) ⟨1, by omega⟩ hj ≫ Λ[2, (0 : Fin 3)].ι =
        stdSimplex.δ (1 : Fin 3) := by
      simpa using (horn.ι_ι (i := (0 : Fin 3)) (j := ⟨1, by omega⟩) (hij := hj))
    calc
      horn.ι 0 ⟨1, by omega⟩ hj ≫ leftTwoZeroTop e d ≫ p =
          yonedaEquiv.symm d.edge ≫ p := by rw [← Category.assoc, htop]
      _ = stdSimplex.δ (1 : Fin 3) ≫ yonedaEquiv.symm cs.simplex := by
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change p.app (Opposite.op ⦋1⦌) d.edge =
          (ConcreteCategory.hom (SimplicialObject.δ S 1)) cs.simplex
        rw [cs.d₁]
        rfl
      _ = horn.ι 0 ⟨1, by omega⟩ hj ≫ Λ[2, 0].ι ≫ yonedaEquiv.symm cs.simplex := by
        rw [← hface, Category.assoc]
  · have htop : horn.ι (0 : Fin 3) ⟨2, by omega⟩ hj ≫ leftTwoZeroTop e d =
        yonedaEquiv.symm e.edge := by
      unfold leftTwoZeroTop
      rw [horn.IsCompatible.ι_desc]
    have hface : horn.ι (0 : Fin 3) ⟨2, by omega⟩ hj ≫ Λ[2, (0 : Fin 3)].ι =
        stdSimplex.δ (2 : Fin 3) := by
      simpa using (horn.ι_ι (i := (0 : Fin 3)) (j := ⟨2, by omega⟩) (hij := hj))
    calc
      horn.ι 0 ⟨2, by omega⟩ hj ≫ leftTwoZeroTop e d ≫ p =
          yonedaEquiv.symm e.edge ≫ p := by rw [← Category.assoc, htop]
      _ = stdSimplex.δ (2 : Fin 3) ≫ yonedaEquiv.symm cs.simplex := by
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change p.app (Opposite.op ⦋1⦌) e.edge =
          (ConcreteCategory.hom (SimplicialObject.δ S 2)) cs.simplex
        rw [cs.d₂]
        rfl
      _ = horn.ι 0 ⟨2, by omega⟩ hj ≫ Λ[2, 0].ι ≫ yonedaEquiv.symm cs.simplex := by
        rw [← hface, Category.assoc]

noncomputable def rightTwoTwoTop {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    (d : Edge x₀ x₂) (e : Edge x₁ x₂) :
    (Λ[2, (2 : Fin 3)] : SSet.{u}) ⟶ X :=
  (show horn.IsCompatible (i := (2 : Fin 3))
      (fun (j : Fin 3) (_ : j ≠ (2 : Fin 3)) =>
        match j with
        | ⟨0, _⟩ => yonedaEquiv.symm e.edge
        | ⟨1, _⟩ => yonedaEquiv.symm d.edge
        | ⟨2, _⟩ => yonedaEquiv.symm d.edge) from by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp]
    change (ConcreteCategory.hom (SimplicialObject.δ X 0)) e.edge =
      (ConcreteCategory.hom (SimplicialObject.δ X 0)) d.edge
    rw [e.tgt_eq, d.tgt_eq]).desc

lemma rightTwoTwoSq {p : X ⟶ S} {x₀ x₁ x₂ : X _⦋0⦌}
    (d : Edge x₀ x₂) (e : Edge x₁ x₂)
    {m : Edge (p.app _ x₀) (p.app _ x₁)}
    (cs : Edge.CompStruct m (e.map p) (d.map p)) :
    CommSq (rightTwoTwoTop d e) (Λ[2, (2 : Fin 3)].ι) p
      (yonedaEquiv.symm cs.simplex) := by
  constructor
  apply horn.hom_ext'
  intro j hj
  fin_cases j
  · have htop : horn.ι (2 : Fin 3) ⟨0, by omega⟩ hj ≫ rightTwoTwoTop d e =
        yonedaEquiv.symm e.edge := by
      unfold rightTwoTwoTop
      rw [horn.IsCompatible.ι_desc]
    have hface : horn.ι (2 : Fin 3) ⟨0, by omega⟩ hj ≫ Λ[2, (2 : Fin 3)].ι =
        stdSimplex.δ (0 : Fin 3) := by
      simpa using (horn.ι_ι (i := (2 : Fin 3)) (j := ⟨0, by omega⟩) (hij := hj))
    calc
      horn.ι 2 ⟨0, by omega⟩ hj ≫ rightTwoTwoTop d e ≫ p =
          yonedaEquiv.symm e.edge ≫ p := by rw [← Category.assoc, htop]
      _ = stdSimplex.δ (0 : Fin 3) ≫ yonedaEquiv.symm cs.simplex := by
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change p.app (Opposite.op ⦋1⦌) e.edge =
          (ConcreteCategory.hom (SimplicialObject.δ S 0)) cs.simplex
        rw [cs.d₀]
        rfl
      _ = horn.ι 2 ⟨0, by omega⟩ hj ≫ Λ[2, 2].ι ≫ yonedaEquiv.symm cs.simplex := by
        rw [← hface, Category.assoc]
  · have htop : horn.ι (2 : Fin 3) ⟨1, by omega⟩ hj ≫ rightTwoTwoTop d e =
        yonedaEquiv.symm d.edge := by
      unfold rightTwoTwoTop
      rw [horn.IsCompatible.ι_desc]
    have hface : horn.ι (2 : Fin 3) ⟨1, by omega⟩ hj ≫ Λ[2, (2 : Fin 3)].ι =
        stdSimplex.δ (1 : Fin 3) := by
      simpa using (horn.ι_ι (i := (2 : Fin 3)) (j := ⟨1, by omega⟩) (hij := hj))
    calc
      horn.ι 2 ⟨1, by omega⟩ hj ≫ rightTwoTwoTop d e ≫ p =
          yonedaEquiv.symm d.edge ≫ p := by rw [← Category.assoc, htop]
      _ = stdSimplex.δ (1 : Fin 3) ≫ yonedaEquiv.symm cs.simplex := by
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        change p.app (Opposite.op ⦋1⦌) d.edge =
          (ConcreteCategory.hom (SimplicialObject.δ S 1)) cs.simplex
        rw [cs.d₁]
        rfl
      _ = horn.ι 2 ⟨1, by omega⟩ hj ≫ Λ[2, 2].ι ≫ yonedaEquiv.symm cs.simplex := by
        rw [← hface, Category.assoc]
  · contradiction

end fibrationData

open fibrationData

theorem leftLiftEdgeOfLeftFibration {p : X ⟶ S} [LeftFibration p]
    {x₀ : X _⦋0⦌} {s₁ : S _⦋0⦌} (e : Edge (p.app _ x₀) s₁) :
    ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₁ = s₁ ∧ (e'.map p).edge = e.edge := by
  have sq := leftEndpointSq (p := p) e
  haveI : HasLiftingProperty (Λ[1, (0 : Fin 2)].ι) p :=
    mem_leftFibrations p _ ⟨(0 : Fin 2), by simp⟩
  let l : Δ[1] ⟶ X := sq.lift
  let σ : X _⦋1⦌ := yonedaEquiv l
  let x₁ : X _⦋0⦌ := X.map (SimplexCategory.δ (0 : Fin 2)).op σ
  have hsrcMap : stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ l =
      yonedaEquiv.symm x₀ := by
    have hface := congrArg (fun q =>
      horn.ι (0 : Fin 2) ⟨1, by omega⟩ (by decide) ≫ q) sq.fac_left
    change (horn.ι (0 : Fin 2) ⟨1, by omega⟩ (by decide) ≫
        Λ[1, (0 : Fin 2)].ι) ≫ l =
      horn.ι (0 : Fin 2) ⟨1, by omega⟩ (by decide) ≫ leftEndpointTop x₀ at hface
    rw [horn.ι_ι] at hface
    rw [show horn.ι (0 : Fin 2) ⟨1, by omega⟩ (by decide) ≫ leftEndpointTop x₀ =
        yonedaEquiv.symm x₀ by
      unfold leftEndpointTop
      rw [horn.IsCompatible.ι_desc]] at hface
    exact hface
  have hsrc : X.map (SimplexCategory.δ (1 : Fin 2)).op σ = x₀ := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality (SimplexCategory.δ (1 : Fin 2)) σ]
    have hσ : yonedaEquiv.symm σ = l := by simp [σ]
    rw [hσ]
    exact hsrcMap
  have hedge : p.app (Opposite.op ⦋1⦌) σ = e.edge := by
    have hright := sq.fac_right
    apply congrArg yonedaEquiv at hright
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at hright
    exact hright
  have hnat : p.app (Opposite.op ⦋0⦌)
      (X.map (SimplexCategory.δ (0 : Fin 2)).op σ) =
      S.map (SimplexCategory.δ (0 : Fin 2)).op (p.app (Opposite.op ⦋1⦌) σ) := by
    simpa using congr_fun
      (congrArg ConcreteCategory.hom (p.naturality (SimplexCategory.δ (0 : Fin 2)).op)) σ
  refine ⟨x₁, Edge.mk σ hsrc rfl, ?_, ?_⟩
  · dsimp [x₁]
    rw [hnat, hedge]
    change (ConcreteCategory.hom (SimplicialObject.δ S 0)) e.edge = s₁
    exact e.tgt_eq
  · dsimp [Edge.map]
    exact hedge

theorem rightLiftEdgeOfRightFibration {p : X ⟶ S} [RightFibration p]
    {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌} (e : Edge s₀ (p.app _ x₁)) :
    ∃ (x₀ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₀ = s₀ ∧ (e'.map p).edge = e.edge := by
  have sq := rightEndpointSq (p := p) e
  haveI : HasLiftingProperty (Λ[1, (1 : Fin 2)].ι) p :=
    mem_rightFibrations p _ ⟨(1 : Fin 2), by simp⟩
  let l : Δ[1] ⟶ X := sq.lift
  let σ : X _⦋1⦌ := yonedaEquiv l
  let x₀ : X _⦋0⦌ := X.map (SimplexCategory.δ (1 : Fin 2)).op σ
  have htgtMap : stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ l =
      yonedaEquiv.symm x₁ := by
    have hface := congrArg (fun q =>
      horn.ι (1 : Fin 2) ⟨0, by omega⟩ (by decide) ≫ q) sq.fac_left
    change (horn.ι (1 : Fin 2) ⟨0, by omega⟩ (by decide) ≫
        Λ[1, (1 : Fin 2)].ι) ≫ l =
      horn.ι (1 : Fin 2) ⟨0, by omega⟩ (by decide) ≫ rightEndpointTop x₁ at hface
    rw [horn.ι_ι] at hface
    rw [show horn.ι (1 : Fin 2) ⟨0, by omega⟩ (by decide) ≫ rightEndpointTop x₁ =
        yonedaEquiv.symm x₁ by
      unfold rightEndpointTop
      rw [horn.IsCompatible.ι_desc]] at hface
    exact hface
  have htgt : X.map (SimplexCategory.δ (0 : Fin 2)).op σ = x₁ := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality (SimplexCategory.δ (0 : Fin 2)) σ]
    have hσ : yonedaEquiv.symm σ = l := by simp [σ]
    rw [hσ]
    exact htgtMap
  have hedge : p.app (Opposite.op ⦋1⦌) σ = e.edge := by
    have hright := sq.fac_right
    apply congrArg yonedaEquiv at hright
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at hright
    exact hright
  have hnat : p.app (Opposite.op ⦋0⦌)
      (X.map (SimplexCategory.δ (1 : Fin 2)).op σ) =
      S.map (SimplexCategory.δ (1 : Fin 2)).op (p.app (Opposite.op ⦋1⦌) σ) := by
    simpa using congr_fun
      (congrArg ConcreteCategory.hom (p.naturality (SimplexCategory.δ (1 : Fin 2)).op)) σ
  refine ⟨x₀, Edge.mk σ rfl htgt, ?_, ?_⟩
  · dsimp [x₀]
    rw [hnat, hedge]
    change (ConcreteCategory.hom (SimplicialObject.δ S 1)) e.edge = s₀
    exact e.src_eq
  · dsimp [Edge.map]
    exact hedge

theorem leftFillTwoZeroOfLeftFibration {p : X ⟶ S} [LeftFibration p]
    {x₀ x₁ x₂ : X _⦋0⦌} (e : Edge x₀ x₁) (d : Edge x₀ x₂)
    {m : Edge (p.app _ x₁) (p.app _ x₂)}
    (cs : Edge.CompStruct (e.map p) m (d.map p)) :
    ∃ (k : Edge x₁ x₂), Nonempty (Edge.CompStruct e k d) ∧ (k.map p).edge = m.edge := by
  have sq := leftTwoZeroSq (p := p) e d cs
  haveI : HasLiftingProperty (Λ[2, (0 : Fin 3)].ι) p :=
    mem_leftFibrations p _ ⟨(0 : Fin 3), by simp⟩
  let l : Δ[2] ⟶ X := sq.lift
  let σ : X _⦋2⦌ := yonedaEquiv l
  have hbase : p.app (Opposite.op ⦋2⦌) σ = cs.simplex := by
    have hright := sq.fac_right
    apply congrArg yonedaEquiv at hright
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at hright
    exact hright
  have h1map : stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫ l =
      yonedaEquiv.symm d.edge := by
    have hface := congrArg (fun q =>
      horn.ι (0 : Fin 3) ⟨1, by omega⟩ (by decide) ≫ q) sq.fac_left
    change (horn.ι (0 : Fin 3) ⟨1, by omega⟩ (by decide) ≫
        Λ[2, (0 : Fin 3)].ι) ≫ l =
      horn.ι (0 : Fin 3) ⟨1, by omega⟩ (by decide) ≫ leftTwoZeroTop e d at hface
    rw [horn.ι_ι] at hface
    rw [show horn.ι (0 : Fin 3) ⟨1, by omega⟩ (by decide) ≫ leftTwoZeroTop e d =
        yonedaEquiv.symm d.edge by
      unfold leftTwoZeroTop
      rw [horn.IsCompatible.ι_desc]] at hface
    exact hface
  have h2map : stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫ l =
      yonedaEquiv.symm e.edge := by
    have hface := congrArg (fun q =>
      horn.ι (0 : Fin 3) ⟨2, by omega⟩ (by decide) ≫ q) sq.fac_left
    change (horn.ι (0 : Fin 3) ⟨2, by omega⟩ (by decide) ≫
        Λ[2, (0 : Fin 3)].ι) ≫ l =
      horn.ι (0 : Fin 3) ⟨2, by omega⟩ (by decide) ≫ leftTwoZeroTop e d at hface
    rw [horn.ι_ι] at hface
    rw [show horn.ι (0 : Fin 3) ⟨2, by omega⟩ (by decide) ≫ leftTwoZeroTop e d =
        yonedaEquiv.symm e.edge by
      unfold leftTwoZeroTop
      rw [horn.IsCompatible.ι_desc]] at hface
    exact hface
  have h1 : X.map (SimplexCategory.δ (1 : Fin 3)).op σ = d.edge := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality (SimplexCategory.δ (1 : Fin 3)) σ]
    have hσ : yonedaEquiv.symm σ = l := by simp [σ]
    rw [hσ]
    exact h1map
  have h2 : X.map (SimplexCategory.δ (2 : Fin 3)).op σ = e.edge := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality (SimplexCategory.δ (2 : Fin 3)) σ]
    have hσ : yonedaEquiv.symm σ = l := by simp [σ]
    rw [hσ]
    exact h2map
  let kEdge : X _⦋1⦌ := X.map (SimplexCategory.δ (0 : Fin 3)).op σ
  have ksrc : X.map (SimplexCategory.δ (1 : Fin 2)).op kEdge = x₁ := by
    dsimp [kEdge]
    rw [← e.tgt_eq, ← h2]
    change X.map (SimplexCategory.δ (1 : Fin 2)).op
        (X.map (SimplexCategory.δ (0 : Fin 3)).op σ) =
      X.map (SimplexCategory.δ (0 : Fin 2)).op
        (X.map (SimplexCategory.δ (2 : Fin 3)).op σ)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    have hδ : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) =
        SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) := by
      simpa using
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (by decide)).symm
    rw [hδ]
  have ktgt : X.map (SimplexCategory.δ (0 : Fin 2)).op kEdge = x₂ := by
    dsimp [kEdge]
    rw [← d.tgt_eq, ← h1]
    change X.map (SimplexCategory.δ (0 : Fin 2)).op
        (X.map (SimplexCategory.δ (0 : Fin 3)).op σ) =
      X.map (SimplexCategory.δ (0 : Fin 2)).op
        (X.map (SimplexCategory.δ (1 : Fin 3)).op σ)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    have hδ : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) =
        SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) := by
      simpa using
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          (by decide)).symm
    rw [hδ]
  let k : Edge x₁ x₂ := Edge.mk kEdge ksrc ktgt
  refine ⟨k, ⟨?_⟩, ?_⟩
  · exact Edge.CompStruct.mk σ h2 rfl h1
  · change p.app (Opposite.op ⦋1⦌) kEdge = m.edge
    have hnat : p.app (Opposite.op ⦋1⦌)
        (X.map (SimplexCategory.δ (0 : Fin 3)).op σ) =
        S.map (SimplexCategory.δ (0 : Fin 3)).op
          (p.app (Opposite.op ⦋2⦌) σ) := by
      simpa using congr_fun
        (congrArg ConcreteCategory.hom (p.naturality (SimplexCategory.δ (0 : Fin 3)).op)) σ
    rw [hnat, hbase]
    change (ConcreteCategory.hom (SimplicialObject.δ S 0)) cs.simplex = m.edge
    exact cs.d₀

instance leftFibrationDataOfLeftFibration {p : X ⟶ S} [LeftFibration p] :
    LeftFibrationData p where
  liftEdge := leftLiftEdgeOfLeftFibration
  fillTwoZero := leftFillTwoZeroOfLeftFibration

theorem rightFillTwoTwoOfRightFibration {p : X ⟶ S} [RightFibration p]
    {x₀ x₁ x₂ : X _⦋0⦌} (d : Edge x₀ x₂) (e : Edge x₁ x₂)
    {m : Edge (p.app _ x₀) (p.app _ x₁)}
    (cs : Edge.CompStruct m (e.map p) (d.map p)) :
    ∃ (k : Edge x₀ x₁), Nonempty (Edge.CompStruct k e d) ∧ (k.map p).edge = m.edge := by
  have sq := rightTwoTwoSq (p := p) d e cs
  haveI : HasLiftingProperty (Λ[2, (2 : Fin 3)].ι) p :=
    mem_rightFibrations p _ ⟨(2 : Fin 3), by simp⟩
  let l : Δ[2] ⟶ X := sq.lift
  let σ : X _⦋2⦌ := yonedaEquiv l
  have hbase : p.app (Opposite.op ⦋2⦌) σ = cs.simplex := by
    have hright := sq.fac_right
    apply congrArg yonedaEquiv at hright
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at hright
    exact hright
  have h0map : stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫ l =
      yonedaEquiv.symm e.edge := by
    have hface := congrArg (fun q =>
      horn.ι (2 : Fin 3) ⟨0, by omega⟩ (by decide) ≫ q) sq.fac_left
    change (horn.ι (2 : Fin 3) ⟨0, by omega⟩ (by decide) ≫
        Λ[2, (2 : Fin 3)].ι) ≫ l =
      horn.ι (2 : Fin 3) ⟨0, by omega⟩ (by decide) ≫ rightTwoTwoTop d e at hface
    rw [horn.ι_ι] at hface
    rw [show horn.ι (2 : Fin 3) ⟨0, by omega⟩ (by decide) ≫ rightTwoTwoTop d e =
        yonedaEquiv.symm e.edge by
      unfold rightTwoTwoTop
      rw [horn.IsCompatible.ι_desc]] at hface
    exact hface
  have h1map : stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫ l =
      yonedaEquiv.symm d.edge := by
    have hface := congrArg (fun q =>
      horn.ι (2 : Fin 3) ⟨1, by omega⟩ (by decide) ≫ q) sq.fac_left
    change (horn.ι (2 : Fin 3) ⟨1, by omega⟩ (by decide) ≫
        Λ[2, (2 : Fin 3)].ι) ≫ l =
      horn.ι (2 : Fin 3) ⟨1, by omega⟩ (by decide) ≫ rightTwoTwoTop d e at hface
    rw [horn.ι_ι] at hface
    rw [show horn.ι (2 : Fin 3) ⟨1, by omega⟩ (by decide) ≫ rightTwoTwoTop d e =
        yonedaEquiv.symm d.edge by
      unfold rightTwoTwoTop
      rw [horn.IsCompatible.ι_desc]] at hface
    exact hface
  have h0 : X.map (SimplexCategory.δ (0 : Fin 3)).op σ = e.edge := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality (SimplexCategory.δ (0 : Fin 3)) σ]
    have hσ : yonedaEquiv.symm σ = l := by simp [σ]
    rw [hσ]
    exact h0map
  have h1 : X.map (SimplexCategory.δ (1 : Fin 3)).op σ = d.edge := by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality (SimplexCategory.δ (1 : Fin 3)) σ]
    have hσ : yonedaEquiv.symm σ = l := by simp [σ]
    rw [hσ]
    exact h1map
  let kEdge : X _⦋1⦌ := X.map (SimplexCategory.δ (2 : Fin 3)).op σ
  have ksrc : X.map (SimplexCategory.δ (1 : Fin 2)).op kEdge = x₀ := by
    dsimp [kEdge]
    rw [← d.src_eq, ← h1]
    change X.map (SimplexCategory.δ (1 : Fin 2)).op
        (X.map (SimplexCategory.δ (2 : Fin 3)).op σ) =
      X.map (SimplexCategory.δ (1 : Fin 2)).op
        (X.map (SimplexCategory.δ (1 : Fin 3)).op σ)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    have hδ : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) =
        SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) := by
      simpa using
        (SimplexCategory.δ_comp_δ (i := (1 : Fin 2)) (j := (1 : Fin 2))
          (by decide))
    rw [hδ]
  have ktgt : X.map (SimplexCategory.δ (0 : Fin 2)).op kEdge = x₁ := by
    dsimp [kEdge]
    rw [← e.src_eq, ← h0]
    change X.map (SimplexCategory.δ (0 : Fin 2)).op
        (X.map (SimplexCategory.δ (2 : Fin 3)).op σ) =
      X.map (SimplexCategory.δ (1 : Fin 2)).op
        (X.map (SimplexCategory.δ (0 : Fin 3)).op σ)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    have hδ : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) =
        SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) := by
      simpa using
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (by decide))
    rw [hδ]
  let k : Edge x₀ x₁ := Edge.mk kEdge ksrc ktgt
  refine ⟨k, ⟨?_⟩, ?_⟩
  · exact Edge.CompStruct.mk σ rfl h0 h1
  · change p.app (Opposite.op ⦋1⦌) kEdge = m.edge
    have hnat : p.app (Opposite.op ⦋1⦌)
        (X.map (SimplexCategory.δ (2 : Fin 3)).op σ) =
        S.map (SimplexCategory.δ (2 : Fin 3)).op
          (p.app (Opposite.op ⦋2⦌) σ) := by
      simpa using congr_fun
        (congrArg ConcreteCategory.hom (p.naturality (SimplexCategory.δ (2 : Fin 3)).op)) σ
    rw [hnat, hbase]
    change (ConcreteCategory.hom (SimplicialObject.δ S 2)) cs.simplex = m.edge
    exact cs.d₂

instance rightFibrationDataOfRightFibration {p : X ⟶ S} [RightFibration p] :
    RightFibrationData p where
  liftEdge := rightLiftEdgeOfRightFibration
  fillTwoTwo := rightFillTwoTwoOfRightFibration

namespace LeftFibrationData

/-- A left fibration lifts a base inverse of `p f` to a left inverse of `f`. -/
theorem left_inverse {p : X ⟶ S} (hp : LeftFibrationData p)
    {a b : X _⦋0⦌} (f : Edge a b) (hf : Nonempty (f.map p).IsIso) :
    ∃ (f' : Edge b a), Nonempty (Edge.CompStruct f f' (Edge.id a)) ∧
      Nonempty (f'.map p).IsIso := by
  obtain ⟨hf⟩ := hf
  have cs : Edge.CompStruct (f.map p) hf.inv ((Edge.id a).map p) :=
    hf.homInvId.ofEq rfl rfl (by rw [Edge.map_id])
  obtain ⟨f', ⟨c⟩, hf'⟩ := hp.fillTwoZero f (Edge.id a) cs
  exact ⟨f', ⟨c⟩, ⟨hf.isIsoInv.ofEq hf'.symm⟩⟩

end LeftFibrationData

namespace RightFibrationData

/-- A right fibration lifts a base inverse of `p f` to a right inverse of `f`. -/
theorem right_inverse {p : X ⟶ S} (hp : RightFibrationData p)
    {a b : X _⦋0⦌} (f : Edge a b) (hf : Nonempty (f.map p).IsIso) :
    ∃ (f' : Edge b a), Nonempty (Edge.CompStruct f' f (Edge.id b)) ∧
      Nonempty (f'.map p).IsIso := by
  obtain ⟨hf⟩ := hf
  have cs : Edge.CompStruct hf.inv (f.map p) ((Edge.id b).map p) :=
    hf.invHomId.ofEq rfl rfl (by rw [Edge.map_id])
  obtain ⟨f', ⟨c⟩, hf'⟩ := hp.fillTwoTwo (Edge.id b) f cs
  exact ⟨f', ⟨c⟩, ⟨hf.isIsoInv.ofEq hf'.symm⟩⟩

end RightFibrationData

/-- Conservativity through the low-dimensional lift interface for left fibrations. -/
theorem leftFibrationData_conservative {p : X ⟶ S} [Quasicategory X] (hp : LeftFibrationData p)
    {x₀ x₁ : X _⦋0⦌} (g : Edge x₀ x₁) (hg : Nonempty (g.map p).IsIso) :
    Nonempty g.IsIso := by
  obtain ⟨h, ⟨cgh⟩, hh⟩ := hp.left_inverse g hg
  obtain ⟨k, ⟨chk⟩, _⟩ := hp.left_inverse h hh
  have hid0 : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₀).toTruncated =
      𝟙 ({ pt := x₀ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) :=
    SSet.Truncated.HomotopyCategory₂.homMk_id _
  have hid1 : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated =
      𝟙 ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) :=
    SSet.Truncated.HomotopyCategory₂.homMk_id _
  have eGH := cgh.toTruncated.homotopyCategory₂_fac
  rw [hid0] at eGH
  have eHK := chk.toTruncated.homotopyCategory₂_fac
  rw [hid1] at eHK
  have eGK : SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated =
      SSet.Truncated.HomotopyCategory₂.homMk k.toTruncated := by
    rw [← Category.comp_id (SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated),
      ← eHK, ← Category.assoc, eGH, Category.id_comp]
  have eHG : SSet.Truncated.HomotopyCategory₂.homMk h.toTruncated ≫
      SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated =
      SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated := by
    rw [eGK, eHK, hid1]
  have chg : Edge.CompStruct h g (Edge.id x₁) :=
    Edge.CompStruct.ofTruncated
      (SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac eHG)
  exact ⟨{ inv := h, homInvId := cgh, invHomId := chg }⟩

/-- Isofibration property through the lift interface for left fibrations. -/
theorem leftFibrationData_isofibration {p : X ⟶ S} [Quasicategory X] (hp : LeftFibrationData p)
    {x₀ : X _⦋0⦌} {s₁ : S _⦋0⦌} (e : Edge (p.app _ x₀) s₁) (he : Nonempty e.IsIso) :
    ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₁ = s₁ ∧ (e'.map p).edge = e.edge ∧ Nonempty e'.IsIso := by
  obtain ⟨x₁, e', hx, he'⟩ := hp.liftEdge e
  refine ⟨x₁, e', hx, he', ?_⟩
  exact leftFibrationData_conservative hp e' (he.map (fun H => H.ofEq he'.symm))

/-- Conservativity of left fibrations. -/
theorem leftFibration_conservative {p : X ⟶ S} [Quasicategory X] [LeftFibration p]
    {x₀ x₁ : X _⦋0⦌} (g : Edge x₀ x₁) (hg : Nonempty (g.map p).IsIso) :
    Nonempty g.IsIso :=
  leftFibrationData_conservative (leftFibrationDataOfLeftFibration (p := p)) g hg

/-- Isofibration property for left fibrations. -/
theorem leftFibration_isofibration {p : X ⟶ S} [Quasicategory X] [LeftFibration p]
    {x₀ : X _⦋0⦌} {s₁ : S _⦋0⦌} (e : Edge (p.app _ x₀) s₁) (he : Nonempty e.IsIso) :
    ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₁ = s₁ ∧ (e'.map p).edge = e.edge ∧ Nonempty e'.IsIso :=
  leftFibrationData_isofibration (leftFibrationDataOfLeftFibration (p := p)) e he

/-- Simplicial maps preserve invertible edges. -/
theorem leftFibration_preserves_iso (p : X ⟶ S) {x₀ x₁ : X _⦋0⦌}
    {g : Edge x₀ x₁} (hg : Nonempty g.IsIso) : Nonempty (g.map p).IsIso :=
  hg.map (fun I => I.map p)

/-- Conservativity through the low-dimensional lift interface for right fibrations. -/
theorem rightFibrationData_conservative {p : X ⟶ S} [Quasicategory X] (hp : RightFibrationData p)
    {x₀ x₁ : X _⦋0⦌} (g : Edge x₀ x₁) (hg : Nonempty (g.map p).IsIso) :
    Nonempty g.IsIso := by
  obtain ⟨h, ⟨chg⟩, hh⟩ := hp.right_inverse g hg
  obtain ⟨k, ⟨ckh⟩, _⟩ := hp.right_inverse h hh
  have hid0 : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₀).toTruncated =
      𝟙 ({ pt := x₀ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) :=
    SSet.Truncated.HomotopyCategory₂.homMk_id _
  have hid1 : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated =
      𝟙 ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) :=
    SSet.Truncated.HomotopyCategory₂.homMk_id _
  have eHG := chg.toTruncated.homotopyCategory₂_fac
  rw [hid1] at eHG
  have eKH := ckh.toTruncated.homotopyCategory₂_fac
  rw [hid0] at eKH
  have eGK : SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated =
      SSet.Truncated.HomotopyCategory₂.homMk k.toTruncated := by
    rw [← Category.id_comp (SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated),
      ← eKH, Category.assoc, eHG, Category.comp_id]
  have eGH : SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated ≫
      SSet.Truncated.HomotopyCategory₂.homMk h.toTruncated =
      SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₀).toTruncated := by
    rw [eGK, eKH, hid0]
  have cgh : Edge.CompStruct g h (Edge.id x₀) :=
    Edge.CompStruct.ofTruncated
      (SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac eGH)
  exact ⟨{ inv := h, homInvId := cgh, invHomId := chg }⟩

/-- Isofibration property through the lift interface for right fibrations. -/
theorem rightFibrationData_isofibration {p : X ⟶ S} [Quasicategory X] (hp : RightFibrationData p)
    {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌} (e : Edge s₀ (p.app _ x₁)) (he : Nonempty e.IsIso) :
    ∃ (x₀ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₀ = s₀ ∧ (e'.map p).edge = e.edge ∧ Nonempty e'.IsIso := by
  obtain ⟨x₀, e', hx, he'⟩ := hp.liftEdge e
  refine ⟨x₀, e', hx, he', ?_⟩
  exact rightFibrationData_conservative hp e' (he.map (fun H => H.ofEq he'.symm))

/-- Conservativity of right fibrations. -/
theorem rightFibration_conservative {p : X ⟶ S} [Quasicategory X] [RightFibration p]
    {x₀ x₁ : X _⦋0⦌} (g : Edge x₀ x₁) (hg : Nonempty (g.map p).IsIso) :
    Nonempty g.IsIso :=
  rightFibrationData_conservative (rightFibrationDataOfRightFibration (p := p)) g hg

/-- Isofibration property for right fibrations. -/
theorem rightFibration_isofibration {p : X ⟶ S} [Quasicategory X] [RightFibration p]
    {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌} (e : Edge s₀ (p.app _ x₁)) (he : Nonempty e.IsIso) :
    ∃ (x₀ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₀ = s₀ ∧ (e'.map p).edge = e.edge ∧ Nonempty e'.IsIso :=
  rightFibrationData_isofibration (rightFibrationDataOfRightFibration (p := p)) e he

/-- Simplicial maps preserve invertible edges. -/
theorem rightFibration_preserves_iso (p : X ⟶ S) {x₀ x₁ : X _⦋0⦌}
    {g : Edge x₀ x₁} (hg : Nonempty g.IsIso) : Nonempty (g.map p).IsIso :=
  hg.map (fun I => I.map p)

end SSet
