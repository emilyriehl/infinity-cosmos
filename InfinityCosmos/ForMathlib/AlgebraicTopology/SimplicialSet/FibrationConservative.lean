import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.IsoCore
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.LeftFibration

open CategoryTheory Simplicial

universe u

namespace SSet

variable {X S : SSet.{u}}

/-- The low-dimensional lift data used by the conservativity proof for left fibrations. -/
structure LeftFibrationData (p : X ⟶ S) where
  liftEdge : ∀ {x₀ : X _⦋0⦌} {s₁ : S _⦋0⦌} (e : Edge (p.app _ x₀) s₁),
    ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁), p.app _ x₁ = s₁ ∧ (e'.map p).edge = e.edge
  fillTwoZero : ∀ {x₀ x₁ x₂ : X _⦋0⦌} (e : Edge x₀ x₁) (d : Edge x₀ x₂)
      {m : Edge (p.app _ x₁) (p.app _ x₂)}
      (_cs : Edge.CompStruct (e.map p) m (d.map p)),
    ∃ (k : Edge x₁ x₂), Nonempty (Edge.CompStruct e k d) ∧ (k.map p).edge = m.edge

/-- The low-dimensional lift data used by the conservativity proof for right fibrations. -/
structure RightFibrationData (p : X ⟶ S) where
  liftEdge : ∀ {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌} (e : Edge s₀ (p.app _ x₁)),
    ∃ (x₀ : X _⦋0⦌) (e' : Edge x₀ x₁), p.app _ x₀ = s₀ ∧ (e'.map p).edge = e.edge
  fillTwoTwo : ∀ {x₀ x₁ x₂ : X _⦋0⦌} (d : Edge x₀ x₂) (e : Edge x₁ x₂)
      {m : Edge (p.app _ x₀) (p.app _ x₁)}
      (_cs : Edge.CompStruct m (e.map p) (d.map p)),
    ∃ (k : Edge x₀ x₁), Nonempty (Edge.CompStruct k e d) ∧ (k.map p).edge = m.edge

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

/-- Conservativity of left fibrations, expressed through the low-dimensional lift interface. -/
theorem leftFibration_conservative {p : X ⟶ S} [Quasicategory X] (hp : LeftFibrationData p)
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

/-- Isofibration property for left fibrations, expressed through the lift interface. -/
theorem leftFibration_isofibration {p : X ⟶ S} [Quasicategory X] (hp : LeftFibrationData p)
    {x₀ : X _⦋0⦌} {s₁ : S _⦋0⦌} (e : Edge (p.app _ x₀) s₁) (he : Nonempty e.IsIso) :
    ∃ (x₁ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₁ = s₁ ∧ (e'.map p).edge = e.edge ∧ Nonempty e'.IsIso := by
  obtain ⟨x₁, e', hx, he'⟩ := hp.liftEdge e
  refine ⟨x₁, e', hx, he', ?_⟩
  exact leftFibration_conservative hp e' (he.map (fun H => H.ofEq he'.symm))

/-- Simplicial maps preserve invertible edges. -/
theorem leftFibration_preserves_iso (p : X ⟶ S) {x₀ x₁ : X _⦋0⦌}
    {g : Edge x₀ x₁} (hg : Nonempty g.IsIso) : Nonempty (g.map p).IsIso :=
  hg.map (fun I => I.map p)

/-- Conservativity of right fibrations, expressed through the low-dimensional lift interface. -/
theorem rightFibration_conservative {p : X ⟶ S} [Quasicategory X] (hp : RightFibrationData p)
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

/-- Isofibration property for right fibrations, expressed through the lift interface. -/
theorem rightFibration_isofibration {p : X ⟶ S} [Quasicategory X] (hp : RightFibrationData p)
    {x₁ : X _⦋0⦌} {s₀ : S _⦋0⦌} (e : Edge s₀ (p.app _ x₁)) (he : Nonempty e.IsIso) :
    ∃ (x₀ : X _⦋0⦌) (e' : Edge x₀ x₁),
      p.app _ x₀ = s₀ ∧ (e'.map p).edge = e.edge ∧ Nonempty e'.IsIso := by
  obtain ⟨x₀, e', hx, he'⟩ := hp.liftEdge e
  refine ⟨x₀, e', hx, he', ?_⟩
  exact rightFibration_conservative hp e' (he.map (fun H => H.ofEq he'.symm))

/-- Simplicial maps preserve invertible edges. -/
theorem rightFibration_preserves_iso (p : X ⟶ S) {x₀ x₁ : X _⦋0⦌}
    {g : Edge x₀ x₁} (hg : Nonempty g.IsIso) : Nonempty (g.map p).IsIso :=
  hg.map (fun I => I.map p)

end SSet
