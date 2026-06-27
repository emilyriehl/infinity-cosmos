import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated

open CategoryTheory Simplicial SSet.Truncated SimplexCategory.Truncated

namespace SSet

variable {X Y : SSet} {x₀ x₁ x₂ y₀ y₁ y₂ : X _⦋0⦌}

namespace Edge

variable (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁)

/-- Transports an edge along equalities on vertices. -/
def ofEq : Edge y₀ y₁ where
  edge := e.edge
  src_eq := e.src_eq.trans h₀
  tgt_eq := e.tgt_eq.trans h₁

namespace CompStruct

variable {e₀₁ : Edge x₀ x₁} {f₀₁ : Edge y₀ y₁}
  {e₁₂ : Edge x₁ x₂} {f₁₂ : Edge y₁ y₂}
  {e₀₂ : Edge x₀ x₂} {f₀₂ : Edge y₀ y₂}
  (c : CompStruct e₀₁ e₁₂ e₀₂)

/-- Transports a `CompStruct` along equalities on 1-simplices. -/
def ofEq (h₀₁ : e₀₁.edge = f₀₁.edge) (h₁₂ : e₁₂.edge = f₁₂.edge)
    (h₀₂ : e₀₂.edge = f₀₂.edge) : CompStruct f₀₁ f₁₂ f₀₂ where
  simplex := c.simplex
  d₂ := c.d₂.trans h₀₁
  d₀ := c.d₀.trans h₁₂
  d₁ := c.d₁.trans h₀₂

end CompStruct

/-- `IsIso hom` encodes that `hom` has an inverse edge with 2-simplices witnessing
composition to identity edges, making `hom` an isomorphism in the homotopy category. -/
structure IsIso (hom : Edge x₀ x₁) where
  inv : Edge x₁ x₀
  homInvId : Edge.CompStruct hom inv (Edge.id x₀)
  invHomId : Edge.CompStruct inv hom (Edge.id x₁)

namespace IsIso

lemma id_comp_id_aux {l m n : ℕ} {f : ⦋n⦌ ⟶ ⦋m⦌} {g : ⦋m⦌ ⟶ ⦋l⦌} {h : ⦋n⦌ ⟶ ⦋l⦌}
    (x : X _⦋l⦌) (e : f ≫ g = h) : X.map f.op (X.map g.op x) = X.map h.op x := by
  subst e; rw [op_comp, X.map_comp]; rfl

/-- The identity edge composed with itself gives the identity. -/
def idCompId (x : X _⦋0⦌) : Edge.CompStruct (Edge.id x) (Edge.id x) (Edge.id x) :=
  .idComp (.id x)

/-- The identity edge is an isomorphism. -/
def isIsoId (x : X _⦋0⦌) : IsIso (Edge.id x) where
  inv := .id x
  homInvId := idCompId x
  invHomId := idCompId x

/-- The inverse of an isomorphism is an isomorphism. -/
def isIsoInv {hom : Edge x₀ x₁} (I : IsIso hom) : IsIso I.inv where
  inv := hom
  homInvId := I.invHomId
  invHomId := I.homInvId

/-- The image of an isomorphism under an SSet morphism is an isomorphism. -/
def map {hom : Edge x₀ x₁} (I : IsIso hom) (f : X ⟶ Y) : IsIso (hom.map f) where
  inv := I.inv.map f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

/-- Transports an isomorphism proof along an equality of 1-simplices. -/
def ofEq {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁} (I : IsIso hom)
    (hhom : hom.edge = hom'.edge) : IsIso hom' where
  inv := I.inv.ofEq (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])
    (by rw [← hom.src_eq, hhom, hom'.src_eq])
  homInvId := I.homInvId.ofEq hhom rfl (by rw [← hom.src_eq, hhom, hom'.src_eq])
  invHomId := I.invHomId.ofEq rfl hhom (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])

end IsIso

variable [Quasicategory X]

/-- The chosen composite of two consecutive edges in a quasi-category. -/
noncomputable def comp (f : Edge x₀ x₁) (g : Edge x₁ x₂) : Edge x₀ x₂ :=
  Edge.ofTruncated (SSet.Truncated.Edge.comp f.toTruncated g.toTruncated)

/-- The chosen 2-simplex witnessing `Edge.comp`. -/
noncomputable def compStruct (f : Edge x₀ x₁) (g : Edge x₁ x₂) :
    Edge.CompStruct f g (comp f g) :=
  Edge.CompStruct.ofTruncated (SSet.Truncated.Edge.compStruct f.toTruncated g.toTruncated)

namespace IsIso

/-- The composite of isomorphism edges is an isomorphism edge. -/
noncomputable def comp {f : Edge x₀ x₁} {g : Edge x₁ x₂} (hf : IsIso f) (hg : IsIso g) :
    IsIso (Edge.comp f g) where
  inv := Edge.comp hg.inv hf.inv
  homInvId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have hid₁ : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated =
        𝟙 ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) := by
      exact SSet.Truncated.HomotopyCategory₂.homMk_id
        ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X))
    calc
      SSet.Truncated.HomotopyCategory₂.homMk (Edge.comp f g).toTruncated ≫
          SSet.Truncated.HomotopyCategory₂.homMk (Edge.comp hg.inv hf.inv).toTruncated =
        (SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) ≫
          (SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          rw [← (Edge.compStruct f g).toTruncated.homotopyCategory₂_fac]
          rw [← (Edge.compStruct hg.inv hf.inv).toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            ((SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated) ≫
              SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          simp only [Category.assoc]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            (SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          rw [hg.homInvId.toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            (𝟙 _ ≫ SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          rw [hid₁]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated := by rw [Category.id_comp]
      _ = SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₀).toTruncated := by
          rw [hf.homInvId.toTruncated.homotopyCategory₂_fac]
  invHomId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have hid₁ : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated =
        𝟙 ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) := by
      exact SSet.Truncated.HomotopyCategory₂.homMk_id
        ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X))
    calc
      SSet.Truncated.HomotopyCategory₂.homMk (Edge.comp hg.inv hf.inv).toTruncated ≫
          SSet.Truncated.HomotopyCategory₂.homMk (Edge.comp f g).toTruncated =
        (SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) ≫
          (SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          rw [← (Edge.compStruct hg.inv hf.inv).toTruncated.homotopyCategory₂_fac]
          rw [← (Edge.compStruct f g).toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            ((SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated) ≫
              SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          simp only [Category.assoc]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            (SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          rw [hf.invHomId.toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            (𝟙 _ ≫ SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          rw [hid₁]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated := by rw [Category.id_comp]
      _ = SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₂).toTruncated := by
          rw [hg.invHomId.toTruncated.homotopyCategory₂_fac]

/-- If `h` is a composite of `f` and `g`, and both `f` and `g` are isomorphism edges,
then `h` is an isomorphism edge. -/
noncomputable def ofCompStruct {f : Edge x₀ x₁} {g : Edge x₁ x₂} {h : Edge x₀ x₂}
    (c : Edge.CompStruct f g h) (hf : IsIso f) (hg : IsIso g) : IsIso h where
  inv := Edge.comp hg.inv hf.inv
  homInvId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have hid₁ : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated =
        𝟙 ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) := by
      exact SSet.Truncated.HomotopyCategory₂.homMk_id
        ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X))
    calc
      SSet.Truncated.HomotopyCategory₂.homMk h.toTruncated ≫
          SSet.Truncated.HomotopyCategory₂.homMk (Edge.comp hg.inv hf.inv).toTruncated =
        (SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) ≫
          (SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          rw [c.toTruncated.homotopyCategory₂_fac]
          rw [← (Edge.compStruct hg.inv hf.inv).toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            ((SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated) ≫
              SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          simp only [Category.assoc]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            (SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          rw [hg.homInvId.toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            (𝟙 _ ≫ SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) := by
          rw [hid₁]
      _ = SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated := by rw [Category.id_comp]
      _ = SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₀).toTruncated := by
          rw [hf.homInvId.toTruncated.homotopyCategory₂_fac]
  invHomId := by
    apply Edge.CompStruct.ofTruncated
    apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    have hid₁ : SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated =
        𝟙 ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X)) := by
      exact SSet.Truncated.HomotopyCategory₂.homMk_id
        ({ pt := x₁ } : SSet.Truncated.HomotopyCategory₂ ((truncation 2).obj X))
    calc
      SSet.Truncated.HomotopyCategory₂.homMk (Edge.comp hg.inv hf.inv).toTruncated ≫
          SSet.Truncated.HomotopyCategory₂.homMk h.toTruncated =
        (SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated) ≫
          (SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          rw [c.toTruncated.homotopyCategory₂_fac]
          rw [← (Edge.compStruct hg.inv hf.inv).toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            ((SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk f.toTruncated) ≫
              SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          simp only [Category.assoc]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            (SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₁).toTruncated ≫
              SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          rw [hf.invHomId.toTruncated.homotopyCategory₂_fac]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            (𝟙 _ ≫ SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated) := by
          rw [hid₁]
      _ = SSet.Truncated.HomotopyCategory₂.homMk hg.inv.toTruncated ≫
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated := by rw [Category.id_comp]
      _ = SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₂).toTruncated := by
          rw [hg.invHomId.toTruncated.homotopyCategory₂_fac]

end IsIso

end Edge

end SSet
