/-
Copyright (c) 2026 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/

import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated

open CategoryTheory Simplicial SSet.Truncated SimplexCategory.Truncated

namespace SSet

variable {X Y : SSet} {x₀ x₁ x₂ y₀ y₁ : X _⦋0⦌}

namespace Edge

/-- Compatibility name for the inverse-edge data supplied by mathlib. -/
abbrev IsIso (hom : Edge x₀ x₁) := InvStruct hom

namespace IsIso

/-- The identity edge is an isomorphism edge. -/
abbrev isIsoId (x : X _⦋0⦌) : IsIso (Edge.id x) :=
  InvStruct.invStructId x

/-- The inverse of an isomorphism edge is an isomorphism edge. -/
abbrev isIsoInv {hom : Edge x₀ x₁} (I : IsIso hom) : IsIso I.inv :=
  InvStruct.invStructInv I

/-- The image of an isomorphism edge under a simplicial-set morphism is an isomorphism edge. -/
abbrev map {hom : Edge x₀ x₁} (I : IsIso hom) (f : X ⟶ Y) : IsIso (hom.map f) :=
  InvStruct.map I f

/-- Transports an isomorphism-edge witness along an equality of underlying edges. -/
abbrev ofEq {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁} (I : IsIso hom)
    (hhom : hom.edge = hom'.edge) : IsIso hom' :=
  InvStruct.ofEq I hhom

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
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated := by
          rw [Category.id_comp]
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
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated := by
          rw [Category.id_comp]
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
            SSet.Truncated.HomotopyCategory₂.homMk hf.inv.toTruncated := by
          rw [Category.id_comp]
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
            SSet.Truncated.HomotopyCategory₂.homMk g.toTruncated := by
          rw [Category.id_comp]
      _ = SSet.Truncated.HomotopyCategory₂.homMk (Edge.id x₂).toTruncated := by
          rw [hg.invHomId.toTruncated.homotopyCategory₂_fac]

end IsIso

end Edge

end SSet
