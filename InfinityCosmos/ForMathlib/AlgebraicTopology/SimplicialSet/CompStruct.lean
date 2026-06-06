import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

open CategoryTheory Simplicial

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

end Edge

end SSet
