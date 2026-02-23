import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet}
variable {x₀ x₁ x₂ y₀ y₁ y₂ : X _⦋0⦌}

namespace Edge

variable (e : Edge x₀ x₁)
variable (h₀ : x₀ = y₀)
variable (h₁ : x₁ = y₁)

/-- The `1`-simplex of `e.map f`, for `f` a simplicial set morphism, is equal to `f` applied to that edge. -/
lemma map_edge
  (f : X ⟶ Y)
  : (e.map f).edge = f.app _ e.edge
  := rfl

/-- Transports an edge between `x₀` and `x₁` along equalities `xᵢ = yᵢ`. I.e. constructs an edge between the `yᵢ` from an edge between the `xᵢ`. -/
def ofEq
  : Edge y₀ y₁
  where
    edge := e.edge
    src_eq := e.src_eq.trans h₀
    tgt_eq := e.tgt_eq.trans h₁

namespace CompStruct

variable {e₀₁ : Edge x₀ x₁} {f₀₁ : Edge y₀ y₁}
variable {e₁₂ : Edge x₁ x₂} {f₁₂ : Edge y₁ y₂}
variable {e₀₂ : Edge x₀ x₂} {f₀₂ : Edge y₀ y₂}
variable (c : CompStruct e₀₁ e₁₂ e₀₂)

lemma d₂ : X.δ 2 c.simplex = e₀₁.edge := c.toTruncated.d₂
lemma d₀ : X.δ 0 c.simplex = e₁₂.edge := c.toTruncated.d₀
lemma d₁ : X.δ 1 c.simplex = e₀₂.edge := c.toTruncated.d₁

/-- Transports a CompStruct between edges `e₀₁`, `e₁₂` and `e₀₂` along equalities on 1-simplices `eᵢⱼ.edge = fᵢⱼ.edge`. I.e. constructs a `CompStruct` between the `fᵢⱼ` from a `CompStruct` between the `eᵢⱼ`. -/
def ofEq
  (h₀₁ : e₀₁.edge = f₀₁.edge)
  (h₁₂ : e₁₂.edge = f₁₂.edge)
  (h₀₂ : e₀₂.edge = f₀₂.edge)
  : CompStruct f₀₁ f₁₂ f₀₂
  where
    simplex := c.simplex
    d₂ := c.d₂.trans h₀₁
    d₀ := c.d₀.trans h₁₂
    d₁ := c.d₁.trans h₀₂

end CompStruct

/-- For `hom` an edge, `IsIso hom` encodes that there is a backward edge `inv`, and there are 2-simplices witnessing that `hom` and `inv` compose to the identity on their endpoints. This means that `hom` becomes an isomorphism in the homotopy category. -/
structure IsIso (hom : Edge x₀ x₁) where
  inv            : Edge x₁ x₀
  homInvId     : Edge.CompStruct hom inv (Edge.id x₀)
  invHomId     : Edge.CompStruct inv hom (Edge.id x₁)

namespace IsIso

lemma id_comp_id_aux
  {l m n : ℕ}
  {f : ⦋n⦌ ⟶ ⦋m⦌}
  {g : ⦋m⦌ ⟶ ⦋l⦌}
  {h : ⦋n⦌ ⟶ ⦋l⦌}
  (x : X _⦋l⦌)
  (e : f ≫ g = h)
  : X.map f.op (X.map g.op x) = X.map h.op x
  := by
    rw [← e, op_comp, X.map_comp]
    rfl

/-- The identity edge on a point, composed with itself, gives the identity. -/
def idCompId (x : X _⦋0⦌) : Edge.CompStruct (Edge.id x) (Edge.id x) (Edge.id x) := .mk
  (X.map (Opposite.op (SimplexCategory.Hom.mk ⟨fun a ↦ 0, monotone_const⟩)) x)
  (by apply id_comp_id_aux; decide)
  (by apply id_comp_id_aux; decide)
  (by apply id_comp_id_aux; decide)

/-- The identity edge is an isomorphism. -/
def isIsoId (x : X _⦋0⦌) : IsIso (Edge.id x) where
  inv := Edge.id x
  homInvId := idCompId x
  invHomId := idCompId x

/-- The inverse of an isomorphism is an isomorphism. -/
def isIsoInv {hom : Edge x₀ x₁} (I : IsIso hom) : IsIso I.inv where
  inv := hom
  homInvId := I.invHomId
  invHomId := I.homInvId

/-- The image of an isomorphism under an SSet morphism is an isomorphism. -/
def map {hom : Edge x₀ x₁} (I : IsIso hom) (f : X ⟶ Y)
  : IsIso (Edge.map hom f) where
  inv := Edge.map I.inv f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

/-- Transports a proof of isomorphism for `hom` along an equality of 1-simplices `hom = hom'`. I.e. shows that `hom'` is an isomorphism from an isomorphism proof of `hom`. -/
def ofEq {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁} (I : IsIso hom) (hhom : hom.edge = hom'.edge)
  : IsIso hom'
  where
    inv := I.inv.ofEq (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq]) (by rw [← hom.src_eq, hhom, hom'.src_eq])
    homInvId := I.homInvId.ofEq hhom rfl (by rw [← hom.src_eq, hhom, hom'.src_eq])
    invHomId := I.invHomId.ofEq rfl hhom (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])

end IsIso

end Edge

end SSet
