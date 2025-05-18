/-
Copyright (c) 2025 Julian Komaromy, Emily Riehl, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy, Emily Riehl, Joël Riou
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.Quasicategory.Basic
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex

open Simplicial SimplexCategory CategoryTheory
  SimplicialObject SSet stdSimplex

namespace SSet
/--
`Edge x₀ x₁` is a wrapper around a 1-simplex in a simplicial set with source `x₀` and target `x₁`.
-/
@[ext]
structure Edge {X : SSet} (x₀ : X _⦋0⦌) (x₁ : X _⦋0⦌) where
  simplex : X _⦋1⦌
  src_eq : X.δ 1 simplex = x₀ := by aesop_cat
  tgt_eq : X.δ 0 simplex = x₁ := by aesop_cat

abbrev edgeMap {X : SSet} {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) : Δ[1] ⟶ X :=
  yonedaEquiv.symm e.simplex

/-- Degenerate edges define identities. -/
def Edge.id {X : SSet} (x : X _⦋0⦌) : Edge x x where
  simplex := X.σ 0 x
  src_eq := by
    erw [δ_comp_σ_succ_apply 0]
  tgt_eq := by
    erw [δ_comp_σ_self_apply 0]

/-- More generally, equalities can be promoted to edges. -/
def Edge.ofEq {X : SSet} {x₀ x₁ : X _⦋0⦌} (h : x₀ = x₁) : Edge x₀ x₁ := h ▸ id x₀

/--
`CompStruct e₀₁ e₁₂ e₀₂` is a wrapper around a 2-simplex in a simplicial set
with edges `e₀₁`, `e₁₂`, `e₀₂` in the obvious configuration.
-/
@[ext]
structure CompStruct {X : SSet} {x₀ x₁ x₂ : X _⦋0⦌}
    (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) where
  simplex : X _⦋2⦌
  h₀₁ : X.δ 2 simplex = e₀₁.simplex := by aesop_cat
  h₁₂ : X.δ 0 simplex = e₁₂.simplex := by aesop_cat
  h₀₂ : X.δ 1 simplex = e₀₂.simplex := by aesop_cat

namespace CompStruct

/-- A degeneracy witness that post composition with the identity is the identity. -/
def compId {X : SSet} {x₀ x₁ : X _⦋0⦌} (f : Edge x₀ x₁) :
    CompStruct f (Edge.id x₁) f where
  simplex := X.σ 1 f.simplex
  h₀₁ := by
    erw [δ_comp_σ_succ_apply 1]
  h₁₂ := by
    erw [δ_comp_σ_of_le_apply (i := 0) (j := 1) (Fin.zero_le _), f.tgt_eq]
    dsimp [Edge.id]
  h₀₂ := by
    erw [δ_comp_σ_self_apply 1]

/-- A degeneracy witness that pre composition with the identity is the identity. -/
def idComp {X : SSet} {x₀ x₁ : X _⦋0⦌} (f : Edge x₀ x₁) :
    CompStruct (Edge.id x₀) f f where
  simplex := X.σ 0 f.simplex
  h₀₁ := by
    erw [δ_comp_σ_of_gt_apply (i := 1) (j := 0) (Fin.zero_lt_one), f.src_eq]
    dsimp [Edge.id]
  h₁₂ := by
    erw [δ_comp_σ_self_apply 0]
  h₀₂ := by
    erw [δ_comp_σ_succ_apply 0]

end CompStruct

namespace horn₃₁
open CompStruct Edge

variable {X : SSet}
variable {x₀ x₁ x₂ x₃ : X _⦋0⦌}
  {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
  {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
  (δ₃ : CompStruct e₀₁ e₁₂ e₀₂)
  (δ₀ : CompStruct e₁₂ e₂₃ e₁₃)
  (δ₂ : CompStruct e₀₁ e₁₃ e₀₃)

abbrev ι₀ : Δ[2] ⟶ Λ[3, 1] := yonedaEquiv.symm (horn.face 1 0 (by norm_num))
abbrev ι₂ : Δ[2] ⟶ Λ[3, 1] := yonedaEquiv.symm (horn.face 1 2 (by decide))
abbrev ι₃ : Δ[2] ⟶ Λ[3, 1] := yonedaEquiv.symm (horn.face 1 3 (by decide))

lemma incl₀ : ι₀ ≫ Λ[3, 1].ι = stdSimplex.δ 0 := rfl
lemma incl₂ : ι₂ ≫ Λ[3, 1].ι = stdSimplex.δ 2 := rfl
lemma incl₃ : ι₃ ≫ Λ[3, 1].ι = stdSimplex.δ 3 := rfl


/-- Index types for the left and right coproducts in the multicoequalizer that defines the horn `Λ[3 , 1] : SSet`. -/
def R := { x : Fin 4 // x ≠ 1 }
def L := { p : R × R // p.1.val < p.2.val }

/-- The shape of the multicoequalizer that defines the horn `Λ[3 , 1] : SSet`. -/
def J : Limits.MultispanShape where
  L := L
  R := R
  fst p := p.val.1
  snd p := p.val.2

/-- The structure required to define the multicoequalizer in simplicial sets. -/
def multispanIndex : Limits.MultispanIndex J SSet where
  left  _ := Δ[1]
  right _ := Δ[2]
  fst p := stdSimplex.map (δ (Fin.pred p.val.2.val (Fin.ne_zero_of_lt p.property)).castSucc)
  snd p := stdSimplex.map (δ p.val.1.val)

/-- Choose the `i`-th face from the given faces for `i : R` as a map `Δ[2] ⟶ X`. -/
def chooseFace (i : R) : (Δ[2] ⟶ X) := match i with
  | ⟨0, _⟩ => yonedaEquiv.symm δ₀.simplex
  | ⟨1, _⟩ => by contradiction
  | ⟨2, _⟩ => yonedaEquiv.symm δ₂.simplex
  | ⟨3, _⟩ => yonedaEquiv.symm δ₃.simplex

/-- Choose the `i`-th face from the given faces for `i : R` as a 2-simplex in `X`. -/
def chooseFace' (i : R) : X _⦋2⦌ := match i with
  | ⟨0, _⟩ => δ₀.simplex
  | ⟨1, _⟩ => by contradiction
  | ⟨2, _⟩ => δ₂.simplex
  | ⟨3, _⟩ => δ₃.simplex

abbrev i₀ : R := ⟨0, by omega⟩
abbrev i₂ : R := ⟨2, by omega⟩
abbrev i₃ : R := ⟨3, by omega⟩

/-- The components of the cone under the multicofork diagram. -/
def π : R → (Δ[2] ⟶ Λ[3, 1]) := fun ⟨x, h⟩ ↦ yonedaEquiv.symm (horn.face 1 x h)

/-- Commutativity of the cone under the multicofork diagram. -/
lemma fork_comm : ∀ p : L,
    multispanIndex.fst p ≫ π (J.fst p) = multispanIndex.snd p ≫ π (J.snd p) := by
  rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij⟩
  dsimp only [multispanIndex, J, π]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    apply (instMonoι Λ[3, 1]).right_cancellation
    dsimp only [Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, ne_eq, Fin.zero_eta, Fin.reducePred,
      Fin.castSucc_one, Fin.val_one, Fin.val_zero]
    rw [Category.assoc, Category.assoc]
    symm
  exact @stdSimplex.δ_comp_δ _ _ _ 0 1 (by norm_num)
  exact @stdSimplex.δ_comp_δ _ _ _ 0 2 (by norm_num)
  exact @stdSimplex.δ_comp_δ _ _ _ 2 2 (by norm_num)

def multicofork := Limits.Multicofork.ofπ multispanIndex Λ[3, 1] π fork_comm

-- TODO this should be also handled by Joel's PR (e.g. mathlib pr #23872)
def isMulticoeq : Limits.IsColimit multicofork := by sorry

/-- The multicofork `⨿ Δ[1] ⇉ ⨿ Δ[2] ⟶ X` defined by sending `Δ[2]`s to each of the three faces `δ₃`, `δ₀`, `δ₂`. -/
def multicoforkFromFaces : Limits.Multicofork multispanIndex :=
  Limits.Multicofork.ofπ multispanIndex X (chooseFace δ₃ δ₀ δ₂)
    (by
      rintro ⟨⟨⟨i, i_ne_1⟩, ⟨j, j_ne_1⟩⟩, i_lt_j⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals
        dsimp [J, multispanIndex, chooseFace]
        rw [map_comp_yonedaEquiv_symm, map_comp_yonedaEquiv_symm]
        congr 1
      -- rw still doesn't work
      . exact Eq.trans δ₀.h₀₂ δ₂.h₁₂.symm
      . exact Eq.trans δ₀.h₀₁ δ₃.h₁₂.symm
      . exact Eq.trans δ₂.h₀₁ δ₃.h₀₁.symm)

/--
Use the fact that `Λ[3, 1]` is the coequalizer of `multicoforkFromFaces` allows the
construction of a map `Λ[3, 1].toSSet ⟶ X`.
-/
def fromFaces : Λ[3, 1].toSSet ⟶ X :=
  Limits.IsColimit.desc horn₃₁.isMulticoeq (multicoforkFromFaces δ₃ δ₀ δ₂)

/-
A group of lemmas stating that the faces of the simplex `Δ[3] ⟶ S` extending the horn
`fromFaces δ₃ δ₀ δ₂ : Λ[3, 1] ⟶ X` are as expected.
-/
lemma horn_extension_face₀ {g : Δ[3] ⟶ X} (comm : fromFaces δ₃ δ₀ δ₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm δ₀.simplex = stdSimplex.δ 0 ≫ g := by
  have : ι₀ ≫ (fromFaces δ₃ δ₀ δ₂) =
            yonedaEquiv.symm δ₀.simplex :=
    isMulticoeq.fac (multicoforkFromFaces δ₃ δ₀ δ₂) (.right ⟨0, by omega⟩)
  rw [← this, comm, ← Category.assoc, incl₀]

lemma horn_extension_face₂ {g : Δ[3] ⟶ X} (comm : fromFaces δ₃ δ₀ δ₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm δ₂.simplex = stdSimplex.δ 2 ≫ g := by
  have : ι₂ ≫ (fromFaces δ₃ δ₀ δ₂) = yonedaEquiv.symm δ₂.simplex :=
    isMulticoeq.fac (multicoforkFromFaces δ₃ δ₀ δ₂) (.right ⟨2, by omega⟩)
  rw [← this, comm, ← Category.assoc, incl₂]

lemma horn_extension_face₃ {g : Δ[3] ⟶ X} (comm : fromFaces δ₃ δ₀ δ₂ = Λ[3, 1].ι ≫ g) :
    yonedaEquiv.symm δ₃.simplex = stdSimplex.δ 3 ≫ g := by
  have : ι₃ ≫ (fromFaces δ₃ δ₀ δ₂) = yonedaEquiv.symm δ₃.simplex :=
    isMulticoeq.fac (multicoforkFromFaces δ₃ δ₀ δ₂) (.right ⟨3, by omega⟩)
  rw [← this, comm, ← Category.assoc, incl₃]

/--
Given a map `Δ[3] ⟶ X` extending the horn given by `fromFaces`, obtain a 2-simplex
bounded by edges `e₀₂`, `e₂₃` and `e₀₃`. -/
def fromHornExtension (g : Δ[3] ⟶ X) (comm : fromFaces δ₃ δ₀ δ₂ = Λ[3, 1].ι ≫ g) :
    (CompStruct e₀₂ e₂₃ e₀₃) where
  simplex := X.δ 1 (yonedaEquiv g)
  h₀₁ := by
    rw [← δ₃.h₀₂]
    erw [← δ_comp_δ_apply (i := 1) (j := 2) (Fin.coe_sub_iff_le.mp rfl)]
    rw [push_yonedaEquiv' (horn_extension_face₃ δ₃ δ₀ δ₂ comm)]
    rfl
  h₁₂ := by
    rw [← δ₀.h₁₂]
    erw [δ_comp_δ_apply (i := 0) (j := 0) (Fin.zero_le _)]
    rw [push_yonedaEquiv' (horn_extension_face₀ δ₃ δ₀ δ₂ comm)]
    rfl
  h₀₂ := by
    rw [← δ₂.h₀₂]
    erw [← δ_comp_δ_apply (i := 1) (j := 1) (by simp)]
    rw [push_yonedaEquiv' (horn_extension_face₂ δ₃ δ₀ δ₂ comm)]
    rfl

end horn₃₁

structure AlgebraicQuasicategory (S : SSet) where
  hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : (Λ[n+2, i] : SSet) ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n+2)), Δ[n+2] ⟶ S
  hornFilling_comm' :  ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : (Λ[n+2, i] : SSet) ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
    σ₀ = Λ[n + 2, i].ι ≫ hornFilling' σ₀ _h0 _hn

namespace AlgebraicQuasicategory

def hornFilling {S : SSet} (Q : AlgebraicQuasicategory S) ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet) ⟶ S) : Δ[n] ⟶ S := by
  cases n using Nat.casesAuxOn with
  | zero => simp [Fin.lt_iff_val_lt_val] at hn
  | succ n =>
  cases n using Nat.casesAuxOn with
  | zero =>
    simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_last, zero_add, Nat.lt_one_iff] at h0 hn
    simp [hn] at h0
  | succ n => exact Q.hornFilling' σ₀ h0 hn

def hornFilling_comm {S : SSet} (Q : AlgebraicQuasicategory S) ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet) ⟶ S) : σ₀ = Λ[n, i].ι ≫ (hornFilling Q h0 hn σ₀) := by
  cases n using Nat.casesAuxOn with
  | zero => simp [Fin.lt_iff_val_lt_val] at hn
  | succ n =>
  cases n using Nat.casesAuxOn with
  | zero =>
    simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_last, zero_add, Nat.lt_one_iff] at h0 hn
    simp [hn] at h0
  | succ n => exact Q.hornFilling_comm' σ₀ h0 hn

end AlgebraicQuasicategory

open AlgebraicQuasicategory

namespace CompStruct

variable {S : SSet} (Q : AlgebraicQuasicategory S) {x₀ x₁ x₂ x₃ : S _⦋0⦌}

def assoc {f₀₁ : Edge x₀ x₁} {f₁₂ : Edge x₁ x₂} {f₂₃ : Edge x₂ x₃}
    {f₀₂ : Edge x₀ x₂} {f₁₃ : Edge x₁ x₃} {f₀₃ : Edge x₀ x₃}
    (δ₃ : CompStruct f₀₁ f₁₂ f₀₂) (δ₀ : CompStruct f₁₂ f₂₃ f₁₃)
    (δ₂ : CompStruct f₀₁ f₁₃ f₀₃) : (CompStruct f₀₂ f₂₃ f₀₃) := by
  let g : Δ[3] ⟶ S := hornFilling Q Fin.zero_lt_one (by simp) (horn₃₁.fromFaces δ₃ δ₀ δ₂)
  let h : horn₃₁.fromFaces δ₃ δ₀ δ₂ = Λ[2 + 1, 1].ι ≫ g := hornFilling_comm Q Fin.zero_lt_one (by simp) (horn₃₁.fromFaces δ₃ δ₀ δ₂)
  exact horn₃₁.fromHornExtension δ₃ δ₀ δ₂ g h

-- TODO: Redo everything above for Λ[3, 2] horns.
def assoc' (Q : AlgebraicQuasicategory S)
    {f₀₁ : Edge x₀ x₁} {f₁₂ : Edge x₁ x₂} {f₂₃ : Edge x₂ x₃}
    {f₀₂ : Edge x₀ x₂} {f₁₃ : Edge x₁ x₃} {f₀₃ : Edge x₀ x₃}
    (δ₃ : CompStruct f₀₁ f₁₂ f₀₂) (δ₀ : CompStruct f₁₂ f₂₃ f₁₃)
    (δ₁ : CompStruct f₀₂ f₂₃ f₀₃) : CompStruct f₀₁ f₁₃ f₀₃ := sorry

end CompStruct


section edgeHomotopy
variable {X : SSet} {x₀ x₁ : X _⦋0⦌} (p q r : Edge x₀ x₁)

/-- A composition structure involving a degenerate final edge is a left homotopy. -/
abbrev HomotopyL := CompStruct p (Edge.id x₁) q

/-- A composition structure involving a degenerate initial edge is a right homotopy. -/
abbrev HomotopyR := CompStruct (Edge.id x₀) p q

/-- Two edges are left homotopic if there exists a left homotopy. -/
def homotopicL : Prop :=
    Nonempty (HomotopyL p q)

/-- Two edges are right homotopic if there exists a right homotopy. -/
def HomotopicR : Prop :=
    Nonempty (HomotopyR p q)

/-- Left homotopy is reflexive. -/
def HomotopyL.refl : HomotopyL p p := CompStruct.compId p

/-- Right homotopy is reflexive. -/
def HomotopyR.refl : HomotopyR p p := CompStruct.idComp p

/-- Equal edges are left homotopic. -/
def HomotopyL.ofEq (h : p = q) : HomotopyL p q := h ▸ HomotopyL.refl p

/-- Equal edges are right homotopic. -/
def HomotopyR.ofEq (h : p = q) : HomotopyR p q := h ▸ HomotopyR.refl p

section quasicategory
variable (Q : AlgebraicQuasicategory X)
variable {p q r : Edge x₀ x₁}

/-- In a quasi-category, the left homotopy relation is symmetric. -/
def HomotopyL.symm (h : HomotopyL p q) : HomotopyL q p :=
  CompStruct.assoc Q h (CompStruct.compId _) (CompStruct.compId p)

/-- In a quasi-category, the right homotopy relation is symmetric. -/
def HomotopyR.symm (h : HomotopyR p q) : HomotopyR q p :=
  CompStruct.assoc' Q (CompStruct.idComp _) h (CompStruct.idComp p)

/-- In a quasi-category, left homotopy implies right homotopy. -/
def HomotopyL.homotopyR (h : HomotopyL p q) : HomotopyR p q :=
  HomotopyR.symm Q (CompStruct.assoc' Q (CompStruct.idComp p) h (CompStruct.compId p))

/-- In a quasi-category, right homotopy implies left homotopy. -/
def HomotopyR.homotopyL (h : HomotopyR p q) : HomotopyL p q :=
  HomotopyL.symm Q (CompStruct.assoc Q h (CompStruct.compId p) (CompStruct.idComp p))

/-- In a quasi-category, the left homotopy relation is transitive. -/
def HomotopyL.trans (h : HomotopyL p q) (h' : HomotopyL q r) :
    HomotopyL p r :=
  CompStruct.assoc Q (CompStruct.idComp p) h (HomotopyL.homotopyR Q h')

/-- In a quasi-category, the right homotopy relation is transitive. -/
def HomotopyR.trans (h : HomotopyR p q) (h' : HomotopyR q r) :
    HomotopyR p r :=
  CompStruct.assoc' Q h (CompStruct.compId p) (HomotopyR.homotopyL Q h')

end quasicategory

end edgeHomotopy


end SSet
