import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Category.ReflQuiv
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Monad.Limits

noncomputable section

namespace CategoryTheory
open Category Limits Functor
universe v v₁ v₂ u u₁ u₂

section

-- NB: Copied to Mathlib/CategoryTheory/Quotient.lean
namespace Quotient
variable {C : Type _} [Category C] (r : HomRel C)

theorem CompClosure.congruence : Congruence fun a b => Relation.EqvGen (@CompClosure C _ r a b) where
  equivalence := Relation.EqvGen.is_equivalence _
  compLeft f g g' rel := by
    induction rel with
    | rel _ _ h =>
      let .intro f' m₁ m₂ g h := h
      apply Relation.EqvGen.rel
      rw [← assoc, ← assoc f]
      exact ⟨_, _, _, _, h⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  compRight g rel := by
    induction rel with
    | rel _ _ h =>
      let .intro f' m₁ m₂ g h := h
      apply Relation.EqvGen.rel
      repeat rw [assoc]
      exact ⟨_, _, _, _, h⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

end Quotient

-- NB: Moved to Order.Category.NonEmptyFiniteLinOrd.lean; who knows if this is correct
theorem Fin.le_succ {n} (i : Fin n) : i.castSucc ≤ i.succ := Nat.le_succ i

def Fin.hom_succ {n} (i : Fin n) : i.castSucc ⟶ i.succ := homOfLE (Fin.le_succ i)

-- NB: Ignoring through the local notation for now.
open Simplicial
local notation3:1000 (priority := high) X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))
namespace SimplexCategory

abbrev Δ (k : ℕ) := SimplexCategory.Truncated k

instance (k : ℕ) : Category (Δ k) := inferInstanceAs (Category (FullSubcategory ..))

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

-- NB: Moved to simplex category and compiled out the abbreviation.
@[ext]
theorem Δ.Hom.ext {k} {a b : Δ k} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g := SimplexCategory.Hom.ext _ _

def mkOfLe {n} (i j : Fin (n+1)) (h : i ≤ j) : [1] ⟶ [n] :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => h
  }

def mkOfSucc {n} (i : Fin n) : [1] ⟶ [n] :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i.castSucc | 1 => i.succ
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => Fin.le_succ i
  }

def mkOfLeComp {n} (i j k : Fin (n+1)) (h₁ : i ≤ j) (h₂ : j ≤ k): [2] ⟶ [n] :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j | 2 => k
    monotone' := fun
      | 0, 0, _ | 1, 1, _ | 2, 2, _  => le_rfl
      | 0, 1, _ => h₁
      | 1, 2, _ => h₂
      | 0, 2, _ => Fin.le_trans h₁ h₂
  }


-- NB: Moved to SimplexCategory because it's needed weirdly for skAdj and coskAdj?
/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
abbrev Δ.ι (k) : Δ k ⥤ SimplexCategory := SimplexCategory.Truncated.inclusion k

-- NB: Next three definitions exist already in simplex category (without the abbrevation). Final instance had to be made "noncomputable."

instance Δ.ι.op_full (k) : (Δ.ι k).op.Full := inferInstance

instance Δ.ι.op_faithful (k) : (Δ.ι k).op.Faithful := inferInstance

instance Δ.ι.op.fullyFaithful (k) : (Δ.ι k).op.FullyFaithful :=
  FullyFaithful.ofFullyFaithful (ι k).op

-- NB: Moved to SimplexCategory.
theorem const_fac_thru_zero (n m : SimplexCategory) (i : Fin (m.len + 1)) :
    SimplexCategory.const n m i =
    SimplexCategory.const n [0] 0 ≫ SimplexCategory.const [0] m i := by
  rw [SimplexCategory.const_comp]; rfl

theorem eq_const_of_zero {n : SimplexCategory} (f : [0] ⟶ n) :
    f = SimplexCategory.const _ n (f.toOrderHom 0) := by
  ext x; match x with | 0 => rfl

theorem eq_const_of_zero' {n : SimplexCategory} (f : [0] ⟶ n) :
    ∃ a, f = SimplexCategory.const _ n a := ⟨_, eq_const_of_zero _⟩

theorem eq_const_to_zero {n : SimplexCategory} (f : n ⟶ [0]) :
    f = SimplexCategory.const n _ 0 := by
  ext : 3
  apply @Subsingleton.elim (Fin 1)

theorem eq_of_one_to_one (f : [1] ⟶ [1]) :
    (∃ a, f = SimplexCategory.const [1] _ a) ∨ f = 𝟙 _ := by
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 0, 0 | 1, 1 =>
    refine .inl ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 0, 1 =>
    right
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 1, 0 =>
    have := f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)
    rw [e0, e1] at this
    exact Not.elim (by decide) this

theorem eq_of_one_to_two (f : [1] ⟶ [2]) :
    f = (SimplexCategory.δ (n := 1) 0) ∨ f = (SimplexCategory.δ (n := 1) 1) ∨ f = (SimplexCategory.δ (n := 1) 2) ∨ ∃ a, f = SimplexCategory.const _ _ a := by
  have : f.toOrderHom 0 ≤ f.toOrderHom 1 := f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 1, 2 =>
    left
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 2 =>
    right; left
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 1 =>
    right; right; left
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 0 | 1, 1 | 2, 2 =>
    right; right; right; use f.toOrderHom 0
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 1, 0 | 2, 0 | 2, 1 =>
    rw [e0, e1] at this
    exact Not.elim (by decide) this

end SimplexCategory

open SimplexCategory

namespace SSet

-- NB: Moved to SimplicialSet
/-- The ulift functor `SSet.Truncated.{u} ⥤ SSet.Truncated.{max u v}` on truncated
simplicial sets. -/
def Truncated.uliftFunctor (k : ℕ) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

-- NB: Renamed "sk" to "truncation" in both SimplicialObject and SimplicialSet.
/-- This is called "sk" in SimplicialSet and SimplicialObject, but this is a better name.-/
def truncation (k) : SSet ⥤ SSet.Truncated k := (whiskeringLeft _ _ _).obj (Δ.ι k).op

-- NB: Moved to SimplicialSet.
def skAdj (k) : lan (Δ.ι k).op ⊣ truncation.{u} k := lanAdjunction _ _
def coskAdj (k) : truncation.{u} k ⊣ ran (Δ.ι k).op := ranAdjunction _ _

instance coskeleton_reflective (k) : IsIso ((coskAdj k).counit) :=
  reflective' (Δ.ι k).op

instance skeleton_reflective (k) : IsIso ((skAdj k).unit) :=
  coreflective' (Δ.ι k).op

instance coskeleton.fullyFaithful (k) : (ran (H := Type u) (Δ.ι k).op).FullyFaithful := by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskAdj k)

instance coskeleton.full (k) : (ran (H := Type u) (Δ.ι k).op).Full :=
  FullyFaithful.full (coskeleton.fullyFaithful k)

instance coskeleton.faithful (k) : (ran (H := Type u) (Δ.ι k).op).Faithful :=
  FullyFaithful.faithful (coskeleton.fullyFaithful k)

instance coskAdj.reflective (k) : Reflective (ran (H := Type u) (Δ.ι k).op) :=
  Reflective.mk (truncation k) (coskAdj k)

instance skeleton.fullyFaithful (k) : (lan (H := Type u) (Δ.ι k).op).FullyFaithful := by
  apply Adjunction.fullyFaithfulLOfIsIsoUnit (skAdj k)

instance skeleton.full (k) : (lan (H := Type u) (Δ.ι k).op).Full :=
  FullyFaithful.full (skeleton.fullyFaithful k)

instance skeleton.faithful (k) : (lan (H := Type u) (Δ.ι k).op).Faithful :=
  FullyFaithful.faithful (skeleton.fullyFaithful k)

instance skAdj.coreflective (k) : Coreflective (lan (H := Type u) (Δ.ι k).op) :=
  Coreflective.mk (truncation k) (skAdj k)

end SSet

-- NB: Moved to Nerve.
open SSet

def nerveFunctor₂ : Cat.{v, u} ⥤ SSet.Truncated 2 := nerveFunctor ⋙ truncation 2

def nerve₂ (C : Type*) [Category C] : SSet.Truncated 2 := nerveFunctor₂.obj (Cat.of C)

theorem nerve₂_restrictedNerve (C : Type*) [Category C] :
    (Δ.ι 2).op ⋙ nerve C = nerve₂ C := rfl

def nerve₂RestrictedIso (C : Type*) [Category C] :
    (Δ.ι 2).op ⋙ nerve C ≅ nerve₂ C := Iso.refl _

namespace Nerve
open Opposite

/-- The identity natural transformation exhibits nerve C as a right extension of its restriction to (Δ 2).op along (Δ.ι 2).op.-/
def nerveRightExtension (C : Cat) : RightExtension (Δ.ι 2).op (nerveFunctor₂.obj C) :=
  RightExtension.mk (nerveFunctor.obj C) (𝟙 ((Δ.ι 2).op ⋙ nerveFunctor.obj C))

/-- The natural transformation in nerveRightExtension C defines a cone with summit
nerve C _[n] over the diagram (StructuredArrow.proj (op ([n] : SimplexCategory)) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C) indexed by the category StructuredArrow (op [n]) (Δ.ι 2).op. -/
def nerveRightExtension.coneAt (C : Cat) (n : ℕ) :
    Cone (StructuredArrow.proj (op ([n] : SimplexCategory)) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C) :=
  RightExtension.coneAt (nerveRightExtension C) (op [n])

section

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : Δ 2))

/-- The map [0] ⟶ [n] with image i.-/
private
def pt {n} (i : Fin (n + 1)) : ([0] : SimplexCategory) ⟶ [n] := SimplexCategory.const _ _ i

/-- The object of StructuredArrow (op [n]) (Δ.ι 2).op corresponding to pt i. -/
private
def pt' {n} (i : Fin (n + 1)) : StructuredArrow (op [n]) (Δ.ι 2).op :=
  .mk (Y := op [0]₂) (.op (pt i))

/-- The map [1] ⟶ [n] with image k : i ⟶ j.-/
private
def ar {n} {i j : Fin (n+1)} (k : i ⟶ j) : [1] ⟶ [n] := mkOfLe _ _ k.le

/-- The object of StructuredArrow (op [n]) (Δ.ι 2).op corresponding to ar k. -/
private
def ar' {n} {i j : Fin (n+1)} (k : i ⟶ j) : StructuredArrow (op [n]) (Δ.ι 2).op :=
  .mk (Y := op [1]₂) (.op (ar k))

/-- The object of StructuredArrow (op [n]) (Δ.ι 2).op corresponding to
ar Fin.hom_succ i. -/
private
def ar'succ {n} (i : Fin n) : StructuredArrow (op [n]) (Δ.ι 2).op := ar' (Fin.hom_succ i)

theorem ran.lift.eq {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n]) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) {i j} (k : i ⟶ j) :
    (s.π.app (CategoryTheory.Nerve.pt' i) x).obj 0 =
    (s.π.app (CategoryTheory.Nerve.ar' k) x).obj 0
 := by
  have hi := congr_fun (s.π.naturality <|
      StructuredArrow.homMk (f := ar' k) (f' := pt' i)
        (.op (SimplexCategory.const _ _ 0)) <| by
        apply Quiver.Hom.unop_inj
        ext z; revert z; intro (0 : Fin 1); rfl) x
  simp at hi
  rw [hi]
  exact rfl

theorem ran.lift.eq₂ {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n]) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) {i j} (k : i ⟶ j) :
    (s.π.app (CategoryTheory.Nerve.pt' j) x).obj 0 =
    (s.π.app (CategoryTheory.Nerve.ar' k) x).obj 1
 := by
  have hj := congr_fun (s.π.naturality <|
      StructuredArrow.homMk (f := ar' k) (f' := pt' j)
        (.op (SimplexCategory.const _ _ 1)) <| by
        apply Quiver.Hom.unop_inj
        ext z; revert z; intro (0 : Fin 1); rfl) x
  simp at hj
  rw [hj]
  exact rfl

/-- This is the value at x : s.pt of the lift of the cone s through the cone with summit nerve
C _[n].-/
private
def ran.lift {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n]) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) : nerve C _[n] :=
  ComposableArrows.mkOfObjOfMapSucc (fun i ↦ s.π.app (pt' i) x |>.obj 0)
    (fun i ↦ eqToHom (ran.lift.eq ..) ≫ (s.π.app (ar'succ i) x).map' 0 1 ≫ eqToHom (ran.lift.eq₂ ..).symm)

/-- A second less efficient construction of the above with more information about arbitrary maps.-/
private
def ran.lift' {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n]) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) : nerve C _[n] where
    obj i := s.π.app (pt' i) x |>.obj 0
    map {i j} (k : i ⟶ j) :=
      eqToHom (ran.lift.eq ..) ≫
      ((s.π.app (ar' k) x).map' 0 1) ≫
      eqToHom (ran.lift.eq₂ ..).symm
    map_id i := by
      have nat := congr_fun (s.π.naturality <|
        StructuredArrow.homMk (f := pt' i) (f' := ar' (𝟙 i))
          (.op (SimplexCategory.const _ _ 0)) <| by
            apply Quiver.Hom.unop_inj
            ext z; revert z; intro | 0 | 1 => rfl) x
      dsimp at nat ⊢
      refine ((conj_eqToHom_iff_heq' ..).2 ?_).symm
      have := congr_arg_heq (·.map' 0 1) nat
      simp [nerveFunctor₂, truncation] at this
      refine HEq.trans ?_ this.symm
      conv => rhs; rhs; equals 𝟙 _ => apply Subsingleton.elim
      simp; rfl
    map_comp := fun {i j k} f g => by
      let tri {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : [2] ⟶ [n] := mkOfLeComp _ _ _ f.le g.le
      let tri' {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : StructuredArrow (op [n]) (Δ.ι 2).op :=
        .mk (Y := op [2]₂) (.op (tri f g))
      let facemap₂ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ ar' f := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 2)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let facemap₀ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : (tri' f g) ⟶ (ar' g) := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 0)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let facemap₁ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : (tri' f g) ⟶ ar' (f ≫ g) := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 1)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let tri₀ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' i := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 0)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      let tri₁ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' j := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 1)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      let tri₂ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' k := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 2)) (Quiver.Hom.unop_inj ?_)
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      apply eq_of_heq
      simp only [Fin.isValue, ← assoc, eqToHom_trans_assoc,
        heq_eqToHom_comp_iff, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
      simp [assoc]
      have h'f := congr_arg_heq (·.map' 0 1) (congr_fun (s.π.naturality (facemap₂ f g)) x)
      have h'g := congr_arg_heq (·.map' 0 1) (congr_fun (s.π.naturality (facemap₀ f g)) x)
      have h'fg := congr_arg_heq (·.map' 0 1) (congr_fun (s.π.naturality (facemap₁ f g)) x)
      dsimp at h'f ⊢
      dsimp at h'g ⊢
      dsimp at h'fg ⊢
      refine ((heq_comp ?_ ?_ ?_ h'f ((eqToHom_comp_heq_iff ..).2 h'g)).trans ?_).symm
      · exact (ran.lift.eq ..).symm.trans congr($(congr_fun (s.π.naturality (tri₀ f g)) x).obj 0)
      · exact (ran.lift.eq₂ ..).symm.trans congr($(congr_fun (s.π.naturality (tri₁ f g)) x).obj 0)
      · exact (ran.lift.eq₂ ..).symm.trans congr($(congr_fun (s.π.naturality (tri₂ f g)) x).obj 0)
      refine (h'fg.trans ?_).symm
      simp [nerveFunctor₂, truncation, ← map_comp]; congr 1

theorem ran.lift.map {C : Cat} {n}
    (s : Cone (StructuredArrow.proj (op [n]) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C))
    (x : s.pt) {i j} (k : i ⟶ j) :
    (ran.lift s x).map k =
      eqToHom (ran.lift.eq ..) ≫
      ((s.π.app (ar' k) x).map' 0 1) ≫
      eqToHom (ran.lift.eq₂ ..).symm := by
  have : ran.lift s x = ran.lift' s x := by
    fapply ComposableArrows.ext
    · exact fun _ ↦ rfl
    · intro i hi
      dsimp only [CategoryTheory.Nerve.ran.lift]
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi, eqToHom_refl, eqToHom_refl, id_comp, comp_id]
      rfl
  exact eq_of_heq (congr_arg_heq (·.map k) this)

/-- An object j : StructuredArrow (op [n]) (Δ.ι 2).op defines a morphism Fin (jlen+1) -> Fin(n+1).
This calculates the image of i : Fin(jlen+1); we might think of this as j(i). -/
private
def strArr.homEv {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin ((unop ((Δ.ι 2).op.obj ((StructuredArrow.proj (op [n]) (Δ.ι 2).op).obj j))).len + 1)) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i

/-- This is the unique arrow in StructuredArrow (op [n]) (Δ.ι 2).op from j to pt' of the j(i)
calculated above. This is used to prove that ran.lift defines a factorization on objects.-/
private
def fact.obj.arr {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin ((unop ((Δ.ι 2).op.obj ((StructuredArrow.proj (op [n]) (Δ.ι 2).op).obj j))).len + 1))
    : j ⟶ (pt' (strArr.homEv j i)) :=
  StructuredArrow.homMk (.op (SimplexCategory.const _ _ i)) <| by
    apply Quiver.Hom.unop_inj
    ext z; revert z; intro | 0 => rfl

/-- An object j : StructuredArrow (op [n]) (Δ.ι 2).op defines a morphism Fin (jlen+1) -> Fin(n+1).
This calculates the image of i.succ : Fin(jlen+1); we might think of this as j(i.succ). -/
private
def strArr.homEvSucc {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin (unop j.right).1.len) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i.succ

/-- The unique arrow (strArr.homEv j i.castSucc) ⟶ (strArr.homEvSucc j i) in Fin(n+1). -/
private
def strArr.homEv.map {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin (unop j.right).1.len) :
    strArr.homEv j i.castSucc ⟶ strArr.homEvSucc j i :=
  (Monotone.functor (j.hom.unop.toOrderHom).monotone).map (Fin.hom_succ i)

/-- This is the unique arrow in StructuredArrow (op [n]) (Δ.ι 2).op from j to ar' of the map just
constructed. This is used to prove that ran.lift defines a factorization on maps.-/
private
def fact.map.arr {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin (unop j.right).1.len)
    : j ⟶ ar' (strArr.homEv.map j i) := by
  fapply StructuredArrow.homMk
  · exact .op (mkOfSucc i : [1] ⟶ [(unop j.right).1.len])
  · apply Quiver.Hom.unop_inj
    ext z; revert z
    intro
    | 0 => rfl
    | 1 => rfl

def isPointwiseRightKanExtensionAt (C : Cat) (n : ℕ) :
    RightExtension.IsPointwiseRightKanExtensionAt
      (nerveRightExtension C) (op ([n] : SimplexCategory)) := by
  show IsLimit _
  unfold nerveRightExtension RightExtension.coneAt
  simp only [nerveFunctor_obj, RightExtension.mk_left, nerve_obj, SimplexCategory.len_mk,
    const_obj_obj, op_obj, comp_obj, StructuredArrow.proj_obj, whiskeringLeft_obj_obj,
    RightExtension.mk_hom, NatTrans.id_app, comp_id]
  exact {
    lift := fun s x => ran.lift s x
    fac := by
      intro s j
      ext x
      refine have obj_eq := ?_; ComposableArrows.ext obj_eq ?_
      · exact fun i ↦ congrArg (·.obj 0) <| congr_fun (s.π.naturality (fact.obj.arr j i)) x
      · intro i hi
        simp only [StructuredArrow.proj_obj, op_obj, const_obj_obj, comp_obj, nerveFunctor_obj,
          RightExtension.mk_left, nerve_obj, SimplexCategory.len_mk, whiskeringLeft_obj_obj,
          RightExtension.mk_hom, NatTrans.id_app, const_obj_map, Functor.comp_map,
          StructuredArrow.proj_map, StructuredArrow.mk_right, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          ComposableArrows.map', types_comp_apply, nerve_map, SimplexCategory.toCat_map, id_eq,
          Int.reduceNeg, Int.Nat.cast_ofNat_Int, ComposableArrows.whiskerLeft_obj,
          Monotone.functor_obj, ComposableArrows.mkOfObjOfMapSucc_obj,
          ComposableArrows.whiskerLeft_map] at obj_eq ⊢
        rw [ran.lift.map]
        have nat := congr_fun (s.π.naturality (fact.map.arr j (Fin.mk i hi))) x
        have := congr_arg_heq (·.map' 0 1) <| nat
        refine (conj_eqToHom_iff_heq' ..).2 ?_
        simpa only [Int.reduceNeg, StructuredArrow.proj_obj, op_obj, id_eq, Int.Nat.cast_ofNat_Int,
          Fin.mk_one, Fin.isValue, ComposableArrows.map', Int.reduceAdd, Int.reduceSub,
          Fin.zero_eta, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    uniq := by
      intro s lift' fact'
      ext x
      unfold ran.lift pt' pt ar'succ ar' ar
      fapply ComposableArrows.ext
      · exact fun i ↦ (congrArg (·.obj 0) <| congr_fun (fact'
          (StructuredArrow.mk (Y := op [0]₂) ([0].const [n] i).op)) x)
      · intro i hi
        rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
        have eq := congr_fun (fact' (ar'succ (Fin.mk i hi))) x
        simp at eq ⊢
        exact (conj_eqToHom_iff_heq' ..).2 (congr_arg_heq (·.hom) <| eq)
  }
end

def isPointwiseRightKanExtension (C : Cat) :
    RightExtension.IsPointwiseRightKanExtension (nerveRightExtension C) :=
  fun Δ => isPointwiseRightKanExtensionAt C Δ.unop.len

def isPointwiseRightKanExtension.isUniversal (C : Cat) :
    CostructuredArrow.IsUniversal (nerveRightExtension C) :=
  RightExtension.IsPointwiseRightKanExtension.isUniversal (isPointwiseRightKanExtension C)

theorem isRightKanExtension (C : Cat) :
    (nerveRightExtension C).left.IsRightKanExtension (nerveRightExtension C).hom :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension C)

/-- The natural map from a nerve. -/
def cosk2NatTrans : nerveFunctor.{u, v} ⟶ nerveFunctor₂ ⋙ ran (Δ.ι 2).op :=
  whiskerLeft nerveFunctor (coskAdj 2).unit

def cosk2RightExtension.hom (C : Cat.{v, u}) :
    nerveRightExtension C ⟶
      RightExtension.mk _ ((Δ.ι 2).op.ranCounit.app ((Δ.ι 2).op ⋙ nerveFunctor.obj C)) :=
  CostructuredArrow.homMk (cosk2NatTrans.app C)
    ((coskAdj 2).left_triangle_components (nerveFunctor.obj C))

instance cosk2RightExtension.hom_isIso (C : Cat) :
    IsIso (cosk2RightExtension.hom C) :=
    isIso_of_isTerminal
      (isPointwiseRightKanExtension.isUniversal C)
      (((Δ.ι 2).op.ran.obj ((Δ.ι 2).op ⋙ nerveFunctor.obj C)).isUniversalOfIsRightKanExtension
        ((Δ.ι 2).op.ranCounit.app ((Δ.ι 2).op ⋙ nerveFunctor.obj C)))
      (cosk2RightExtension.hom C)

def cosk2RightExtension.component.hom.iso (C : Cat.{v, u}) :
    nerveRightExtension C ≅
      RightExtension.mk _ ((Δ.ι 2).op.ranCounit.app ((Δ.ι 2).op ⋙ nerveFunctor.obj C)) :=
  asIso (cosk2RightExtension.hom C)

def cosk2NatIso.component (C : Cat.{v, u}) :
    nerveFunctor.obj C ≅ (ran (Δ.ι 2).op).obj (nerveFunctor₂.obj C) :=
  (CostructuredArrow.proj
    ((whiskeringLeft _ _ _).obj (Δ.ι 2).op) ((Δ.ι 2).op ⋙ nerveFunctor.obj C)).mapIso
      (cosk2RightExtension.component.hom.iso C)

/-- It follows that we have a natural isomorphism between nerveFunctor and nerveFunctor ⋙ cosk₂
whose components are the isomorphisms just established. -/
def cosk2Iso : nerveFunctor.{u, u} ≅ nerveFunctor₂.{u, u} ⋙ ran (Δ.ι 2).op := by
  apply NatIso.ofComponents cosk2NatIso.component _
  have := cosk2NatTrans.{u, u}.naturality
  exact cosk2NatTrans.naturality

end Nerve

-- NB: Moved from here to the commented out to-dos to HomotopyCat.

section
open Opposite

def SSet.OneTruncation (S : SSet) := S _[0]

def SSet.OneTruncation.src {S : SSet} (f : S _[1]) : OneTruncation S :=
  S.map (SimplexCategory.δ (n := 0) 1).op f

def SSet.OneTruncation.tgt {S : SSet} (f : S _[1]) : OneTruncation S :=
  S.map (SimplexCategory.δ (n := 0) 0).op f

def SSet.OneTruncation.Hom {S : SSet} (X Y : OneTruncation S) :=
  {p : S _[1] // src p = X ∧ tgt p = Y}

instance (S : SSet) : ReflQuiver (OneTruncation S) where
  Hom X Y := OneTruncation.Hom X Y
  id X := by
    refine ⟨S.map (SimplexCategory.σ (n := 0) 0).op X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp, (_ : _ ≫ _ = 𝟙 _)]; simp
      show ({..} : Opposite _) = _; congr; ext i
      let 0 := i
      rfl

def SSet.oneTruncation : SSet.{u} ⥤ ReflQuiv.{u,u} where
  obj S := ReflQuiv.of (OneTruncation S)
  map {S T} F := {
    obj := F.app (op [0])
    map := fun f => by
      refine ⟨F.app (op [1]) f.1, ?_, ?_⟩
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.1
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.2
    map_id := fun X => by
      change ({..} : Subtype _) = {..}
      congr
      change _ = (F.app _ ≫ _) _
      rw [← F.naturality]
      rfl
  }
  map_id X := rfl
  map_comp f g := rfl

section
variable {C : Type u} [Category.{v} C]

theorem opstuff.{w} (V : Cᵒᵖ ⥤ Type w) {X Y Z : C} {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
      α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
    rintro rfl
    change (V.map _ ≫ V.map _) _ = _
    rw [← map_comp]; rfl

def SSet.OneTruncation.ofNerve.map {X Y : OneTruncation (nerve C)}
    (f : X ⟶ Y) : X.left ⟶ Y.left :=
  eqToHom (congrArg (·.left) f.2.1.symm) ≫ f.1.hom ≫ eqToHom (congrArg (·.left) f.2.2)

def SSet.OneTruncation.ofNerve.hom : OneTruncation (nerve C) ⥤rq C where
  obj := (·.left)
  map := OneTruncation.ofNerve.map
  map_id := fun X : ComposableArrows _ 0 => by
    simp only [SimplexCategory.len_mk, map, nerve_obj, eqToHom_refl, comp_id, id_comp,
      ReflQuiver.id_eq_id]
    exact ComposableArrows.map'_self _ 0

def SSet.OneTruncation.ofNerve.inv : C ⥤rq OneTruncation (nerve C) where
  obj := (.mk₀ ·)
  map := fun f => by
    refine ⟨.mk₁ f, ?_⟩
    constructor <;> apply ComposableArrows.ext <;>
      simp [SimplexCategory.len] <;> (exact fun 0 ↦ rfl)
  map_id := fun X : C => Subtype.ext <| by
    simp; apply ComposableArrows.ext <;> simp
    · rintro _ rfl; simp; rfl
    · intro; split <;> rfl

def SSet.OneTruncation.ofNerve (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation (nerve C)) ≅ ReflQuiv.of C := by
  refine {
    hom := ofNerve.hom
    inv := ofNerve.inv (C := C)
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  · have H1 {X X' Y : OneTruncation (nerve C)} (f : X ⟶ Y) (h : X = X') :
        (Eq.rec f h : X' ⟶ Y).1 = f.1 := by cases h; rfl
    have H2 {X Y Y' : OneTruncation (nerve C)} (f : X ⟶ Y) (h : Y = Y') :
        (Eq.rec f h : X ⟶ Y').1 = f.1 := by cases h; rfl
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ ComposableArrows.ext₀ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      apply Subtype.ext
      simp [ReflQuiv.comp_eq_comp]
      refine ((H2 ..).trans ((H1 ..).trans (ComposableArrows.ext₁ ?_ ?_ ?_))).symm
      · rfl
      · rfl
      · simp [ofNerve.inv, ofNerve.hom, ofNerve.map]; rfl
  · fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      simp [ReflQuiv.comp_eq_comp, ReflQuiv.id_eq_id, ofNerve.inv, ofNerve.hom, ofNerve.map]

@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def SSet.OneTruncation.ofNerve.natIso : nerveFunctor.{u,u} ⋙ SSet.oneTruncation ≅ ReflQuiv.forget := by
  refine NatIso.ofComponents (fun C => OneTruncation.ofNerve C) ?nat
  · intro C D F
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      unfold SSet.oneTruncation nerveMap mapComposableArrows toReflPrefunctor
      simp [ReflQuiv.comp_eq_comp, ofNerve, ofNerve.hom, ofNerve.map]

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

private def ι0 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 1
private def ι1 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 2
private def ι2 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 1

private def ev0 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map ι0.op φ
private def ev1 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map ι1.op φ
private def ev2 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map ι2.op φ

private def δ0 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 0
private def δ1 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 1
private def δ2 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 2

private def ev02 {V : SSet} (φ : V _[2]) : ev0 φ ⟶ ev2 φ :=
  ⟨V.map δ1.op φ, opstuff V rfl, opstuff V rfl⟩
private def ev01 {V : SSet} (φ : V _[2]) : ev0 φ ⟶ ev1 φ :=
  ⟨V.map δ2.op φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
private def ev12 {V : SSet} (φ : V _[2]) : ev1 φ ⟶ ev2 φ :=
  ⟨V.map δ0.op φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

inductive SSet.HoRel {V : SSet} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]) :
    HoRel _ _
      (Quot.mk _ (.cons .nil (ev02 φ)))
      (Quot.mk _ (.cons (.cons .nil (ev01 φ)) (ev12 φ)))

theorem SSet.HoRel.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation V)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Z) (f' : X' ⟶ Z') (hf : f.1 = f'.1)
    (g : X ⟶ Y) (g' : X' ⟶ Y') (hg : g.1 = g'.1)
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (hh : h.1 = h'.1) :
    HoRel _ _
      ((Quotient.functor _).map (.cons .nil f))
      ((Quotient.functor _).map (.cons (.cons .nil g) h)) ↔
    HoRel _ _
      ((Quotient.functor _).map (.cons .nil f'))
      ((Quotient.functor _).map (.cons (.cons .nil g') h')) := by
  cases hX
  cases hY
  cases hZ
  congr! <;> apply Subtype.ext <;> assumption

def SSet.hoCat (V : SSet.{u}) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) (HoRel (V := V))

instance (V : SSet.{u}) : Category.{u} (SSet.hoCat V) :=
  inferInstanceAs (Category (Quotient ..))

def SSet.hoFunctorMap {V W : SSet.{u}} (F : V ⟶ W) : SSet.hoCat V ⥤ SSet.hoCat W :=
  Quotient.lift _ (((SSet.oneTruncation ⋙ Cat.freeRefl).map F) ⋙ Quotient.functor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      simp [Quot.liftOn]
      apply Quotient.sound
      convert HoRel.mk (F.app (op [2]) φ) using 0
      apply HoRel.ext_triangle
      · exact congrFun (F.naturality ι0.op) φ
      · exact congrFun (F.naturality ι1.op) φ
      · exact congrFun (F.naturality ι2.op) φ
      · exact congrFun (F.naturality δ1.op) φ
      · exact congrFun (F.naturality δ2.op) φ
      · exact congrFun (F.naturality δ0.op) φ)

def SSet.hoFunctor' : SSet.{u} ⥤ Cat.{u,u} where
  obj V := Cat.of (SSet.hoCat V)
  map {S T} F := SSet.hoFunctorMap F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctorMap, Quotient.lift_spec]
    exact (Functor.id_comp ..).trans (Functor.comp_id ..).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctorMap]
    rw [Quotient.lift_spec, Cat.comp_eq_comp, Cat.comp_eq_comp, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]
end
section

local macro:1000 (priority := high) X:term " _[" n:term "]₂" : term =>
    `(($X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

-- FIXME why doesn't this work?
-- local notation3:1000 (priority := high) (prettyPrint := false) " _[" n "]₂" =>
--     (X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk n, by decide⟩)

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : Δ 2))

def SSet.OneTruncation₂ (S : SSet.Truncated 2) := S _[0]₂

abbrev SSet.δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
    (⟨[n], hn⟩ : Δ 2) ⟶ ⟨[n + 1], hn'⟩ := SimplexCategory.δ i

abbrev SSet.σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨[n+1], hn⟩ : Δ 2) ⟶ ⟨[n], hn'⟩ := SimplexCategory.σ i

def SSet.OneTruncation₂.src {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ (n := 0) 1).op f

def SSet.OneTruncation₂.tgt {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ (n := 0) 0).op f

def SSet.OneTruncation₂.Hom {S : SSet.Truncated 2} (X Y : OneTruncation₂ S) :=
  {p : S _[1]₂ // src p = X ∧ tgt p = Y}

instance (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom X Y := OneTruncation₂.Hom X Y
  id X := by
    refine ⟨S.map (σ₂ (n := 0) 0).op X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp, (_ : _ ≫ _ = 𝟙 _)]; simp
      show ({..} : Opposite _) = _; congr; dsimp [Δ]; ext ⟨i, _⟩
      let 0 := i
      rfl

def SSet.oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u,u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map {S T} F := {
    obj := F.app (op [0]₂)
    map := fun f => by
      refine ⟨F.app (op [1]₂) f.1, ?_, ?_⟩
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.1
      · change (F.app _ ≫ _) _ = _
        rw [← F.naturality]
        exact congrArg (F.app _) f.2.2
    map_id := fun X => by
      change ({..} : Subtype _) = {..}
      congr
      change _ = (F.app _ ≫ _) _
      rw [← F.naturality]
      rfl
  }
  map_id X := rfl
  map_comp f g := rfl

section
variable {V : SSet}

def SSet.OneTruncation₂.ofTwoTruncationIso (V : SSet) :
    ReflQuiv.of (OneTruncation₂ ((truncation 2).obj V)) ≅ ReflQuiv.of (OneTruncation V) := .refl _

def SSet.OneTruncation₂.nerve₂Iso (C : Cat) :
    ReflQuiv.of (OneTruncation₂ (nerve₂ C)) ≅ ReflQuiv.of (OneTruncation (nerve C)) := .refl _

@[simps!]
def SSet.OneTruncation₂.nerve₂.natIso :
    nerveFunctor₂ ⋙ SSet.oneTruncation₂ ≅ nerveFunctor ⋙ SSet.oneTruncation := .refl _

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

private def ι0₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1
private def ι1₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2
private def ι2₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

private def ev0₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι0₂.op φ
private def ev1₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι1₂.op φ
private def ev2₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι2₂.op φ

private def δ1₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 1
private def δ2₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 2
private def δ0₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 0

private def ev02₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, opstuff V rfl, opstuff V rfl⟩
private def ev01₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
private def ev12₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

inductive SSet.HoRel₂ {V : SSet.Truncated 2} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]₂) :
    HoRel₂ _ _
      (Quot.mk _ (.cons .nil (ev02₂ φ)))
      (Quot.mk _ (.cons (.cons .nil (ev01₂ φ)) (ev12₂ φ)))

theorem SSet.HoRel₂.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation₂ V)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Z) (f' : X' ⟶ Z') (hf : f.1 = f'.1)
    (g : X ⟶ Y) (g' : X' ⟶ Y') (hg : g.1 = g'.1)
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (hh : h.1 = h'.1) :
    HoRel₂ _ _ ((Quotient.functor _).map (.cons .nil f)) ((Quotient.functor _).map (.cons (.cons .nil g) h)) ↔
    HoRel₂ _ _ ((Quotient.functor _).map (.cons .nil f')) ((Quotient.functor _).map (.cons (.cons .nil g') h')) := by
  cases hX
  cases hY
  cases hZ
  congr! <;> apply Subtype.ext <;> assumption

def SSet.hoFunctor₂Obj (V : SSet.Truncated.{u} 2) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

instance (V : SSet.Truncated.{u} 2) : Category.{u} (SSet.hoFunctor₂Obj V) :=
  inferInstanceAs (Category (Quotient ..))

def SSet.hoFunctor₂Obj.quotientFunctor (V : SSet.Truncated.{u} 2) :
    Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)) ⥤ SSet.hoFunctor₂Obj V :=
  Quotient.functor (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

theorem SSet.hoFunctor₂Obj.lift_unique' (V : SSet.Truncated.{u} 2)
    {D} [Category D] (F₁ F₂ : SSet.hoFunctor₂Obj V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) : F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)))
    (HoRel₂ (V := V)) _ _ h

def SSet.hoFunctor₂Map {V W : SSet.Truncated.{u} 2} (F : V ⟶ W) : SSet.hoFunctor₂Obj V ⥤ SSet.hoFunctor₂Obj W :=
  Quotient.lift _
    ((SSet.oneTruncation₂ ⋙ Cat.freeRefl).map F ⋙ SSet.hoFunctor₂Obj.quotientFunctor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      apply Quotient.sound
      convert HoRel₂.mk (F.app (op _) φ) using 0
      apply HoRel₂.ext_triangle
      · exact congrFun (F.naturality ι0₂.op) φ
      · exact congrFun (F.naturality ι1₂.op) φ
      · exact congrFun (F.naturality ι2₂.op) φ
      · exact congrFun (F.naturality δ1₂.op) φ
      · exact congrFun (F.naturality δ2₂.op) φ
      · exact congrFun (F.naturality δ0₂.op) φ)

def SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u} where
  obj V := Cat.of (SSet.hoFunctor₂Obj V)
  map {S T} F := SSet.hoFunctor₂Map F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, SSet.hoFunctor₂Obj.quotientFunctor]
    rw [Quotient.lift_spec, Cat.comp_eq_comp, Cat.comp_eq_comp, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

theorem SSet.hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    (SSet.oneTruncation₂ ⋙ Cat.freeRefl).map f ⋙
    hoFunctor₂Obj.quotientFunctor Y =
    SSet.hoFunctor₂Obj.quotientFunctor X ⋙ hoFunctor₂Map f := rfl

def SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := truncation 2 ⋙ SSet.hoFunctor₂

end

-- /-- ER: We don't actually need this but it would be nice and potentially not too hard. -/
-- def hoFunctor.ofTwoTruncationIso (V : SSet) :
--     SSet.hoFunctor₂Obj ((truncation 2).obj V) ≅ SSet.hoCat V := sorry

-- /-- ER: We don't actually need this but it would be nice and potentially not too hard. -/
-- def hoFunctor.ofTwoTruncationNatIso :
--     truncation 2 ⋙ SSet.hoFunctor₂ ≅ SSet.hoFunctor' := sorry

-- NB: Moved from here through the second to last definition to NerveAdjunction.
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def forgetToReflQuiv.natIso : nerveFunctor₂ ⋙ SSet.oneTruncation₂.{u} ≅ ReflQuiv.forget :=
  OneTruncation₂.nerve₂.natIso ≪≫ OneTruncation.ofNerve.natIso

@[simps!]
def nerve₂Adj.counit.component (C : Cat.{u, u}) :
    SSet.hoFunctor₂.obj (nerveFunctor₂.obj C) ⥤ C := by
  fapply Quotient.lift
  · exact (whiskerRight (forgetToReflQuiv.natIso).hom _ ≫ ReflQuiv.adj.{u}.counit).app C
  · intro x y f g rel
    cases rel; rename_i φ
    simp [ReflQuiv.adj, Quot.liftOn, Cat.FreeRefl.quotientFunctor, Quotient.functor,
      Quiv.adj, Quiv.id_eq_id]
    change OneTruncation.ofNerve.map (ev02₂ φ) =
      OneTruncation.ofNerve.map (ev01₂ φ) ≫ OneTruncation.ofNerve.map (ev12₂ φ)
    simp [OneTruncation.ofNerve.map]
    exact φ.map_comp (X := (0 : Fin 3)) (Y := 1) (Z := 2)
      (homOfLE (by decide)) (homOfLE (by decide))

@[simp]
theorem nerve₂Adj.counit.component_eq (C : Cat) :
    SSet.hoFunctor₂Obj.quotientFunctor (nerve₂ C) ⋙ nerve₂Adj.counit.component.{u} C =
    (whiskerRight forgetToReflQuiv.natIso.hom _ ≫
      ReflQuiv.adj.{u}.counit).app C := rfl

theorem nerve₂Adj.counit.naturality' ⦃C D : Cat.{u, u}⦄ (F : C ⟶ D) :
    (nerveFunctor₂ ⋙ SSet.hoFunctor₂).map F ⋙ nerve₂Adj.counit.component D =
      nerve₂Adj.counit.component C ⋙ F := by
  apply SSet.hoFunctor₂Obj.lift_unique'
  have := SSet.hoFunctor₂_naturality (nerveFunctor₂.map F)
  conv => lhs; rw [← Functor.assoc]; lhs; exact this.symm
  simp only [Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, Functor.comp_map]
  rw [← Functor.assoc _ _ F]
  conv => rhs; lhs; exact (nerve₂Adj.counit.component_eq C)
  conv => rhs; exact ((whiskerRight forgetToReflQuiv.natIso.hom Cat.freeRefl ≫ ReflQuiv.adj.counit).naturality F).symm
  simp only [component, Cat.freeRefl_obj_α, ReflQuiv.of_val, NatTrans.comp_app, comp_obj,
    ReflQuiv.forget_obj, id_obj, whiskerRight_app, Cat.comp_eq_comp, Functor.comp_map, Functor.assoc,
    hoFunctor₂Obj.quotientFunctor, Cat.freeRefl_obj_α, ReflQuiv.of_val]
  rw [Quotient.lift_spec]

def nerve₂Adj.counit : nerveFunctor₂ ⋙ SSet.hoFunctor₂.{u} ⟶ (𝟭 Cat) where
  app := nerve₂Adj.counit.component
  naturality := nerve₂Adj.counit.naturality'

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

def toNerve₂.mk.app {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (n : Δ 2) :
    X.obj (op n) ⟶ (nerveFunctor₂.obj C).obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => .mk₀ (F.obj x)
  | 1 => exact fun f => .mk₁ (F.map ⟨f, rfl, rfl⟩)
  | 2 => exact fun φ => .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ))

@[simp] theorem toNerve₂.mk.app_zero {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (x : X _[0]₂) :
    mk.app F [0]₂ x = .mk₀ (F.obj x) := rfl

@[simp] theorem toNerve₂.mk.app_one {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (f : X _[1]₂) :
    mk.app F [1]₂ f = .mk₁ (F.map ⟨f, rfl, rfl⟩) := rfl

@[simp] theorem toNerve₂.mk.app_two {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (φ : X _[2]₂) :
    mk.app F [2]₂ φ = .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ)) := rfl

/-- This is similiar to one of the famous Segal maps, except valued in a product rather than a pullback.-/
def nerve₂.seagull (C : Cat.{v, u}) :
    (nerveFunctor₂.obj C).obj (op [2]₂) ⟶
    (nerveFunctor₂.obj C).obj (op [1]₂) ⨯ (nerveFunctor₂.obj C).obj (op [1]₂) :=
  prod.lift ((nerveFunctor₂.obj C).map (.op δ2₂)) ((nerveFunctor₂.obj C).map (.op δ0₂))

instance (C : Cat) : Mono (nerve₂.seagull C) where
  right_cancellation {X} (f g : X → ComposableArrows C 2) eq := by
    ext x
    simp [nerve₂.seagull] at eq
    have eq1 := congr($eq ≫ prod.fst)
    have eq2 := congr($eq ≫ prod.snd)
    simp at eq1 eq2
    replace eq1 := congr_fun eq1 x
    replace eq2 := congr_fun eq2 x
    simp at eq1 eq2
    generalize f x = fx at *
    generalize g x = gx at *
    fapply ComposableArrows.ext₂
    · exact congrArg (·.obj 0) <| eq1
    · exact congrArg (·.obj 1) <| eq1
    · exact congrArg (·.obj 1) <| eq2
    · exact (conj_eqToHom_iff_heq' ..).2 (congr_arg_heq (·.hom) <| eq1)
    · exact (conj_eqToHom_iff_heq' ..).2 (congr_arg_heq (·.hom) <| eq2)

@[simps!] def toNerve₂.mk {X : SSet.Truncated.{u} 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (ev02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C where
      app := fun n => toNerve₂.mk.app F n.unop
      naturality := by
        rintro ⟨⟨m, hm⟩⟩ ⟨⟨n, hn⟩⟩ ⟨α : (⟨n, hn⟩ : Δ 2) ⟶ ⟨m, hm⟩⟩
        rw [show Opposite.op α = α.op by rfl]
        induction' m using SimplexCategory.rec with m
        induction' n using SimplexCategory.rec with n
        dsimp at α ⊢
        let OK {n m hn hm} (f : (⟨[n], hn⟩ : Δ 2) ⟶ ⟨[m], hm⟩) :=
          X.map f.op ≫ mk.app F ⟨[n], hn⟩ = mk.app F ⟨[m], hm⟩ ≫ (nerveFunctor₂.obj C).map f.op
        show OK α
        have fac : ∀ {n m hn hm} {α : (⟨[n], hn⟩ : Δ 2) ⟶ ⟨[m], hm⟩} k hk
            {β : (⟨[n], hn⟩ : Δ 2) ⟶ ⟨[k], hk⟩}
            {γ : (⟨[k], hk⟩ : Δ 2) ⟶ ⟨[m], hm⟩},
            α = β ≫ γ → OK β → OK γ → OK α := by
          rintro _ _ _ _ _ k hk β γ rfl h1 h2
          dsimp only [OK] at h1 h2 ⊢
          rw [op_comp, map_comp, map_comp, assoc, h1, ← assoc, h2, assoc]
        have const10 (α : [1]₂ ⟶ [0]₂) : OK α := by
          ext x
          cases SimplexCategory.eq_const_to_zero α
          dsimp
          fapply ComposableArrows.ext₁
          · simp only [ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
            congr 1
            refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
            rw [← map_comp, ← map_id]; congr 1
            apply Quiver.Hom.unop_inj
            apply SimplexCategory.hom_zero_zero
          · simp only [ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
            congr 1
            refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
            rw [← map_comp, ← map_id]; congr 1
            apply Quiver.Hom.unop_inj
            apply SimplexCategory.hom_zero_zero
          · refine eq_of_heq <|
              (?_ : HEq _ (ComposableArrows.mk₁ (C := C) (𝟙rq (F.obj x))).hom).trans ?_
            · have : ∀ x' a b (h : _ = a ∧ _ = b), x = a → x = b → x' = X.map (σ₂ (n := 0) 0).op x →
                HEq (ComposableArrows.mk₁ (C := C) (F.map ⟨x', h⟩)).hom
                  (ComposableArrows.mk₁ (C := C) (𝟙rq (F.obj x))).hom := by
                rintro _ _ _ _ rfl rfl rfl
                exact congr_arg_heq (fun a => (ComposableArrows.mk₁ (C := C) a).hom) (F.map_id x)
              apply this
              · simp only [SimplexCategory.len_mk]
                refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
                rw [← map_comp, ← map_id]; congr 1
                exact Quiver.Hom.unop_inj (SimplexCategory.hom_zero_zero _)
              · simp only [SimplexCategory.len_mk]
                refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
                rw [← map_comp, ← map_id]; congr 1
                exact Quiver.Hom.unop_inj (SimplexCategory.hom_zero_zero _)
              · rw [← eq_const_to_zero]
            · simp; rfl
        have const01 (α : [0]₂ ⟶ [1]₂) : OK α := by
          ext x
          apply ComposableArrows.ext₀
          simp only [SimplexCategory.len_mk]
          obtain ⟨i : Fin 2, rfl⟩ := eq_const_of_zero' α
          match i with
          | 0 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [1] 0 = δ₂ 1))
            ext i; match i with | 0 => rfl
          | 1 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [1] 1 = δ₂ 0))
            ext i; match i with | 0 => rfl
        have const02 (α : [0]₂ ⟶ [2]₂) : OK α := by
          ext x
          apply ComposableArrows.ext₀
          obtain ⟨i : Fin 3, rfl⟩ := eq_const_of_zero' α
          match i with
          | 0 =>
            revert x; intro f
            refine congrArg F.obj (?_ : _ = X.map _ _)
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 0 = ι0₂))
            ext i; match i with | 0 => rfl
          | 1 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 1 = ι1₂))
            ext i; match i with | 0 => rfl
          | 2 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 2 = ι2₂))
            ext i; match i with | 0 => rfl
        have nat1m {m hm} (α : [1]₂ ⟶ ⟨[m], hm⟩) : OK α := by
          match m with
          | 0 => apply const10
          | 1 =>
            match α, eq_of_one_to_one α with
            | _, .inr rfl =>
              dsimp [OK]
              rw [(_ : X.map _ = id), (_ : Prefunctor.map _ _ = id)]; rfl
              all_goals apply map_id
            | _, .inl ⟨i, rfl⟩ =>
              exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const01 ..)
          | 2 =>
            match α, eq_of_one_to_two α with
            | _, .inl rfl =>
              ext x
              simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
              fapply ComposableArrows.ext₁
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp only [nerveFunctor₂, truncation, comp_obj, nerveFunctor_obj,
                  whiskeringLeft_obj_obj, Functor.comp_map, nerve_map,
                  ComposableArrows.whiskerLeft_map, ComposableArrows.precomp_map]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨1, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp, ← op_comp]; congr 2
                  ext (i : Fin 1); match i with | 0 => rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inl rfl) =>
              ext x
              simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
              fapply ComposableArrows.ext₁
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp only [nerveFunctor₂, truncation, comp_obj, nerveFunctor_obj,
                  whiskeringLeft_obj_obj, Functor.comp_map, nerve_map,
                  ComposableArrows.whiskerLeft_map, ComposableArrows.precomp_map]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                refine HEq.trans ?_ (heq_of_eq (hyp x))
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inr (.inl rfl)) =>
              ext x
              simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
              fapply ComposableArrows.ext₁
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp only [nerveFunctor₂, truncation, comp_obj, nerveFunctor_obj,
                  whiskeringLeft_obj_obj, Functor.comp_map, nerve_map,
                  ComposableArrows.whiskerLeft_map, ComposableArrows.precomp_map]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨1, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp, ← op_comp]; congr 2
                  ext (i : Fin 1); match i with | 0 => rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inr (.inr ⟨i, rfl⟩)) =>
              exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const02 ..)
        have nat2m (α : [2]₂ ⟶ ⟨[m], hm⟩) : OK α := by
          dsimp [OK]
          apply (cancel_mono (nerve₂.seagull _)).1
          simp [nerve₂.seagull]
          congr 1 <;> rw [← map_comp, ← op_comp, ← nat1m, ← nat1m, op_comp, map_comp, assoc]
        match n with
        | 0 =>
          match m with
          | 0 =>
            ext x
            simp [SimplexCategory.rec]
            apply ComposableArrows.ext₀
            simp only [ComposableArrows.obj', ComposableArrows.mk₀_obj]
            cases SimplexCategory.hom_zero_zero α
            congr 1
            exact congr_fun (X.map_id _) x
          | 1 => apply const01
          | 2 => apply const02
        | 1 => apply nat1m
        | 2 => apply nat2m

/-- ER: We might prefer this version where we are missing the analogue of the hypothesis hyp
conjugated by the isomorphism nerve₂Adj.NatIso.app C -/
@[simps!] def toNerve₂.mk' {X : SSet.Truncated.{u} 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := C) ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev01₂ φ))
        ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C :=
  toNerve₂.mk (f ≫ (forgetToReflQuiv.natIso.app C).hom) hyp

theorem oneTruncation₂_toNerve₂Mk' {X : SSet.Truncated 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := C) ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev01₂ φ))
        ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev12₂ φ))) :
    oneTruncation₂.map (toNerve₂.mk' f hyp) = f := by
  refine ReflPrefunctor.ext (fun _ ↦ ComposableArrows.ext₀ rfl)
    (fun X Y g ↦ eq_of_heq (heq_eqRec_iff_heq.2 <| heq_eqRec_iff_heq.2 ?_))
  simp [oneTruncation₂]
  have {A B A' B' : OneTruncation₂ (nerveFunctor₂.obj C)}
      : A = A' → B = B' → ∀ (x : A ⟶ B) (y : A' ⟶ B'), x.1 = y.1 → HEq x y := by
    rintro rfl rfl ⟨⟩ ⟨⟩ ⟨⟩; rfl
  apply this
  · exact ComposableArrows.ext₀ rfl
  · exact ComposableArrows.ext₀ rfl
  · simp
    fapply ComposableArrows.ext₁ <;> simp [ReflQuiv.comp_eq_comp]
    · rw [g.2.1]; exact congr_arg (·.obj 0) (f.map g).2.1.symm
    · rw [g.2.2]; exact congr_arg (·.obj 1) (f.map g).2.2.symm
    · refine (conj_eqToHom_iff_heq' _ _ _ _).2 ?_
      simp [ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map]
      obtain ⟨g, rfl, rfl⟩ := g
      rfl

/-- Now do a case split. For n = 0 and n = 1 this is covered by the hypothesis.
         For n = 2 this is covered by the new lemma above.-/
theorem toNerve₂.ext {X : SSet.Truncated 2} {C : Cat} (f g : X ⟶ nerve₂ C)
    (hyp : SSet.oneTruncation₂.map f = SSet.oneTruncation₂.map g) : f = g := by
  have eq₀ x : f.app (op [0]₂) x = g.app (op [0]₂) x := congr(($hyp).obj x)
  have eq₁ x : f.app (op [1]₂) x = g.app (op [1]₂) x := congr((($hyp).map ⟨x, rfl, rfl⟩).1)
  ext ⟨⟨n, hn⟩⟩ x
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => apply eq₀
  | 1 => apply eq₁
  | 2 =>
    apply Functor.hext (fun i : Fin 3 => ?_) (fun (i j : Fin 3) k => ?_)
    · let pt : [0]₂ ⟶ [2]₂ := SimplexCategory.const _ _ i
      refine congr(($(congr_fun (f.naturality pt.op) x)).obj 0).symm.trans ?_
      refine .trans ?_ congr(($(congr_fun (g.naturality pt.op) x)).obj 0)
      exact congr($(eq₀ _).obj 0)
    · let ar : [1]₂ ⟶ [2]₂ := mkOfLe _ _ k.le
      have h1 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (f.naturality (op ar)) x)
      have h2 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (g.naturality (op ar)) x)
      exact h1.symm.trans <| .trans (congr_arg_heq (fun x => x.map' 0 1) (eq₁ _)) h2

/-- ER: This is dumb. -/
theorem toNerve₂.ext' {X : SSet.Truncated 2} {C : Cat} (f g : X ⟶ nerveFunctor₂.obj C)
    (hyp : SSet.oneTruncation₂.map f = SSet.oneTruncation₂.map g) : f = g := by
  let f' : X ⟶ nerve₂ C := f
  let g' : X ⟶ nerve₂ C := g
  exact toNerve₂.ext f' g' hyp

-- @[simps! toPrefunctor obj map]
def nerve₂Adj.unit.component (X : SSet.Truncated.{u} 2) :
    X ⟶ nerveFunctor₂.obj (SSet.hoFunctor₂.obj X) := by
  fapply toNerve₂.mk' (C := SSet.hoFunctor₂.obj X)
  · exact (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor ⋙rq
    (forgetToReflQuiv.natIso).inv.app (SSet.hoFunctor₂.obj X))
  · exact fun φ ↦ Quotient.sound _ (HoRel₂.mk φ)

theorem nerve₂Adj.unit.component_eq (X : SSet.Truncated.{u} 2) :
    SSet.oneTruncation₂.map (nerve₂Adj.unit.component X) =
    ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor ⋙rq
    (forgetToReflQuiv.natIso).inv.app (SSet.hoFunctor₂.obj X) := oneTruncation₂_toNerve₂Mk' ..

def nerve₂Adj.unit : 𝟭 (SSet.Truncated.{u} 2) ⟶ hoFunctor₂ ⋙ nerveFunctor₂ where
  app := nerve₂Adj.unit.component
  naturality := by
    refine fun V W f ↦ toNerve₂.ext' (f ≫ nerve₂Adj.unit.component W)
      (nerve₂Adj.unit.component V ≫ nerveFunctor₂.map (hoFunctor₂.map f)) ?_
    rw [Functor.map_comp, Functor.map_comp, nerve₂Adj.unit.component_eq,
      nerve₂Adj.unit.component_eq]
    have nat₁ := (forgetToReflQuiv.natIso).inv.naturality (hoFunctor₂.map f)
    repeat rw [← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _)]
    repeat rw [assoc]
    simp at nat₁
    rw [← nat₁]
    rfl

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
nonrec def nerve₂Adj : SSet.hoFunctor₂.{u} ⊣ nerveFunctor₂ := by
  refine Adjunction.mkOfUnitCounit {
    unit := nerve₂Adj.unit
    counit := nerve₂Adj.counit
    left_triangle := ?_
    right_triangle := ?_
  }
  · ext X
    apply SSet.hoFunctor₂Obj.lift_unique'
    simp only [id_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, NatTrans.comp_app,
      whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp, NatTrans.id_app']
    rw [← Cat.comp_eq_comp (SSet.hoFunctor₂Obj.quotientFunctor X) (𝟙 (SSet.hoFunctor₂.obj X)),
      comp_id, Cat.comp_eq_comp, ← Functor.assoc]
    conv => lhs; lhs; exact (SSet.hoFunctor₂_naturality (nerve₂Adj.unit.component X)).symm
    simp only [comp_obj, Cat.freeRefl_obj_α, Functor.comp_map]
    rw [nerve₂Adj.unit.component_eq X, Functor.assoc]
    conv => lhs; rhs; exact (nerve₂Adj.counit.component_eq (SSet.hoFunctor₂.obj X))
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc, NatTrans.comp_app, id_obj, whiskerRight_app]
    rw [← Cat.comp_eq_comp, ← assoc, ← Cat.freeRefl.map_comp, ReflQuiv.comp_eq_comp, ReflPrefunctor.comp_assoc]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp]
    simp only [ReflQuiv.forget_obj, comp_obj, Iso.inv_hom_id_app]
    rw [ReflQuiv.id_eq_id]
    simp_rw [ReflPrefunctor.comp_id
      (U := ReflQuiv.of _) (V := ReflQuiv.of ↑(SSet.hoFunctor₂.obj X))
      ((SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor)]
    rw [← ReflQuiv.comp_eq_comp (Z := ReflQuiv.of _)
      (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X))
      ((SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor)]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, map_comp, assoc]
    have nat := ReflQuiv.adj.counit.naturality
      (X := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ X)))
      (Y := SSet.hoFunctor₂.obj X) (SSet.hoFunctor₂Obj.quotientFunctor X)
    dsimp at nat
    rw [nat, ← assoc]
    conv => lhs; lhs; apply ReflQuiv.adj.left_triangle_components (SSet.oneTruncation₂.obj X)
    simp
  · refine NatTrans.ext (funext fun C ↦ ?_)
    simp only [comp_obj, id_obj, NatTrans.comp_app, whiskerLeft_app, associator_inv_app,
      whiskerRight_app, id_comp, NatTrans.id_app']
    apply toNerve₂.ext
    simp only [map_comp, map_id]
    rw [nerve₂Adj.unit, nerve₂Adj.unit.component_eq]
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp, ← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _)
      (Z := ReflQuiv.of _), assoc, assoc, ← Functor.comp_map,
        ← forgetToReflQuiv.natIso.inv.naturality]
    conv => lhs; rhs; rw [← assoc] --
    show _ ≫ (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map _) ≫ _ = _
    rw [← ReflQuiv.forget.map_comp]
    show _ ≫ ReflQuiv.forget.map (SSet.hoFunctor₂Obj.quotientFunctor (nerve₂ ↑C)
      ⋙ nerve₂Adj.counit.app C) ≫ _ = _
    rw [nerve₂Adj.counit, nerve₂Adj.counit.component_eq]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, NatTrans.comp_app,
      comp_obj, id_obj, whiskerRight_app]
    rw [ReflQuiv.forget.map_comp, ← Functor.comp_map, ← assoc, ← assoc]
    have := ReflQuiv.adj.unit.naturality (forgetToReflQuiv.natIso.hom.app C)
    simp only [Functor.comp_obj] at this
    conv => lhs; lhs; lhs; apply this.symm
    simp only [Cat.freeRefl_obj_α, id_obj, Functor.id_map]
    slice_lhs 2 3 => rw [ReflQuiv.adj.right_triangle_components C]
    simp

instance nerveFunctor₂.faithful : nerveFunctor₂.{u, u}.Faithful := by
  haveI lem := ReflQuiv.forget.Faithful -- TODO: why is this needed
  exact Functor.Faithful.of_comp_iso
    (G := oneTruncation₂) (H := ReflQuiv.forget) forgetToReflQuiv.natIso

instance nerveFunctor₂.full : nerveFunctor₂.{u, u}.Full where
  map_surjective := by
    intro X Y F
    let uF := SSet.oneTruncation₂.map F
    let uF' : X ⥤rq Y :=
      forgetToReflQuiv.natIso.inv.app X ≫ uF ≫ forgetToReflQuiv.natIso.hom.app Y
    have {a b c : X} (h : a ⟶ b) (k : b ⟶ c) :
        uF'.map (h ≫ k) = uF'.map h ≫ uF'.map k := by
      let hk := ComposableArrows.mk₂ h k
      let Fh : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ h)
      let Fk : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ k)
      let Fhk' : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ (h ≫ k))
      let Fhk : ComposableArrows Y 2 := F.app (op [2]₂) hk
      have lem0 := congr_fun (F.naturality δ0₂.op) hk
      have lem1 := congr_fun (F.naturality δ1₂.op) hk
      have lem2 := congr_fun (F.naturality δ2₂.op) hk
      replace lem0 := congr_arg_heq (·.map' 0 1) lem0
      replace lem1 := congr_arg_heq (·.map' 0 1) lem1
      replace lem2 := congr_arg_heq (·.map' 0 1) lem2
      have eq0 : (nerveFunctor₂.obj X).map δ0₂.op hk = .mk₁ k := by
        apply ComposableArrows.ext₁ rfl rfl
        simp [nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂]
      have eq2 : (nerveFunctor₂.obj X).map δ2₂.op hk = .mk₁ h := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂]; rfl
      have eq1 : (nerveFunctor₂.obj X).map δ1₂.op hk = .mk₁ (h ≫ k) := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂]; rfl
      simp at lem0 lem1 lem2
      rw [eq0] at lem0
      rw [eq1] at lem1
      rw [eq2] at lem2
      replace lem0 : HEq (uF'.map k) (Fhk.map' 1 2) := by
        refine HEq.trans (b := Fk.map' 0 1) ?_ lem0
        simp [uF', nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF]
        rfl
      replace lem2 : HEq (uF'.map h) (Fhk.map' 0 1) := by
        refine HEq.trans (b := Fh.map' 0 1) ?_ lem2
        simp [uF', nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF]
        rfl
      replace lem1 : HEq (uF'.map (h ≫ k)) (Fhk.map' 0 2) := by
        refine HEq.trans (b := Fhk'.map' 0 1) ?_ lem1
        simp [uF', nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF]
        rfl
      rw [Fhk.map'_comp 0 1 2] at lem1
      refine eq_of_heq (lem1.trans (heq_comp ?_ ?_ ?_ lem2.symm lem0.symm))
      · simp [uF', nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι0₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left,
          nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
      · simp [uF', nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι1₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left,
          nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
      · simp [uF', nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι2₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left,
          nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
    let fF : X ⥤ Y := ReflPrefunctor.toFunctor uF' this
    have eq : fF.toReflPrefunctor = uF' := rfl
    refine ⟨fF, toNerve₂.ext' (nerveFunctor₂.map fF) F ?_⟩
    · have nat := forgetToReflQuiv.natIso.hom.naturality fF
      simp [eq, uF', uF] at nat
      exact (Iso.cancel_iso_hom_right (oneTruncation₂.map (nerveFunctor₂.map fF))
        (oneTruncation₂.map F) (forgetToReflQuiv.natIso.app Y)).mp nat

instance nerveFunctor₂.fullyfaithful : nerveFunctor₂.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor₂

instance nerve₂Adj.reflective : Reflective nerveFunctor₂.{u, u} :=
  Reflective.mk SSet.hoFunctor₂ nerve₂Adj

end

def nerveAdjunction : SSet.hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((coskAdj 2).comp nerve₂Adj) Nerve.cosk2Iso.symm

/-- Repleteness exists for full and faithful functors but not fully faithful functors, which is
why we do this inefficiently.-/
instance nerveFunctor.faithful : nerveFunctor.{u, u}.Faithful := by
  have := coskeleton.faithful 2
  exact Functor.Faithful.of_iso (F := (nerveFunctor₂.{u, u} ⋙ ran (Δ.ι 2).op)) Nerve.cosk2Iso.symm

instance nerveFunctor.full : nerveFunctor.{u, u}.Full := by
  have := coskeleton.full 2
  exact Functor.Full.of_iso (F := (nerveFunctor₂.{u, u} ⋙ ran (Δ.ι 2).op)) Nerve.cosk2Iso.symm

instance nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor

instance nerveCounit_isIso : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

def nerveCounitNatIso : nerveFunctor ⋙ SSet.hoFunctor ≅ 𝟭 Cat := asIso (nerveAdjunction.counit)

instance : Reflective nerveFunctor where
  L := SSet.hoFunctor
  adj := nerveAdjunction

-- NB: Moved to CategoryTheory.Category.Cat.Limits
instance : HasColimits Cat.{u, u} :=
  hasColimits_of_reflective nerveFunctor

end
