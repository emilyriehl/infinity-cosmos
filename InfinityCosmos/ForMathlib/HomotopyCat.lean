import InfinityCosmos.Mathlib.AlgebraicTopology.Nerve
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Opposites
import Mathlib.Tactic.LiftLets
import InfinityCosmos.ForMathlib.Wombat

noncomputable section

namespace CategoryTheory
open Category Limits Functor
universe v v₁ v₂ u u₁ u₂

section
theorem Functor.id_eq_id (X : Cat) : 𝟙 X = 𝟭 X := rfl
theorem Functor.comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

theorem Quiv.id_eq_id (X : Quiv) : 𝟙 X = 𝟭q X := rfl
theorem Quiv.comp_eq_comp {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙q G := rfl

@[simp] theorem Cat.of_α (C) [Category C] : (of C).α = C := rfl

theorem conj_eqToHom_iff_heq' {C} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : Z = X) :
    f = eqToHom h ≫ g ≫ eqToHom h' ↔ HEq f g := conj_eqToHom_iff_heq _ _ _ h'.symm

theorem eqToHom_comp_heq {C} [Category C] {W X Y : C}
    (f : Y ⟶ X) (h : W = Y) : HEq (eqToHom h ≫ f) f := by
  rw [← conj_eqToHom_iff_heq _ _ h rfl]
  simp

@[simp] theorem eqToHom_comp_heq_iff {C} [Category C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    HEq (eqToHom h ≫ f) g ↔ HEq f g :=
  ⟨(eqToHom_comp_heq ..).symm.trans, (eqToHom_comp_heq ..).trans⟩

@[simp] theorem heq_eqToHom_comp_iff {C} [Category C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    HEq g (eqToHom h ≫ f) ↔ HEq g f :=
  ⟨(·.trans (eqToHom_comp_heq ..)), (·.trans (eqToHom_comp_heq ..).symm)⟩

theorem comp_eqToHom_heq {C} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (h : Y = Z) : HEq (f ≫ eqToHom h) f := by
  rw [← conj_eqToHom_iff_heq' _ _ rfl h]
  simp

@[simp] theorem comp_eqToHom_heq_iff {C} [Category C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    HEq (f ≫ eqToHom h) g ↔ HEq f g :=
  ⟨(comp_eqToHom_heq ..).symm.trans, (comp_eqToHom_heq ..).trans⟩

@[simp] theorem heq_comp_eqToHom_iff {C} [Category C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    HEq g (f ≫ eqToHom h) ↔ HEq g f :=
  ⟨(·.trans (comp_eqToHom_heq ..)), (·.trans (comp_eqToHom_heq ..).symm)⟩

theorem heq_comp {C} [Category C] {X Y Z X' Y' Z' : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (eq1 : X = X') (eq2 : Y = Y') (eq3 : Z = Z')
    (H1 : HEq f f') (H2 : HEq g g') :
    HEq (f ≫ g) (f' ≫ g') := by
  cases eq1; cases eq2; cases eq3; cases H1; cases H2; rfl

end

namespace Quotient
variable {C : Type _} [Category C] (r : HomRel C)

theorem CompClosure.congruence : Congruence fun a b => EqvGen (@CompClosure C _ r a b) where
  equivalence := EqvGen.is_equivalence _
  compLeft f g g' rel := by
    induction rel with
    | rel _ _ h =>
      let .intro f' m₁ m₂ g h := h
      apply EqvGen.rel
      rw [← assoc, ← assoc f]
      exact ⟨_, _, _, _, h⟩
    | refl => exact EqvGen.refl _
    | symm _ _ _ ih => exact EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂
  compRight g rel := by
    induction rel with
    | rel _ _ h =>
      let .intro f' m₁ m₂ g h := h
      apply EqvGen.rel
      repeat rw [assoc]
      exact ⟨_, _, _, _, h⟩
    | refl => exact EqvGen.refl _
    | symm _ _ _ ih => exact EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

end Quotient

@[pp_with_univ]
class ReflQuiver (obj : Type u) extends Quiver.{v} obj : Type max u v where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙rq" => ReflQuiver.id  -- type as \b1

instance catToReflQuiver {C : Type u} [inst : Category.{v} C] : ReflQuiver.{v+1, u} C :=
  { inst with }

@[simp] theorem ReflQuiver.id_eq_id {C : Type*} [Category C] (X : C) : 𝟙rq X = 𝟙 X := rfl

/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `Prefunctor`. -/
structure ReflPrefunctor (V : Type u₁) [ReflQuiver.{v₁} V] (W : Type u₂) [ReflQuiver.{v₂} W]
    extends Prefunctor V W where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : V, map (𝟙rq X) = 𝟙rq (obj X) := by aesop_cat

namespace ReflPrefunctor

-- Porting note: added during port.
-- These lemmas can not be `@[simp]` because after `whnfR` they have a variable on the LHS.
-- Nevertheless they are sometimes useful when building functors.
lemma mk_obj {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V → W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl

lemma mk_map {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V → W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

-- @[ext]
theorem ext {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W] {F G : ReflPrefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨⟨F_obj⟩⟩ := F
  obtain ⟨⟨G_obj⟩⟩ := G
  obtain rfl : F_obj = G_obj := (Set.eqOn_univ F_obj G_obj).mp fun _ _ ↦ h_obj _
  congr
  funext X Y f
  simpa using h_map X Y f

/-- The identity morphism between quivers. -/
@[simps!]
def id (V : Type*) [ReflQuiver V] : ReflPrefunctor V V where
  __ := Prefunctor.id _
  map_id _ := rfl

instance (V : Type*) [ReflQuiver V] : Inhabited (ReflPrefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers. -/
@[simps!]
def comp {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [ReflQuiver W]
    (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) : ReflPrefunctor U W where
  __ := F.toPrefunctor.comp G.toPrefunctor
  map_id _ := by simp [F.map_id, G.map_id]

@[simp]
theorem comp_id {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
theorem id_comp {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
theorem comp_assoc {U V W Z : Type*} [ReflQuiver U] [ReflQuiver V] [ReflQuiver W] [ReflQuiver Z]
    (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) (H : ReflPrefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) := rfl

/-- Notation for a prefunctor between quivers. -/
infixl:50 " ⥤rq " => ReflPrefunctor

/-- Notation for composition of prefunctors. -/
infixl:60 " ⋙rq " => ReflPrefunctor.comp

/-- Notation for the identity prefunctor on a quiver. -/
notation "𝟭rq" => id

theorem congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
    (h : f = g) : F.map f = F.map g := congrArg F.map h

end ReflPrefunctor

def Functor.toReflPrefunctor {C D} [Category C] [Category D] (F : C ⥤ D) : C ⥤rq D := { F with }

@[simp]
theorem Functor.toReflPrefunctor_toPrefunctor {C D : Cat} (F : C ⥤ D) :
    (Functor.toReflPrefunctor F).toPrefunctor = F.toPrefunctor := rfl

namespace ReflQuiver
open Opposite

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [ReflQuiver V] : ReflQuiver Vᵒᵖ where
   id X := op (𝟙rq X.unop)

instance discreteQuiver (V : Type u) : ReflQuiver.{u+1} (Discrete V) := { discreteCategory V with }

end ReflQuiver

@[nolint checkUnivs]
def ReflQuiv :=
  Bundled ReflQuiver.{v + 1, u}

namespace ReflQuiv

instance : CoeSort ReflQuiv (Type u) where coe := Bundled.α

instance str' (C : ReflQuiv.{v, u}) : ReflQuiver.{v + 1, u} C := C.str

def toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u} := Quiv.of C.α

/-- Construct a bundled `ReflQuiv` from the underlying type and the typeclass. -/
def of (C : Type u) [ReflQuiver.{v + 1} C] : ReflQuiv.{v, u} := Bundled.of C

instance : Inhabited ReflQuiv := ⟨ReflQuiv.of (Discrete default)⟩

@[simp] theorem of_val (C : Type u) [ReflQuiver C] : (ReflQuiv.of C) = C := rfl

/-- Category structure on `ReflQuiv` -/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G

theorem id_eq_id (X : ReflQuiv) : 𝟙 X = 𝟭rq X := rfl
theorem comp_eq_comp {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙rq G := rfl

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toReflPrefunctor

theorem forget_faithful {C D : Cat.{v, u}} (F G : C ⥤ D)
    (hyp : forget.map F = forget.map G) : F = G := by
  cases F
  cases G
  cases hyp
  rfl

theorem forget.Faithful : Functor.Faithful (forget) where
  map_injective := fun hyp ↦ forget_faithful _ _ hyp

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  obj V := Quiv.of V
  map F := F.toPrefunctor

theorem forgetToQuiv_faithful {V W : ReflQuiv} (F G : V ⥤rq W)
    (hyp : forgetToQuiv.map F = forgetToQuiv.map G) : F = G := by
  cases F
  cases G
  cases hyp
  rfl

theorem forgetToQuiv.Faithful : Functor.Faithful (forgetToQuiv) where
  map_injective := fun hyp ↦ forgetToQuiv_faithful _ _ hyp

theorem forget_forgetToQuiv : forget ⋙ forgetToQuiv = Quiv.forget := rfl

end ReflQuiv

namespace ReflPrefunctor

def toFunctor {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D))
    (hyp : ∀ {X Y Z : ↑C} (f : X ⟶ Y) (g : Y ⟶ Z),
      F.map (CategoryStruct.comp (obj := C) f g) =
        CategoryStruct.comp (obj := D) (F.map f) (F.map g)) : C ⥤ D where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := hyp

end ReflPrefunctor
namespace Cat

inductive FreeReflRel {V} [ReflQuiver V] : (X Y : Paths V) → (f g : X ⟶ Y) → Prop
  | mk {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

def FreeReflObj (V) [ReflQuiver V] :=
  Quotient (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V))

instance (V) [ReflQuiver V] : Category (FreeReflObj V) :=
  inferInstanceAs (Category (Quotient _))

def FreeReflObj.quotientFunctor (V) [ReflQuiver V] : Cat.free.obj (Quiv.of V) ⥤ FreeReflObj V :=
  Quotient.functor (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V))

theorem FreeReflObj.lift_unique' {V} [ReflQuiver V] {D} [Category D] (F₁ F₂ : FreeReflObj V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h

@[simps!]
def freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (FreeReflObj V)
  map f := Quotient.lift _ ((by exact Cat.free.map f.toPrefunctor) ⋙ FreeReflObj.quotientFunctor _)
    (fun X Y f g hfg => by
      apply Quotient.sound
      cases hfg
      simp [ReflPrefunctor.map_id]
      constructor)
  map_id X := by
    simp
    symm
    apply Quotient.lift_unique
    refine (Functor.comp_id _).trans <| (Functor.id_comp _).symm.trans ?_
    congr 1
    exact (free.map_id X.toQuiv).symm
  map_comp {X Y Z} f g := by
    simp
    symm
    apply Quotient.lift_unique
    have : free.map (f ≫ g).toPrefunctor =
        free.map (X := X.toQuiv) (Y := Y.toQuiv) f.toPrefunctor ⋙
        free.map (X := Y.toQuiv) (Y := Z.toQuiv) g.toPrefunctor := by
      show _ = _ ≫ _
      rw [← Functor.map_comp]; rfl
    rw [this]; simp [Functor.assoc]
    show _ ⋙ _ ⋙ _ = _
    rw [← Functor.assoc, Quotient.lift_spec, Functor.assoc,
      FreeReflObj.quotientFunctor, Quotient.lift_spec]

theorem freeRefl_naturality {X Y} [ReflQuiver X] [ReflQuiver Y] (f : X ⥤rq Y) :
    free.map (X := Quiv.of X) (Y := Quiv.of Y) f.toPrefunctor ⋙
    FreeReflObj.quotientFunctor ↑Y =
    FreeReflObj.quotientFunctor ↑X ⋙ freeRefl.map (X := ReflQuiv.of X) (Y := ReflQuiv.of Y) f := by
  simp only [free_obj, of_α, FreeReflObj.quotientFunctor, freeRefl, ReflQuiv.of_val]
  rw [Quotient.lift_spec]

def freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  app V := FreeReflObj.quotientFunctor V
  naturality _ _ f := freeRefl_naturality f

end Cat

namespace ReflQuiv

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!

/-- ER: Universe error is why this is for u u.-/
@[simps! toPrefunctor obj map]
def adj.unit.app (V : ReflQuiv.{max u v, u}) : V ⥤rq forget.obj (Cat.freeRefl.obj V) where
  toPrefunctor := Quiv.adj.unit.app (V.toQuiv) ⋙q
    Quiv.forget.map (Cat.FreeReflObj.quotientFunctor V)
  map_id := fun X => by
    apply Quotient.sound
    simp [ReflPrefunctor.map_id]
    constructor

/-- ER: This is used in the proof of both triangle equalities. Should we simp?-/
theorem adj.unit.component_eq (V : ReflQuiv.{max u v, u}) :
    forgetToQuiv.map (adj.unit.app V) = Quiv.adj.unit.app (V.toQuiv) ≫
    Quiv.forget.map (Y := Cat.of _) (Cat.FreeReflObj.quotientFunctor V) := rfl

@[simps!]
def adj.counit.app (C : Cat) : Cat.freeRefl.obj (forget.obj C) ⥤ C := by
  fapply Quotient.lift
  · exact Quiv.adj.counit.app C
  · intro x y f g rel
    cases rel
    unfold Quiv.adj
    simp only [id_obj, forget_obj, Cat.free_obj, Quiv.forget_obj,
      Adjunction.mkOfHomEquiv_counit_app, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk, Quiv.lift_obj,
      ReflQuiver.id_eq_id, Quiv.lift_map, Prefunctor.mapPath_toPath, composePath_toPath,
      Prefunctor.mapPath_nil, composePath_nil]
    rfl

/-- ER: This is used in the proof of both triangle equalities. Should we simp?-/
@[simp]
theorem adj.counit.component_eq (C : Cat) :
    Cat.FreeReflObj.quotientFunctor C ⋙ adj.counit.app C =
    Quiv.adj.counit.app C := rfl

@[simp]
theorem adj.counit.component_eq' (C) [Category C] :
    Cat.FreeReflObj.quotientFunctor C ⋙ adj.counit.app (Cat.of C) =
    Quiv.adj.counit.app (Cat.of C) := rfl

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
nonrec def adj : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget := by
  refine
    Adjunction.mkOfUnitCounit {
      unit := {
        app := adj.unit.app
        naturality := by
          intro V W f
          exact rfl
      }
      counit := {
        app := adj.counit.app
        naturality := by
          intro C D F
          apply Quotient.lift_unique'
          exact (Quiv.adj.counit.naturality F)
      }
      left_triangle := ?_
      right_triangle := ?_
    }
  · ext V
    apply Cat.FreeReflObj.lift_unique'
    simp only [id_obj, Cat.free_obj, Cat.of_α, comp_obj, Cat.freeRefl_obj_α, NatTrans.comp_app,
      forget_obj, whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp, NatTrans.id_app']
    rw [Functor.id_eq_id, Functor.comp_eq_comp]
    simp only [Cat.freeRefl_obj_α, Functor.comp_id]
    rw [← Functor.assoc, ← Cat.freeRefl_naturality, Functor.assoc]
    dsimp [Cat.freeRefl]
    rw [adj.counit.component_eq' (Cat.FreeReflObj V)]
    conv =>
      enter [1, 1, 2]
      apply (Quiv.comp_eq_comp (X := Quiv.of _) (Y := Quiv.of _) (Z := Quiv.of _) ..).symm
    rw [Cat.free.map_comp]
    show (_ ⋙ ((Quiv.forget ⋙ Cat.free).map (X := Cat.of _) (Y := Cat.of _)
      (Cat.FreeReflObj.quotientFunctor V))) ⋙ _ = _
    rw [Functor.assoc, ← Functor.comp_eq_comp]
    conv => enter [1, 2]; apply Quiv.adj.counit.naturality
    rw [Functor.comp_eq_comp, ← Functor.assoc, ← Functor.comp_eq_comp]
    conv => enter [1, 1]; apply Quiv.adj.left_triangle_components V.toQuiv
    simp [Functor.id_eq_id]
    exact Functor.id_comp _
  · ext C
    simp only [comp_obj, forget_obj, id_obj, NatTrans.comp_app, Cat.freeRefl_obj_α, of_val,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, forget_map, id_comp,
      NatTrans.id_app', forgetToQuiv.map_comp, adj.unit.component_eq, Category.assoc,
      Functor.toReflPrefunctor_toPrefunctor, Quiv.comp_eq_comp, adj.counit.component_eq]
    apply forgetToQuiv_faithful
    exact Quiv.adj.right_triangle_components C

end ReflQuiv

open Simplicial
local notation3:1000 (priority := high) X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

namespace SimplexCategory

abbrev Δ (k : ℕ) := SimplexCategory.Truncated k

instance (k : ℕ) : Category (Δ k) := inferInstanceAs (Category (FullSubcategory ..))

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

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

theorem Fin.le_succ {n} (i : Fin n) : i.castSucc ≤ i.succ := Nat.le_succ i

def Fin.hom_succ {n} (i : Fin n) : i.castSucc ⟶ i.succ := homOfLE (Fin.le_succ i)

def mkOfSucc {n} (i : Fin n) : [1] ⟶ [n] :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i.castSucc | 1 => i.succ
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => by
        simp only [Fin.coe_eq_castSucc]
        exact Fin.le_succ i
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


/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
abbrev Δ.ι (k) : Δ k ⥤ SimplexCategory := SimplexCategory.Truncated.inclusion

instance Δ.ι.op_full (k) : (Δ.ι k).op.Full := inferInstance

instance Δ.ι.op_faithful (k) : (Δ.ι k).op.Faithful := inferInstance

instance Δ.ι.op_fullyFaithful (k) : (Δ.ι k).op.FullyFaithful :=
  FullyFaithful.ofFullyFaithful (ι k).op

theorem eq_const_of_zero {n : SimplexCategory} (f : [0] ⟶ n) :
    f = SimplexCategory.const _ n (f.toOrderHom 0) := by
  apply SimplexCategory.Hom.ext
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

theorem const_fac_thru_zero (n m : SimplexCategory) (i : Fin (m.len + 1)) :
    SimplexCategory.const n m i =
    SimplexCategory.const n [0] 0 ≫ SimplexCategory.const [0] m i := by
  rw [SimplexCategory.const_comp]; rfl

end SimplexCategory

open SimplexCategory

namespace SSet
namespace Truncated

/-- The ulift functor `SSet.Truncated.{u} ⥤ SSet.Truncated.{max u v}` on truncated
simplicial sets. -/
def uliftFunctor (k : ℕ) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

end Truncated

/-- ER: This is called "sk" in SimplicialSet and SimplicialObject, but this is a better name.-/
def truncation (k) : SSet ⥤ SSet.Truncated k := (whiskeringLeft _ _ _).obj (Δ.ι k).op

def skAdj (k) : lan (Δ.ι k).op ⊣ truncation k := lanAdjunction _ _
def coskAdj (k) : truncation k ⊣ ran (Δ.ι k).op := ranAdjunction _ _

instance coskeleton.reflective (k) : IsIso ((coskAdj k).counit) :=
  reflective' (Δ.ι k).op

instance skeleton.reflective (k) : IsIso ((skAdj k).unit) :=
  coreflective' (Δ.ι k).op

instance coskeleton.fullyfaithful (k) : (ran (H := Type) (Δ.ι k).op).FullyFaithful := by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskAdj k)

instance coskeleton.full (k) : (ran (H := Type) (Δ.ι k).op).Full :=
  FullyFaithful.full (coskeleton.fullyfaithful k)

instance coskeleton.faithful (k) : (ran (H := Type) (Δ.ι k).op).Faithful :=
  FullyFaithful.faithful (coskeleton.fullyfaithful k)

instance coskAdj.reflective (k) : Reflective (ran (H := Type) (Δ.ι k).op) :=
  Reflective.mk (truncation k) (coskAdj k)

end SSet

open SSet

def nerveFunctor₂ : Cat ⥤ SSet.Truncated 2 := nerveFunctor ⋙ truncation 2

def nerve₂ (C : Type*) [Category C] : SSet.Truncated 2 := nerveFunctor₂.obj (Cat.of C)

theorem nerve₂_restrictedNerve (C : Type*) [Category C] :
    (Δ.ι 2).op ⋙ (nerve C) = nerve₂ C := rfl

def nerve₂restrictediso (C : Type*) [Category C] :
    (Δ.ι 2).op ⋙ (nerve C) ≅ nerve₂ C := Iso.refl _

namespace Nerve
open Opposite

def nerveRightExtension (C : Cat) : RightExtension (Δ.ι 2).op (nerveFunctor₂.obj C) :=
  RightExtension.mk (nerveFunctor.obj C) (𝟙 ((Δ.ι 2).op ⋙ nerveFunctor.obj C))

def nerveRightExtension.coneAt (C : Cat) (n : ℕ) :
    Cone (StructuredArrow.proj (op ([n] : SimplexCategory)) (Δ.ι 2).op ⋙ nerveFunctor₂.obj C) :=
  RightExtension.coneAt (nerveRightExtension C) (op [n])

section

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : Δ 2))

private
def pt {n} (i : Fin (n + 1)) : ([0] : SimplexCategory) ⟶ [n] := SimplexCategory.const _ _ i

private
def pt' {n} (i : Fin (n + 1)) : StructuredArrow (op [n]) (Δ.ι 2).op :=
  .mk (Y := op [0]₂) (.op (pt i))

private
def ar {n} {i j : Fin (n+1)} (k : i ⟶ j) : [1] ⟶ [n] := mkOfLe _ _ k.le

private
def ar' {n} {i j : Fin (n+1)} (k : i ⟶ j) : StructuredArrow (op [n]) (Δ.ι 2).op :=
  .mk (Y := op [1]₂) (.op (ar k))

private
def arr' {n} (i : Fin n) : StructuredArrow (op [n]) (Δ.ι 2).op := ar' (Fin.hom_succ i)

private
def arr'.dom {n} (i : Fin n) : (arr' i) ⟶ (pt' i.castSucc) := by
  fapply StructuredArrow.homMk
  · exact (.op (SimplexCategory.const _ _ 0))
  · apply Quiver.Hom.unop_inj
    ext z; revert z; intro (0 : Fin 1); rfl

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
    (x : s.pt) : nerve C _[n] := by
  fapply SSet.nerve.mk
  · exact fun i ↦ s.π.app (pt' i) x |>.obj 0
  · exact fun i ↦ eqToHom (ran.lift.eq ..) ≫ (s.π.app (arr' i) x).map' 0 1 ≫
      eqToHom (ran.lift.eq₂ ..).symm

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
      let tri {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : [2] ⟶ [n] :=
          mkOfLeComp _ _ _ f.le g.le
      let tri' {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) :
        StructuredArrow (op [n]) (Δ.ι 2).op :=
          .mk (Y := op [2]₂) (.op (tri f g))
      let facemap₂ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ ar' f := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 2)) ?_
        apply Quiver.Hom.unop_inj
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let facemap₀ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : (tri' f g) ⟶ (ar' g) := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 0)) ?_
        apply Quiver.Hom.unop_inj
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let facemap₁ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : (tri' f g) ⟶ ar' (f ≫ g) := by
        refine StructuredArrow.homMk (.op (SimplexCategory.δ 1)) ?_
        apply Quiver.Hom.unop_inj
        ext z; revert z;
        simp [ar']
        intro | 0 | 1 => rfl
      let tri₀ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' i := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 0)) ?_
        apply Quiver.Hom.unop_inj
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      let tri₁ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' j := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 1)) ?_
        apply Quiver.Hom.unop_inj
        ext z; revert z
        simp [ar']
        intro | 0 => rfl
      let tri₂ {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) : tri' f g ⟶ pt' k := by
        refine StructuredArrow.homMk (.op (SimplexCategory.const [0] _ 2)) ?_
        apply Quiver.Hom.unop_inj
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
      · refine (ran.lift.eq ..).symm.trans ?_
        exact congr($(congr_fun (s.π.naturality (tri₀ f g)) x).obj 0)
      · refine (ran.lift.eq₂ ..).symm.trans ?_
        exact congr($(congr_fun (s.π.naturality (tri₁ f g)) x).obj 0)
      · refine (ran.lift.eq₂ ..).symm.trans ?_
        exact congr($(congr_fun (s.π.naturality (tri₂ f g)) x).obj 0)
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
    · intro; rfl
    · intro i hi
      dsimp only [CategoryTheory.Nerve.ran.lift, SSet.nerve.mk]
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
      rw [eqToHom_refl, eqToHom_refl, id_comp, comp_id]; rfl
  exact eq_of_heq (congr_arg_heq (·.map k) this)

/-- An object j : StructuredArrow (op [n]) (Δ.ι 2).op defines a morphism Fin (jlen+1) -> Fin(n+1).
This calculates the image of i : Fin(jlen+1); we might think of this as j(i). -/
private
def fact.obj.dom {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin ((unop ((Δ.ι 2).op.obj ((StructuredArrow.proj (op [n]) (Δ.ι 2).op).obj j))).len + 1)) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i

/-- This is the unique arrow in StructuredArrow (op [n]) (Δ.ι 2).op from j to pt' of the j(i)
calculated above. This is used to prove that ran.lift defines a factorization on objects.-/
private
def fact.obj.arr {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin ((unop ((Δ.ι 2).op.obj ((StructuredArrow.proj (op [n]) (Δ.ι 2).op).obj j))).len + 1))
    : j ⟶ (pt' (fact.obj.dom j i)) :=
  StructuredArrow.homMk (.op (SimplexCategory.const _ _ i)) <| by
    apply Quiver.Hom.unop_inj
    ext z; revert z; intro | 0 => rfl

/-- An object j : StructuredArrow (op [n]) (Δ.ι 2).op defines a morphism Fin (jlen+1) -> Fin(n+1).
This calculates the image of i.succ : Fin(jlen+1); we might think of this as j(i.succ). -/
private
def fact.map.cod {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin (unop j.right).1.len) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i.succ

/-- The unique arrow (fact.obj.dom j i.castSucc) ⟶ (fact.map.cod j i) in Fin(n+1). -/
private
def fact.map.map {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin (unop j.right).1.len) :
    (fact.obj.dom j i.castSucc) ⟶ (fact.map.cod j i) := by
  let jfun := Monotone.functor (j.hom.unop.toOrderHom).monotone
  exact (jfun.map (Fin.hom_succ i))

/-- This is the unique arrow in StructuredArrow (op [n]) (Δ.ι 2).op from j to ar' of the map just
constructed. This is used to prove that ran.lift defines a factorization on maps.-/
private
def fact.map.arr {n}
    (j : StructuredArrow (op [n]) (Δ.ι 2).op)
    (i : Fin (unop j.right).1.len)
    : j ⟶ ar' (fact.map.map j i) := by
  fapply StructuredArrow.homMk
  · exact .op (mkOfSucc i : [1] ⟶ [(unop j.right).1.len])
  · apply Quiver.Hom.unop_inj
    ext z; revert z
    intro
    | 0 => rfl
    | 1 => rfl

def isPointwiseRightKanExtensionAt (C : Cat.{0}) (n : ℕ) :
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
      refine have obj_eq := ?a; ComposableArrows.ext obj_eq ?b
      · intro i
        have nat := congr_fun (s.π.naturality (fact.obj.arr j i)) x
        have := congrArg (·.obj 0) <| nat
        exact this
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
        -- unfold ar' ar fact.map.arr fact.obj.dom fact.map.cod at nat
        simp at nat
        have := congr_arg_heq (·.map' 0 1) <| nat
        refine (conj_eqToHom_iff_heq' _ _ _ _).2 ?_
        simpa only [Int.reduceNeg, StructuredArrow.proj_obj, op_obj, id_eq, Int.Nat.cast_ofNat_Int,
          Fin.mk_one, Fin.isValue, ComposableArrows.map', Int.reduceAdd, Int.reduceSub,
          Fin.zero_eta, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    uniq := by
      intro s lift' fact'
      ext x
      unfold ran.lift SSet.nerve.mk pt' pt arr' ar' ar
      fapply ComposableArrows.ext
      · intro i
        simp
        have eq := congr_fun (fact' (StructuredArrow.mk (Y := op [0]₂) ([0].const [n] i).op)) x
        simp at eq
        exact (congrArg (·.obj 0) <| eq)
      · intro i hi
        simp only [id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
          SimplexCategory.len_mk, StructuredArrow.proj_obj, StructuredArrow.mk_right, op_obj,
          Fin.zero_eta, Fin.isValue, Fin.mk_one, ComposableArrows.mkOfObjOfMapSucc_obj]
        rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
        have eq := congr_fun (fact' (arr' (Fin.mk i hi))) x
        simp at eq ⊢
        have := congr_arg_heq (·.hom) <| eq
        exact (conj_eqToHom_iff_heq' _ _ _ _).2 this
  }
end

def isPointwiseRightKanExtension (C : Cat) :
    RightExtension.IsPointwiseRightKanExtension (nerveRightExtension C) :=
  fun Δ => isPointwiseRightKanExtensionAt C Δ.unop.len

def isPointwiseRightKanExtension.isUniversal (C : Cat) :
    CostructuredArrow.IsUniversal (nerveRightExtension C) :=
  RightExtension.IsPointwiseRightKanExtension.isUniversal (isPointwiseRightKanExtension C)

-- ER: Universe error I don't understand.
theorem isRightKanExtension (C : Cat.{0,0}) :
    (nerveRightExtension C).left.IsRightKanExtension (nerveRightExtension C).hom :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension C)

/-- ER: The natural map from a nerve. -/
def cosk2NatTrans : nerveFunctor ⟶ nerveFunctor₂ ⋙ ran (Δ.ι 2).op :=
  whiskerLeft nerveFunctor (coskAdj 2).unit

def cosk2RightExtension.hom (C : Cat) :
    (nerveRightExtension C) ⟶
      (RightExtension.mk _ ((Δ.ι 2).op.ranCounit.app ((Δ.ι 2).op ⋙ nerveFunctor.obj C))) := by
  fapply CostructuredArrow.homMk
  · simp only [nerveFunctor_obj, RightExtension.mk_left]
    exact (cosk2NatTrans.app C)
  · exact (coskAdj 2).left_triangle_components (nerveFunctor.obj C)

instance cosk2RightExtension.hom_isIso (C : Cat) :
    IsIso (cosk2RightExtension.hom C) :=
    isIso_of_isTerminal
      (isPointwiseRightKanExtension.isUniversal C)
      (((Δ.ι 2).op.ran.obj ((Δ.ι 2).op ⋙ nerveFunctor.obj C)).isUniversalOfIsRightKanExtension
        ((Δ.ι 2).op.ranCounit.app ((Δ.ι 2).op ⋙ nerveFunctor.obj C)))
      (cosk2RightExtension.hom C)

def cosk2RightExtension.component.hom.iso (C : Cat) :
    (nerveRightExtension C) ≅
      (RightExtension.mk _ ((Δ.ι 2).op.ranCounit.app ((Δ.ι 2).op ⋙ nerveFunctor.obj C))) :=
  (asIso (cosk2RightExtension.hom C))

def cosk2NatIso.component (C : Cat) :
    nerveFunctor.obj C ≅ (ran (Δ.ι 2).op).obj (nerveFunctor₂.obj C) :=
  (CostructuredArrow.proj
    ((whiskeringLeft _ _ _).obj (Δ.ι 2).op) ((Δ.ι 2).op ⋙ nerveFunctor.obj C)).mapIso
      (cosk2RightExtension.component.hom.iso C)

/-- ER: It follows that we have a natural isomorphism between nerveFunctor and nerveFunctor ⋙ cosk₂
whose components are the isomorphisms just established. -/
def cosk2Iso : nerveFunctor ≅ nerveFunctor₂ ⋙ ran (Δ.ι 2).op := by
  apply NatIso.ofComponents cosk2NatIso.component _
  have := cosk2NatTrans.naturality
  exact cosk2NatTrans.naturality

end Nerve

section
open Opposite

def OneTruncation (S : SSet) := S _[0]

def OneTruncation.src {S : SSet} (f : S _[1]) : OneTruncation S :=
  S.map (SimplexCategory.δ (n := 0) 1).op f

def OneTruncation.tgt {S : SSet} (f : S _[1]) : OneTruncation S :=
  S.map (SimplexCategory.δ (n := 0) 0).op f

def OneTruncation.Hom {S : SSet} (X Y : OneTruncation S) :=
  {p : S _[1] // src p = X ∧ tgt p = Y}

instance (S : SSet) : ReflQuiver (OneTruncation S) where
  Hom X Y := OneTruncation.Hom X Y
  id X := by
    refine ⟨S.map (SimplexCategory.σ (n := 0) 0).op X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp]
      rw [(_ : _ ≫ _ = 𝟙 _)]; simp
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
  map_id X := by rfl
  map_comp f g := by rfl

section
variable {C : Type u} [Category.{v} C]
def OneTruncation.ofNerve.map {X Y : OneTruncation (nerve C)}
    (f : X ⟶ Y) : X.left ⟶ Y.left :=
  eqToHom (congrArg (·.left) f.2.1.symm) ≫ f.1.hom ≫ eqToHom (congrArg (·.left) f.2.2)

def OneTruncation.ofNerve.hom : OneTruncation (nerve C) ⥤rq C where
  obj := (·.left)
  map := OneTruncation.ofNerve.map
  map_id := fun X : ComposableArrows _ 0 => by
    simp only [SimplexCategory.len_mk, map, nerve_obj, eqToHom_refl, comp_id, id_comp,
      ReflQuiver.id_eq_id]
    exact ComposableArrows.map'_self _ 0

def OneTruncation.ofNerve.inv : C ⥤rq OneTruncation (nerve C) where
  obj := (.mk₀ ·)
  map := fun f => by
    refine ⟨.mk₁ f, ?_⟩
    constructor <;> apply ComposableArrows.ext <;>
      simp [SimplexCategory.len] <;> (exact fun 0 ↦ rfl)
  map_id := fun X : C => Subtype.ext <| by
    simp; apply ComposableArrows.ext <;> simp
    · rintro _ rfl; simp; rfl
    · intro; split <;> rfl

def OneTruncation.ofNerve (C : Type u) [Category.{u} C] :
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
    · exact fun _ ↦ ComposableArrows.ext₀ (by rfl)
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      apply Subtype.ext
      simp [ReflQuiv.comp_eq_comp]
      refine ((H2 _ _).trans ?_).symm
      refine (H1 _ _).trans ?_
      fapply ComposableArrows.ext₁
      · rfl
      · rfl
      · simp [ofNerve.inv, ofNerve.hom, ofNerve.map]; rfl
  · fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      simp [ReflQuiv.comp_eq_comp, ReflQuiv.id_eq_id, ofNerve.inv, ofNerve.hom, ofNerve.map]

/-- ER: For use later. -/
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def OneTruncation.ofNerveNatIso : nerveFunctor.{u,u} ⋙ SSet.oneTruncation ≅ ReflQuiv.forget := by
  refine NatIso.ofComponents (fun C => OneTruncation.ofNerve C) ?nat
  · intro C D F
    fapply ReflPrefunctor.ext <;> simp
    · exact fun _ ↦ rfl
    · intro X Y f
      obtain ⟨f, rfl, rfl⟩ := f
      unfold SSet.oneTruncation nerveFunctor mapComposableArrows toReflPrefunctor
      simp [ReflQuiv.comp_eq_comp, ofNerve, ofNerve.hom, ofNerve.map]

def helperAdj : Cat.freeRefl.{u, u} ⊣ nerveFunctor.{u, u} ⋙ SSet.oneTruncation.{u} :=
  (ReflQuiv.adj).ofNatIsoRight (OneTruncation.ofNerveNatIso.symm)

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

theorem opstuff.{w} (V : Cᵒᵖ ⥤ Type w) {X Y Z : C} {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
      α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
    rintro rfl
    change (V.map _ ≫ V.map _) _ = _
    rw [← map_comp]; rfl

def ι0 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 1
def ι1 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 2
def ι2 : [0] ⟶ [2] := SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 1

def φ0 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map ι0.op φ
def φ1 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map ι1.op φ
def φ2 {V : SSet} (φ : V _[2]) : OneTruncation V := V.map ι2.op φ

def δ1 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 1
def δ2 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 2
def δ0 : [1] ⟶ [2] := SimplexCategory.δ (n := 1) 0

def φ02 {V : SSet} (φ : V _[2]) : φ0 φ ⟶ φ2 φ :=
  ⟨V.map δ1.op φ, opstuff V rfl, opstuff V rfl⟩
def φ01 {V : SSet} (φ : V _[2]) : φ0 φ ⟶ φ1 φ :=
  ⟨V.map δ2.op φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
def φ12 {V : SSet} (φ : V _[2]) : φ1 φ ⟶ φ2 φ :=
  ⟨V.map δ0.op φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

inductive HoRel {V : SSet} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]) :
    HoRel _ _
      (Quot.mk _ (.cons .nil (φ02 φ)))
      (Quot.mk _ (.cons (.cons .nil (φ01 φ)) (φ12 φ)))

theorem HoRel.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation V)
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

theorem Cat.id_eq (C : Cat) : 𝟙 C = 𝟭 C := rfl
theorem Cat.comp_eq {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) : F ≫ G = F ⋙ G := rfl

def SSet.hoCat (V : SSet.{u}) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation V))) (HoRel (V := V))

instance (V : SSet.{u}) : Category.{u} (SSet.hoCat V) :=
  inferInstanceAs (Category (Quotient ..))

def SSet.hoFunctorMap {V W : SSet.{u}} (F : V ⟶ W) : SSet.hoCat V ⥤ SSet.hoCat W :=
  Quotient.lift _ (((SSet.oneTruncation ⋙ Cat.freeRefl).map F) ⋙ Quotient.functor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      clear f g hfg
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
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctorMap]
    rw [Quotient.lift_spec, Cat.comp_eq, Cat.comp_eq, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

theorem eq_of_one_to_two (f : [1] ⟶ [2]) :
    f = δ0 ∨ f = δ1 ∨ f = δ2 ∨ ∃ a, f = SimplexCategory.const _ _ a := by
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

def OneTruncation₂ (S : SSet.Truncated 2) := S _[0]₂

abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
    (⟨[n], hn⟩ : Δ 2) ⟶ ⟨[n + 1], hn'⟩ := SimplexCategory.δ i

abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨[n+1], hn⟩ : Δ 2) ⟶ ⟨[n], hn'⟩ := SimplexCategory.σ i

def OneTruncation₂.src {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ (n := 0) 1).op f

def OneTruncation₂.tgt {S : SSet.Truncated 2} (f : S _[1]₂) : OneTruncation₂ S :=
  S.map (δ₂ (n := 0) 0).op f

def OneTruncation₂.Hom {S : SSet.Truncated 2} (X Y : OneTruncation₂ S) :=
  {p : S _[1]₂ // src p = X ∧ tgt p = Y}

instance (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom X Y := OneTruncation₂.Hom X Y
  id X := by
    refine ⟨S.map (σ₂ (n := 0) 0).op X, ?_, ?_⟩ <;>
    · change (S.map _ ≫ S.map _) X = X
      rw [← map_comp]
      rw [(_ : _ ≫ _ = 𝟙 _)]; simp
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
  map_id X := by rfl
  map_comp f g := by rfl

section
variable {V : SSet}

def OneTruncation₂.ofTwoTruncationIso (V : SSet) :
    ReflQuiv.of (OneTruncation₂ ((truncation 2).obj V)) ≅ ReflQuiv.of (OneTruncation V) := .refl _

def OneTruncation₂.nerve₂Iso (C : Cat) :
    ReflQuiv.of (OneTruncation₂ (nerve₂ C)) ≅ ReflQuiv.of (OneTruncation (nerve C)) := .refl _

@[simps!]
def OneTruncation₂.nerve₂NatIso :
    nerveFunctor₂ ⋙ SSet.oneTruncation₂ ≅ nerveFunctor ⋙ SSet.oneTruncation := .refl _

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

def ι0₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1
def ι1₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2
def ι2₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

def φ0₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι0₂.op φ
def φ1₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι1₂.op φ
def φ2₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι2₂.op φ

def δ1₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 1
def δ2₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 2
def δ0₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 0

def φ02₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : φ0₂ φ ⟶ φ2₂ φ :=
  ⟨V.map δ1₂.op φ, opstuff V rfl, opstuff V rfl⟩
def φ01₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : φ0₂ φ ⟶ φ1₂ φ :=
  ⟨V.map δ2₂.op φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
def φ12₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : φ1₂ φ ⟶ φ2₂ φ :=
  ⟨V.map δ0₂.op φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

inductive HoRel₂ {V : SSet.Truncated 2} :
    (X Y : Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) → (f g : X ⟶ Y) → Prop
  | mk (φ : V _[2]₂) :
    HoRel₂ _ _
      (Quot.mk _ (.cons .nil (φ02₂ φ)))
      (Quot.mk _ (.cons (.cons .nil (φ01₂ φ)) (φ12₂ φ)))

theorem HoRel₂.ext_triangle {V} (X X' Y Y' Z Z' : OneTruncation₂ V)
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

def SSet.Truncated.hoFunctor₂Obj (V : SSet.Truncated.{u} 2) : Type u :=
  Quotient (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

instance (V : SSet.Truncated.{u} 2) : Category.{u} (SSet.Truncated.hoFunctor₂Obj V) :=
  inferInstanceAs (Category (Quotient ..))

def SSet.Truncated.hoFunctor₂Obj.quotientFunctor (V : SSet.Truncated.{u} 2) :
    Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)) ⥤ SSet.Truncated.hoFunctor₂Obj V :=
  Quotient.functor (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V))) (HoRel₂ (V := V))

theorem SSet.Truncated.hoFunctor₂Obj.lift_unique' (V : SSet.Truncated.{u} 2)
    {D} [Category D] (F₁ F₂ : SSet.Truncated.hoFunctor₂Obj V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) : F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ V)))
    (HoRel₂ (V := V)) _ _ h

def SSet.Truncated.hoFunctor₂Map {V W : SSet.Truncated.{u} 2} (F : V ⟶ W) : SSet.Truncated.hoFunctor₂Obj V ⥤ SSet.Truncated.hoFunctor₂Obj W :=
  Quotient.lift _
    ((by exact (SSet.oneTruncation₂ ⋙ Cat.freeRefl).map F) ⋙
      SSet.Truncated.hoFunctor₂Obj.quotientFunctor _)
    (fun X Y f g hfg => by
      let .mk φ := hfg
      clear f g hfg
      simp [Quot.liftOn]
      apply Quotient.sound
      convert HoRel₂.mk (F.app (op _) φ) using 0
      apply HoRel₂.ext_triangle
      · exact congrFun (F.naturality ι0₂.op) φ
      · exact congrFun (F.naturality ι1₂.op) φ
      · exact congrFun (F.naturality ι2₂.op) φ
      · exact congrFun (F.naturality δ1₂.op) φ
      · exact congrFun (F.naturality δ2₂.op) φ
      · exact congrFun (F.naturality δ0₂.op) φ)

def SSet.Truncated.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u} where
  obj V := Cat.of (SSet.Truncated.hoFunctor₂Obj V)
  map {S T} F := SSet.Truncated.hoFunctor₂Map F
  map_id S := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, Quotient.lift_spec]
    exact Eq.trans (Functor.id_comp ..) (Functor.comp_id _).symm
  map_comp {S T U} F G := by
    apply Quotient.lift_unique'
    simp [hoFunctor₂Map, SSet.Truncated.hoFunctor₂Obj.quotientFunctor]
    rw [Quotient.lift_spec, Cat.comp_eq, Cat.comp_eq, ← Functor.assoc, Functor.assoc,
      Quotient.lift_spec, Functor.assoc, Quotient.lift_spec]

theorem SSet.Truncated.hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    (SSet.oneTruncation₂ ⋙ Cat.freeRefl).map f ⋙
    hoFunctor₂Obj.quotientFunctor Y =
    SSet.Truncated.hoFunctor₂Obj.quotientFunctor X ⋙ hoFunctor₂Map f := rfl
end

-- /-- ER: We don't actually need this but it would be nice and potentially not too hard. -/
-- def hoFunctor.ofTwoTruncationIso (V : SSet) :
--     SSet.Truncated.hoFunctor₂Obj ((truncation 2).obj V) ≅ SSet.hoCat V := sorry

-- /-- ER: We don't actually need this but it would be nice and potentially not too hard. -/
-- def hoFunctor.ofTwoTruncationNatIso :
--     truncation 2 ⋙ SSet.Truncated.hoFunctor₂ ≅ SSet.hoFunctor' := sorry

@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def nerve₂oneTrunc.natIso : nerveFunctor₂ ⋙ SSet.oneTruncation₂ ≅ ReflQuiv.forget :=
  OneTruncation₂.nerve₂NatIso ≪≫ OneTruncation.ofNerveNatIso

@[simps!]
def nerve₂Adj.counit.component (C : Cat) :
    SSet.Truncated.hoFunctor₂.obj (nerveFunctor₂.obj C) ⥤ C := by
  fapply Quotient.lift
  · exact (whiskerRight (nerve₂oneTrunc.natIso).hom _ ≫ ReflQuiv.adj.counit).app C
  · intro x y f g rel
    cases rel; rename_i φ
    simp [ReflQuiv.adj, Quot.liftOn, Cat.FreeReflObj.quotientFunctor, Quotient.functor,
      Quiv.adj, Quiv.id_eq_id]
    change OneTruncation.ofNerve.map (φ02₂ φ) =
      OneTruncation.ofNerve.map (φ01₂ φ) ≫ OneTruncation.ofNerve.map (φ12₂ φ)
    simp [OneTruncation.ofNerve.map]
    exact φ.map_comp (X := (0 : Fin 3)) (Y := 1) (Z := 2)
      (homOfLE (by decide)) (homOfLE (by decide))

@[simp]
theorem nerve₂Adj.counit.component_eq (C : Cat.{u,u}) :
    SSet.Truncated.hoFunctor₂Obj.quotientFunctor (nerve₂ C) ⋙ nerve₂Adj.counit.component.{u,u} C =
    (whiskerRight (nerve₂oneTrunc.natIso.{u,u}).hom _ ≫
      (ReflQuiv.adj.{u,u}).counit).app C := rfl

/-- ER: Two weird things about this statement:
(i) I had to kill the universes
(ii) I had to convert one composition in cat to functor composition (but not the other)?
-/
theorem nerve₂Adj.counit.naturality' ⦃C D : Cat.{u,u}⦄ (F : C ⟶ D) :
    (nerveFunctor₂ ⋙ SSet.Truncated.hoFunctor₂.{u}).map F ⋙ nerve₂Adj.counit.component.{u,u} D =
      nerve₂Adj.counit.component.{u,u} C ⋙ F := by
  apply SSet.Truncated.hoFunctor₂Obj.lift_unique'
  have := SSet.Truncated.hoFunctor₂_naturality (nerveFunctor₂.map F)
  conv =>
    lhs; rw [← Functor.assoc]; lhs; apply this.symm
  simp only [Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, Functor.comp_map]
  rw [← Functor.assoc _ _ F]
  conv => rhs; lhs; apply (nerve₂Adj.counit.component_eq C)
  conv =>
    rhs
    apply
      ((whiskerRight (nerve₂oneTrunc.natIso.{u,u}).hom Cat.freeRefl ≫
        ReflQuiv.adj.counit).naturality F).symm
  simp [Functor.comp_eq_comp, component]
  rw [Functor.assoc]
  simp [SSet.Truncated.hoFunctor₂Obj.quotientFunctor]
  rw [Quotient.lift_spec]

def nerve₂Adj.counit : nerveFunctor₂ ⋙ SSet.Truncated.hoFunctor₂ ⟶ (𝟭 Cat) where
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
  | 2 => exact fun φ => .mk₂ (F.map (φ01₂ φ)) (F.map (φ12₂ φ))

@[simp] theorem toNerve₂.mk.app_zero {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (x : X _[0]₂) :
    mk.app F [0]₂ x = .mk₀ (F.obj x) := rfl

@[simp] theorem toNerve₂.mk.app_one {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (f : X _[1]₂) :
    mk.app F [1]₂ f = .mk₁ (F.map ⟨f, rfl, rfl⟩) := rfl

@[simp] theorem toNerve₂.mk.app_two {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (φ : X _[2]₂) :
    mk.app F [2]₂ φ = .mk₂ (F.map (φ01₂ φ)) (F.map (φ12₂ φ)) := rfl

def seagull (C : Cat) :
    (nerveFunctor₂.obj C).obj (op [2]₂) ⟶
    (nerveFunctor₂.obj C).obj (op [1]₂) ⨯ (nerveFunctor₂.obj C).obj (op [1]₂) :=
  prod.lift ((nerveFunctor₂.obj C).map (.op δ2₂)) ((nerveFunctor₂.obj C).map (.op δ0₂))

instance (C : Cat) : Mono (seagull C) where
  right_cancellation {X} (f g : X → ComposableArrows C 2) eq := by
    ext x
    simp [seagull] at eq
    have eq1 := congr_fun congr($eq ≫ prod.fst) x; simp at eq1
    have eq2 := congr_fun congr($eq ≫ prod.snd) x; simp at eq2
    generalize f x = fx at *
    generalize g x = gx at *
    clear eq x f g
    fapply ComposableArrows.ext₂
    · exact congrArg (·.obj 0) <| eq1
    · exact congrArg (·.obj 1) <| eq1
    · exact congrArg (·.obj 1) <| eq2
    · have := congr_arg_heq (·.hom) <| eq1
      refine (conj_eqToHom_iff_heq' _ _ _ _).2 this
    · have := congr_arg_heq (·.hom) <| eq2
      refine (conj_eqToHom_iff_heq' _ _ _ _).2 this

@[simps] def toNerve₂.mk {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (φ02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (φ01₂ φ)) (F.map (φ12₂ φ)))
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
          · simp [nerveFunctor₂, truncation, OneTruncation₂.src]
            congr 1
            refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
            rw [← map_comp, ← map_id]; congr 1
            apply Quiver.Hom.unop_inj
            apply SimplexCategory.hom_zero_zero
          · simp [nerveFunctor₂, truncation, OneTruncation₂.tgt]
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
              · simp [nerveFunctor₂, truncation, OneTruncation₂.src]
                refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
                rw [← map_comp, ← map_id]; congr 1
                apply Quiver.Hom.unop_inj
                apply SimplexCategory.hom_zero_zero
              · simp [nerveFunctor₂, truncation, OneTruncation₂.tgt]
                refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
                rw [← map_comp, ← map_id]; congr 1
                apply Quiver.Hom.unop_inj
                apply SimplexCategory.hom_zero_zero
              · rw [← eq_const_to_zero]
            · simp; rfl
        have const01 (α : [0]₂ ⟶ [1]₂) : OK α := by
          ext x
          apply ComposableArrows.ext₀
          unfold nerveFunctor₂ truncation Δ.ι
          simp only [ComposableArrows.obj', Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
            ComposableArrows.mk₀_obj, comp_obj, nerveFunctor_obj, whiskeringLeft_obj_obj,
            Functor.comp_map, op_obj, op_map, Quiver.Hom.unop_op', nerve_map, Quiver.Hom.unop_op,
            SimplexCategory.toCat_map, ComposableArrows.whiskerLeft_obj, Monotone.functor_obj,
            ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
          -- ER: Would help if we know maps out of 0 were constant.
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
          simp [SimplexCategory.rec]
          apply ComposableArrows.ext₀
          unfold nerveFunctor₂ truncation Δ.ι SimplexCategory.Truncated.inclusion fullSubcategoryInclusion inducedFunctor
          simp only [ComposableArrows.obj', Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
            ComposableArrows.mk₀_obj, comp_obj, nerveFunctor_obj, whiskeringLeft_obj_obj,
            Functor.comp_map, op_obj, op_map, Quiver.Hom.unop_op', nerve_map,
            SimplexCategory.len_mk, Quiver.Hom.unop_op, SimplexCategory.toCat_map,
            ComposableArrows.whiskerLeft_obj, Monotone.functor_obj] -- , ComposableArrows.precomp_obj]
          -- ER: Would help if we know maps out of 0 were constant.
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
              simp [SimplexCategory.rec]
              fapply ComposableArrows.ext₁
              · simp [nerveFunctor₂, truncation, OneTruncation₂.src]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp [nerveFunctor₂, truncation, OneTruncation₂.tgt]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp [φ12₂, φ01₂, nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨1, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, φ1₂]
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
              simp [SimplexCategory.rec]
              fapply ComposableArrows.ext₁
              · simp [nerveFunctor₂, truncation, OneTruncation₂.src]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · simp [nerveFunctor₂, truncation, OneTruncation₂.tgt]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp [φ12₂, φ01₂, nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, φ1₂]
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
              simp [SimplexCategory.rec]
              fapply ComposableArrows.ext₁
              · simp [nerveFunctor₂, truncation, OneTruncation₂.src]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp [nerveFunctor₂, truncation, OneTruncation₂.tgt]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp [φ12₂, φ01₂, nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨1, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, φ1₂]
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
          apply (cancel_mono (seagull _)).1
          simp [seagull]
          congr 1 <;> rw [← map_comp, ← op_comp, ← nat1m, ← nat1m, op_comp, map_comp, assoc]
        match n with
        | 0 =>
          match m with
          | 0 =>
            ext x
            simp [SimplexCategory.rec]
            apply ComposableArrows.ext₀
            unfold nerveFunctor₂ truncation
            simp only [ComposableArrows.obj', Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
              ComposableArrows.mk₀_obj, comp_obj, nerveFunctor_obj, whiskeringLeft_obj_obj,
              Functor.comp_map, op_obj, op_map, Quiver.Hom.unop_op', nerve_map, Quiver.Hom.unop_op,
              SimplexCategory.toCat_map, ComposableArrows.whiskerLeft_obj, Monotone.functor_obj]
            -- ER: Would help if we knew α = 𝟙 [0].
            cases SimplexCategory.hom_zero_zero α
            congr 1
            exact congr_fun (X.map_id _) x
          | 1 => apply const01
          | 2 => apply const02
        | 1 => apply nat1m
        | 2 => apply nat2m

/-- ER: We might prefer this version where we are missing the analogue of the hypothesis hyp
conjugated by the isomorphism nerve₂Adj.NatIso.app C -/
@[simps!] def toNerve₂.mk' {X : SSet.Truncated.{0} 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (nerve₂oneTrunc.natIso.app C).hom).map (φ02₂ φ)
      = CategoryStruct.comp (obj := C) ((f ≫ (nerve₂oneTrunc.natIso.app C).hom).map (φ01₂ φ))
        ((f ≫ (nerve₂oneTrunc.natIso.app C).hom).map (φ12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C :=
  toNerve₂.mk (f ≫ (nerve₂oneTrunc.natIso.app C).hom) hyp

theorem oneTruncation₂_toNerve₂Mk' {X : SSet.Truncated.{0} 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (nerve₂oneTrunc.natIso.app C).hom).map (φ02₂ φ)
      = CategoryStruct.comp (obj := C) ((f ≫ (nerve₂oneTrunc.natIso.app C).hom).map (φ01₂ φ))
        ((f ≫ (nerve₂oneTrunc.natIso.app C).hom).map (φ12₂ φ))) :
    oneTruncation₂.map (toNerve₂.mk' f hyp) = f := by
  fapply ReflPrefunctor.ext
  · intro X; exact ComposableArrows.ext₀ rfl
  · intro X Y g
    apply eq_of_heq
    refine (heq_eqRec_iff_heq _ _ _).2 <| (heq_eqRec_iff_heq _ _ _).2 ?_
    simp [oneTruncation₂]
    have {A B A' B' : OneTruncation₂ (nerveFunctor₂.obj C)}
       : A = A' → B = B' → ∀ (x : A ⟶ B) (y : A' ⟶ B'), x.1 = y.1 → HEq x y := by
      rintro rfl rfl ⟨⟩ ⟨⟩ ⟨⟩; rfl
    apply this
    · exact ComposableArrows.ext₀ rfl
    · exact ComposableArrows.ext₀ rfl
    · simp
      fapply ComposableArrows.ext₁
      · simp [ReflQuiv.comp_eq_comp]
        rw [g.2.1]
        exact congr_arg (·.obj 0) (f.map g).2.1.symm
      · simp [ReflQuiv.comp_eq_comp]
        rw [g.2.2]
        exact congr_arg (·.obj 1) (f.map g).2.2.symm
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
def nerve₂Adj.unit.component (X : SSet.Truncated 2) :
    X ⟶ nerveFunctor₂.obj (SSet.Truncated.hoFunctor₂.obj X) := by
  fapply toNerve₂.mk' (C := SSet.Truncated.hoFunctor₂.obj X)
  · exact ((ReflQuiv.adj).unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.Truncated.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor ⋙rq
    (nerve₂oneTrunc.natIso).inv.app (SSet.Truncated.hoFunctor₂.obj X))
  · intro φ
    set g := _ ≫ ((nerve₂oneTrunc.natIso).app _).hom
    have : g = ((ReflQuiv.adj).unit.app (SSet.oneTruncation₂.obj X) ⋙rq
      (SSet.Truncated.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor) := by
      dsimp only [g]
      rw [← ReflQuiv.comp_eq_comp (Y := ReflQuiv.of _), Category.assoc, Iso.app_hom,
        Iso.inv_hom_id_app]
      exact Category.comp_id _
    clear_value g; subst g
    simp [Truncated.hoFunctor₂Obj.quotientFunctor, toReflPrefunctor]
    exact Quotient.sound _ (HoRel₂.mk φ)

theorem nerve₂Adj.unit.component_eq (X : SSet.Truncated 2) :
    SSet.oneTruncation₂.map (nerve₂Adj.unit.component X) =
    (ReflQuiv.adj).unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.Truncated.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor ⋙rq
    (nerve₂oneTrunc.natIso).inv.app (SSet.Truncated.hoFunctor₂.obj X) := by
  apply oneTruncation₂_toNerve₂Mk'


-- /-- ER: This is currently not used.-/
-- theorem nerve₂.two_simplex_property {C : Type*} [Category C] (F G : nerve₂ C _[2]₂)
--     (h₀ : (nerve₂ C).map ι0₂.op F = (nerve₂ C).map ι0₂.op G)
--     (h₁ : (nerve₂ C).map ι0₂.op F = (nerve₂ C).map ι1₂.op G)
--     (h₂ : (nerve₂ C).map ι0₂.op F = (nerve₂ C).map ι2₂.op G)
--     (h₀₁ : (nerve₂ C).map δ2₂.op F = (nerve₂ C).map δ2₂.op G)
--     (h₁₂ : (nerve₂ C).map δ0₂.op F = (nerve₂ C).map δ0₂.op G)
--     (h₀₂ : (nerve₂ C).map δ1₂.op F = (nerve₂ C).map δ1₂.op G)
--   : F = G := sorry

def nerve₂Adj.unit : 𝟭 (SSet.Truncated 2) ⟶ Truncated.hoFunctor₂ ⋙ nerveFunctor₂ where
  app := nerve₂Adj.unit.component
  naturality := by
    intro V W f
    simp only [id_obj, comp_obj, Functor.id_map, Functor.comp_map]
    apply toNerve₂.ext'
      (f ≫ nerve₂Adj.unit.component W)
      (nerve₂Adj.unit.component V ≫ nerveFunctor₂.map (Truncated.hoFunctor₂.map f))
    rw [Functor.map_comp, Functor.map_comp, nerve₂Adj.unit.component_eq,
      nerve₂Adj.unit.component_eq]
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp, ← ReflQuiv.comp_eq_comp, ← assoc]
    have η := (ReflQuiv.adj).unit.naturality (oneTruncation₂.map f)
    simp at η
    conv => lhs; lhs; apply η
    have nat₁ := (nerve₂oneTrunc.natIso).inv.naturality (Truncated.hoFunctor₂.map f)
    repeat rw [← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _)]
    repeat rw [assoc]
    simp at nat₁
    rw [← nat₁]
    rfl

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
ER: Note universe error.
-/
nonrec def nerve₂Adj : SSet.Truncated.hoFunctor₂.{0} ⊣ nerveFunctor₂.{0,0} := by
  refine
    Adjunction.mkOfUnitCounit {
      unit := nerve₂Adj.unit
      counit := nerve₂Adj.counit
      left_triangle := ?_
      right_triangle := ?_
    }
  · ext X
    apply SSet.Truncated.hoFunctor₂Obj.lift_unique'
    simp only [id_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, NatTrans.comp_app,
      whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp, NatTrans.id_app']
    rw [← Functor.comp_eq_comp
      (SSet.Truncated.hoFunctor₂Obj.quotientFunctor X) (𝟙 (SSet.Truncated.hoFunctor₂.obj X))]
    rw [comp_id, Functor.comp_eq_comp, ← Functor.assoc]
    conv =>
      lhs; lhs; apply (SSet.Truncated.hoFunctor₂_naturality (nerve₂Adj.unit.component X)).symm
    simp only [comp_obj, Cat.freeRefl_obj_α, Functor.comp_map]
    rw [nerve₂Adj.unit.component_eq X, Functor.assoc]
    conv =>
      lhs; rhs
      apply (nerve₂Adj.counit.component_eq (SSet.Truncated.hoFunctor₂.obj X))
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc, NatTrans.comp_app, id_obj, whiskerRight_app]
    rw [← Functor.comp_eq_comp, ← assoc, ← Cat.freeRefl.map_comp, ReflQuiv.comp_eq_comp,
      ReflPrefunctor.comp_assoc]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp]
    simp only [ReflQuiv.forget_obj, comp_obj, Iso.inv_hom_id_app]
    rw [ReflQuiv.id_eq_id]
    simp_rw [ReflPrefunctor.comp_id
      (U := ReflQuiv.of _) (V := ReflQuiv.of ↑(SSet.Truncated.hoFunctor₂.{0}.obj X))
      ((SSet.Truncated.hoFunctor₂Obj.quotientFunctor.{0} X).toReflPrefunctor)]
    rw [← ReflQuiv.comp_eq_comp (Z := ReflQuiv.of _)
      ((ReflQuiv.adj.{0,0}).unit.app (SSet.oneTruncation₂.obj X))
      ((SSet.Truncated.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor)]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, map_comp, assoc]
    have nat := ReflQuiv.adj.counit.naturality
      (X := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ X)))
      (Y := SSet.Truncated.hoFunctor₂.obj X) (SSet.Truncated.hoFunctor₂Obj.quotientFunctor X)
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
        ← nerve₂oneTrunc.natIso.inv.naturality]
    conv => lhs; rhs; rw [← assoc] --
    show _ ≫ (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map _) ≫ _ = _
    rw [← ReflQuiv.forget.map_comp]
    show _ ≫ ReflQuiv.forget.map (SSet.Truncated.hoFunctor₂Obj.quotientFunctor (nerve₂ ↑C)
      ⋙ nerve₂Adj.counit.app C) ≫ _ = _
    rw [nerve₂Adj.counit, nerve₂Adj.counit.component_eq]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, NatTrans.comp_app,
      comp_obj, id_obj, whiskerRight_app]
    rw [ReflQuiv.forget.map_comp, ← Functor.comp_map, ← assoc, ← assoc]
    have := ReflQuiv.adj.unit.naturality (nerve₂oneTrunc.natIso.hom.app C)
    simp only [Functor.comp_obj] at this
    conv => lhs; lhs; lhs; apply this.symm
    simp only [Cat.freeRefl_obj_α, id_obj, Functor.id_map]
    slice_lhs 2 3 => rw [ReflQuiv.adj.right_triangle_components C]
    simp

/-- ER: A new strategy to prove that nerveFunctor₂ is fully faithful: just argue directly using toNerve₂.ext to help with fullness. Faithfulness is easy (modulo a universe error I can't figure out).-/
instance nerveFunctor₂.faithful : nerveFunctor₂.{0,0}.Faithful := by
  haveI lem := ReflQuiv.forget.Faithful -- TODO: why is this needed
  exact Functor.Faithful.of_comp_iso (G := oneTruncation₂) (H := ReflQuiv.forget) nerve₂oneTrunc.natIso

/-- ER: Here is my best attempt to prove fullness. map_comp should be extractible by using lem somehow. -/
instance nerveFunctor₂.full : nerveFunctor₂.{0,0}.Full where
  map_surjective := by
    intro X Y F
    let uF := SSet.oneTruncation₂.map F
    let uF' : X ⥤rq Y :=
      nerve₂oneTrunc.natIso.inv.app X ≫ uF ≫ nerve₂oneTrunc.natIso.hom.app Y
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
      -- simp [nerveFunctor₂, truncation, forget₂, HasForget₂.forget₂] at lem0 lem1 lem2
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
    use fF
    refine toNerve₂.ext' (nerveFunctor₂.map fF) F ?_
    · have nat := nerve₂oneTrunc.natIso.{0}.hom.naturality fF
      simp at nat
      rw [eq] at nat
      simp [uF', uF] at nat
      exact
        ((Iso.cancel_iso_hom_right (oneTruncation₂.{0}.map (nerveFunctor₂.{0}.map fF))
          (oneTruncation₂.{0}.map F) (nerve₂oneTrunc.natIso.{0}.app Y)).mp nat)

instance nerveFunctor₂.fullyfaithful : nerveFunctor₂.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor₂

-- -- /-- ER: The underlying refl Quiver of this functor is essentially the unit of ReflQuiver.adj
-- -- composed with the quotient functor. Then we just have to check that this preserves composition.
-- -- Note universe error. -/
-- -- def nerve₂Adj.counit.app.inv.reflPrefunctor (C : Cat.{0}) :
-- --     C ⥤rq SSet.Truncated.hoFunctor₂.obj (nerveFunctor₂.obj C) :=
-- --   ReflQuiv.adj.unit.app (ReflQuiv.of C) ⋙rq
-- --     (Cat.freeRefl.map (nerve₂oneTrunc.natIso.inv.app C)).toReflPrefunctor ⋙rq
-- --     (SSet.Truncated.hoFunctor₂Obj.quotientFunctor (nerveFunctor₂.obj C)).toReflPrefunctor

-- -- /-- ER: Use f and g to build a 2-simplex in the nerve of C and use the corresponding HoRel₂. -/
-- -- def nerve₂Adj.counit.app.inv (C : Cat) :
-- --     C ⥤ SSet.Truncated.hoFunctor₂.obj (nerveFunctor₂.obj C) where
-- --   __ := nerve₂Adj.counit.app.inv.reflPrefunctor C
-- --   map_comp := by
-- --     intros X Y Z f g
-- --     dsimp
-- --     unfold inv.reflPrefunctor
-- --     apply Quotient.sound
-- --     have fg : (nerveFunctor₂.obj C).obj (op [2]₂) := .mk₂ f g
-- --     have : (φ01₂ fg).1 = .mk₁ f := by sorry
-- --     have := HoRel₂.mk fg -- ER: Maybe need lemmas saying what HoRel₂.mk after .mk₂ is between?
-- --     dsimp
-- --     unfold Quiv.adj
-- --     simp only [Cat.free_obj, Quiv.forget_obj, Cat.of_α, Adjunction.mkOfHomEquiv_unit_app,
-- --       Equiv.coe_fn_mk, Prefunctor.comp_obj, Paths.of_obj, Prefunctor.comp_map, Paths.of_map,
-- --       Cat.id_map]
-- --     sorry

-- -- theorem nerve₂Adj.counit.app.inv_reflPrefunctor (C : Cat) :
-- --     ReflQuiv.forget.map (nerve₂Adj.counit.app.inv C) =
-- --       ReflQuiv.adj.unit.app (ReflQuiv.of C) ⋙rq
-- --         (Cat.freeRefl.map (nerve₂oneTrunc.natIso.inv.app C)).toReflPrefunctor ⋙rq
-- --           (SSet.Truncated.hoFunctor₂Obj.quotientFunctor (nerveFunctor₂.obj C)).toReflPrefunctor :=
-- --   rfl

-- -- /-- ER: Killed universes to avoid universe error. -/
-- -- def nerve₂Adj.counit.app.iso (C : Cat.{0,0}) :
-- --     SSet.Truncated.hoFunctor₂.obj (nerveFunctor₂.obj C) ≅ C where
-- --   hom := nerve₂Adj.counit.app _
-- --   inv := nerve₂Adj.counit.app.inv _
-- --   hom_inv_id := sorry
-- --   inv_hom_id := by
-- --     apply ReflQuiv.forget_faithful
-- --     rw [Functor.map_comp]
-- --     rw [nerve₂Adj.counit.app.inv_reflPrefunctor C]
-- --     rw [ReflQuiv.comp_eq_comp, ReflPrefunctor.comp_assoc]
-- --     rw [← ReflQuiv.forget_map]
-- --     show _ ⋙rq _ ⋙rq (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map (app C)) = _
-- --     rw [← Functor.map_comp]
-- --     have eq := nerve₂Adj.counit.component_eq C
-- --     rw [← Functor.comp_eq_comp _ (app C)] at eq
-- --     unfold nerve₂ at eq
-- --     sorry -- ER: Should be able to rewrite at the eq.

-- -- -- ER: Can't infer argument is a morphism in a category.
-- -- -- instance nerve₂Adj.counit.app_isIso (C : Cat) :
-- -- --    IsIso (nerve₂Adj.counit.app C : SSet.Truncated.hoFunctor₂.obj (nerveFunctor₂.obj C) ⟶ C) :=
-- -- --   Iso.isIso_hom (nerve₂Adj.counit.app.iso C)

-- -- -- ER: Should work using the above
-- -- instance nerve₂Adj.counit_isIso : IsIso (nerve₂Adj.counit) := by sorry
-- -- --  apply NatIso.isIso_of_isIso_app

-- -- def nerve₂Adj.counit.iso : nerveFunctor₂ ⋙ SSet.Truncated.hoFunctor₂ ≅ (𝟭 Cat) :=
-- --   asIso nerve₂Adj.counit

-- -- ER: Should work.
-- instance nerveFunctor₂.fullyfaithful : nerveFunctor₂.FullyFaithful := by sorry
-- --  apply Adjunction.fullyFaithfulROfIsIsoCounit nerve₂Adj

/-- ER: Universe errors from here. -/
instance nerve₂Adj.reflective : Reflective nerveFunctor₂.{0,0} :=
  Reflective.mk SSet.Truncated.hoFunctor₂ nerve₂Adj

end

def SSet.hoFunctor : SSet.{u} ⥤ Cat.{u,u} := truncation 2 ⋙ SSet.Truncated.hoFunctor₂

def nerveAdjunction : SSet.hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((coskAdj 2).comp nerve₂Adj) Nerve.cosk2Iso.symm

/-- ER: Repleteness exists for full and faithful functors but not fully faithful functors, which is
why we do this inefficiently. NB the universe error. -/
instance nerveFunctor.faithful : nerveFunctor.{0,0}.Faithful := by
  have := coskeleton.faithful 2
  have : (nerveFunctor₂ ⋙ ran (Δ.ι 2).op).Faithful := Faithful.comp nerveFunctor₂ (ran (Δ.ι 2).op)
  exact (Functor.Faithful.of_iso (F := (nerveFunctor₂ ⋙ ran (Δ.ι 2).op)) (Nerve.cosk2Iso.symm))

instance nerveFunctor.full : nerveFunctor.{0,0}.Full := by
  have := coskeleton.full 2
  have : (nerveFunctor₂ ⋙ ran (Δ.ι 2).op).Full := Full.comp nerveFunctor₂ (ran (Δ.ι 2).op)
  exact (Functor.Full.of_iso (F := (nerveFunctor₂ ⋙ ran (Δ.ι 2).op)) Nerve.cosk2Iso.symm)

instance nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor

instance nerveCounit_isIso : IsIso (nerveAdjunction.counit) :=
  Adjunction.counit_isIso_of_R_fully_faithful _

def nerveCounitNatIso : nerveFunctor ⋙ SSet.hoFunctor ≅ 𝟭 Cat := asIso (nerveAdjunction.counit)

instance : Reflective nerveFunctor where
  L := SSet.hoFunctor
  adj := nerveAdjunction

instance : HasColimits Cat.{0,0} :=
  hasColimits_of_reflective nerveFunctor

end
