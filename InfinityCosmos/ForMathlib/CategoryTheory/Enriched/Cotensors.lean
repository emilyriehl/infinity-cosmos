import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.MonoidalProdCat
import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Opposite
import Mathlib.CategoryTheory.Closed.Enrichment

universe u u₁ v w

open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory SymmetricCategory

open scoped MonoidalClosed

namespace CategoryTheory

namespace Enriched

--TODO: This is intended to be notation, but I'm having trouble with getting that to work
-- so for now, this is a reducible definition
abbrev Ihom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V] (x y : V) : V :=
  (ihom x).obj y

-- The variable V is explicit here since trying to make it implicit throws errors in practice
abbrev Ehom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V]
    (C : Type v) [EnrichedCategory V C] (x y : C) : V :=
  @EnrichedCategory.Hom V _ _ _ _ x y

def Ihom_Ehom_eq (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V]
    (x y : V) : Ihom V x y = Ehom V V x y :=
  rfl

-- New stuff
variable {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V]
variable {C : Type v} [EnrichedCategory V C]

/-- The structure of the cotensoring of `x : C` by `v : V` -/
structure Precotensor (v : V) (x : C) where
  obj : C
  cone : v ⟶ (Ehom V C obj x)

/-- The adjoint tranpose of precotensor_eval -/
def Precotensor.coneNatTrans {v : V} {x : C} (vx : Precotensor v x) (y : C) :
    (Ehom V C y vx.obj) ⟶ (Ihom V v (Ehom V C y x)) :=
  curry ((β_ v (Ehom V C y vx.obj)).hom ≫ Ehom V C y vx.obj ◁ vx.cone ≫ eComp V y vx.obj x)

lemma Precotensor.coneNatTrans_eq {v : V} {x : C} (vx : Precotensor v x) (y : C) :
    uncurry (vx.coneNatTrans y) = (β_ _ _).hom ≫ _ ◁ vx.cone ≫ eComp V y vx.obj x :=
  uncurry_curry _

lemma Precotensor.coneNatTrans_braid_eq {v : V} {x : C} (vx : Precotensor v x) (y : C) :
    (β_ _ _).hom ≫ uncurry (vx.coneNatTrans y) = _ ◁ vx.cone ≫ eComp V y vx.obj x := by
  rw [braiding_swap_eq_inv_braiding]
  apply (Iso.inv_comp_eq (β_ v (Ehom V C y vx.obj))).mpr
  exact vx.coneNatTrans_eq y

/-- A `Cotensor` is a `Precotensor` such that `coneNatTransInv` is an inverse to `coneNatTrans`. -/
structure Cotensor (v : V) (x : C) extends (Precotensor v x) where
  coneNatTransInv (y : C) :
    (Ihom V v (Ehom V C y x)) ⟶ (Ehom V C y obj)
  NatTransInv_NatTrans_eq (y : C) :
    (coneNatTransInv y ≫ Precotensor.coneNatTrans toPrecotensor y = 𝟙 _)
  NatTrans_NatTransInv_eq (y : C) :
    (Precotensor.coneNatTrans toPrecotensor y ≫ coneNatTransInv y = 𝟙 _)

instance {v : V} {x : C} {vx : Cotensor v x} {y : C} : IsIso (vx.coneNatTransInv y) where
  out := ⟨vx.coneNatTrans y, {
    left := vx.NatTransInv_NatTrans_eq y
    right := vx.NatTrans_NatTransInv_eq y
  }⟩

instance {v : V} {x : C} {vx : Cotensor v x} {y : C} : IsIso (vx.coneNatTrans y) where
  out := ⟨vx.coneNatTransInv y, {
    left := vx.NatTrans_NatTransInv_eq y
    right := vx.NatTransInv_NatTrans_eq y
  }⟩

namespace Cotensor

variable (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
variable {C : Type v} [EnrichedCategory V C]

-- Postcomposition and its coherences
def postcompose {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    Ehom V C x y ⟶ Ehom V C vx.obj vy.obj :=
  curry (vx.cone ▷ Ehom V C x y ≫ eComp V vx.obj x y) ≫ vy.coneNatTransInv vx.obj

lemma postcompose_coneNatTrans_eq {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    postcompose V vx vy ≫ vy.coneNatTrans _ = curry (vx.cone ▷ _ ≫ eComp V _ _ _) :=
  ((Category.assoc _ _ _).trans (whisker_eq _ (vy.NatTransInv_NatTrans_eq _))).trans (Category.comp_id _)

lemma uncurry_postcompose_coneNatTrans_eq {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    uncurry (postcompose V vx vy ≫ vy.coneNatTrans _) = vx.cone ▷ _ ≫ eComp V _ _ _ := by
  simp only [postcompose_coneNatTrans_eq, uncurry_curry]

lemma postcompose_selfEval_comp_eq {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    (postcompose V vx vy ▷ _) ≫ (_ ◁ vy.cone) ≫ (eComp V vx.obj vy.obj y)
      = (β_ _ v).hom ≫ (vx.cone ▷ _) ≫ (eComp V vx.obj x y) := by
  rw [← vy.coneNatTrans_braid_eq, braiding_naturality_left_assoc]
  apply (Iso.cancel_iso_hom_left _ _ _).mpr
  apply curry_injective
  rw [curry_natural_left, curry_uncurry]
  exact postcompose_coneNatTrans_eq V vx vy

-- Functorality of post-composition
theorem postcompose_comp_eq {x y z : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y)
    (vz : Cotensor v z) : eComp V x y z ≫ postcompose V vx vz =
      (postcompose V vx vy ⊗ postcompose V vy vz) ≫ eComp V _ _ _ := by
  -- Work the LHS
  apply (cancel_mono (vz.coneNatTrans _)).mp
  apply uncurry_injective
  simp only [Category.assoc]
  rw [uncurry_natural_left]
  rw [uncurry_postcompose_coneNatTrans_eq]
  -- This final exchange solves at the end
  rw [whisker_exchange_assoc]

  -- Work the RHS
  simp only [tensorHom_def, uncurry_natural_left,
    MonoidalCategory.whiskerLeft_comp, vz.coneNatTrans_eq, Category.assoc]
  rw [braiding_naturality_right_assoc]
  rw [braiding_naturality_right_assoc]
  nth_rw 2 [← whisker_exchange_assoc]
  simp only [braiding_tensor_right, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc]
  rw [← associator_inv_naturality_right_assoc]
  rw [e_assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  -- This invokes commutativity of post with selfEval
  simp only [Category.assoc, postcompose_selfEval_comp_eq,
    MonoidalCategory.whiskerLeft_comp]
  -- Now we can use symmetry
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [symmetry, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- Moving a morphism through a bunch of associators and braids >_>
  rw [associator_inv_naturality_middle_assoc]
  -- Annoying
  rw [← comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  rw [comp_whiskerRight_assoc]
  --
  rw [← associator_naturality_middle_assoc]
  --
  rw [(e_assoc' V vx.obj vy.obj y z)]
  --
  nth_rw 3 [← comp_whiskerRight_assoc]
  nth_rw 2 [← comp_whiskerRight_assoc]
  simp only [postcompose_selfEval_comp_eq, comp_whiskerRight, Category.assoc]
  -- Take out the symmetry
  rw [← comp_whiskerRight_assoc]
  simp only [symmetry, id_whiskerRight, Category.id_comp]
  -- All posts are gone from the equation
  rw [← associator_inv_naturality_left_assoc]
  rw [e_assoc]

theorem postcompose_id_eq {x : C} {v : V} (vx : Cotensor v x) :
    eId V x ≫ postcompose V vx vx = eId V vx.obj := by
  -- These lines are copied from the last proof - consider isolating!
  apply (cancel_mono (vx.coneNatTrans _)).mp
  apply uncurry_injective
  simp only [Category.assoc]
  rw [uncurry_natural_left]
  rw [uncurry_postcompose_coneNatTrans_eq]
  -- This is copied from the RHS part of the previous proof
  simp only [uncurry_natural_left, MonoidalCategory.whiskerLeft_comp,
    vx.coneNatTrans_eq, Category.assoc]
  simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
    Category.assoc]
  -- Braiding has been replaced by unitors
  apply (Iso.inv_comp_eq _).mp
  -- Moving selfEval up on the LHS
  rw [whisker_exchange_assoc]
  rw [← rightUnitor_inv_naturality_assoc]
  -- Moving up selfEval on the RHS
  rw [← whisker_exchange_assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  -- Final step
  rw [e_id_comp, e_comp_id]

-- Precomposition and its coherences
def IhomPrecompose {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    Ihom V w v ⟶ Ehom V C vx.obj wx.obj :=
  (ihom w).map vx.cone ≫ wx.coneNatTransInv vx.obj

def EhomPrecompose {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    Ehom V V w v ⟶ Ehom V C vx.obj wx.obj := IhomPrecompose V _ _

lemma IhomPrecompose_coneNatTrans_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    IhomPrecompose V wx vx ≫ wx.coneNatTrans _ = (ihom w).map vx.cone :=
  ((Category.assoc _ _ _).trans (whisker_eq _ (wx.NatTransInv_NatTrans_eq _))).trans (Category.comp_id _)

lemma EhomPrecompose_coneNatTrans_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    EhomPrecompose V wx vx ≫ wx.coneNatTrans _ = (ihom w).map vx.cone :=
  IhomPrecompose_coneNatTrans_eq V wx vx

lemma IhomPrecompose_selfEval_comp_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    (IhomPrecompose V wx vx) ▷ _ ≫ (_ ◁ wx.cone) ≫ eComp V _ _ _
      = (β_ _ _).hom ≫ (ihom.ev w).app v ≫ vx.cone := by
  rw [← ihom.ev_naturality]
  rw [← braiding_naturality_left_assoc]
  unfold IhomPrecompose
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  apply whisker_eq
  apply (cancel_epi ((wx.coneNatTrans _) ▷ w)).mp
  rw [← comp_whiskerRight_assoc]
  simp only [wx.NatTrans_NatTransInv_eq, id_whiskerRight, Category.id_comp]
  rw [braiding_naturality_left_assoc]
  rw [← uncurry_eq]
  exact (Precotensor.coneNatTrans_braid_eq wx.toPrecotensor vx.obj).symm

lemma EhomPrecompose_selfEval_comp_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    (EhomPrecompose V wx vx) ▷ _ ≫ (_ ◁ wx.cone) ≫ eComp V _ _ _
      = (β_ _ _).hom ≫ (ihom.ev w).app v ≫ vx.cone :=
  IhomPrecompose_selfEval_comp_eq V wx vx

-- Functoriality of precomposition
theorem precompose_comp_eq {x : C} {u v w : V} (ux : Cotensor u x) (vx : Cotensor v x)
    (wx : Cotensor w x) : eComp V u v w ≫ EhomPrecompose V ux wx =
      (EhomPrecompose V ux vx ⊗ EhomPrecompose V vx wx) ≫ (β_ _ _).hom ≫ eComp V _ _ _ := by
  apply (cancel_mono (ux.coneNatTrans _)).mp
  simp only [Category.assoc]
  rw [EhomPrecompose_coneNatTrans_eq]
  apply uncurry_injective
  simp only [uncurry_natural_left]
  rw [ux.coneNatTrans_eq]
  -- Moving comp to after selfEval
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  -- Moving Precompose down to comp
  simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
  -- Annoying move again
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_left]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [braiding_naturality_right_assoc]
  simp only [braiding_tensor_right, whisker_assoc, tensor_whiskerLeft,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [e_assoc]
  nth_rw 4 [← MonoidalCategory.whiskerLeft_comp_assoc]
  nth_rw 3 [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [EhomPrecompose_selfEval_comp_eq, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  -- Another very bad
  have t := symmetry u (Ehom V V u v)
  have t' : (β_ (Ehom V V u v) u).hom = (β_ ((ihom u).obj v) u).hom := rfl
  rw [t'] at t
  rw [t]
  --
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- The lemma again
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_right]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [associator_inv_naturality_middle_assoc]
  -- and again...
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  --
  rw [associator_naturality_left_assoc]
  rw [← whisker_exchange_assoc]
  simp only [Functor.id_obj]
  rw [EhomPrecompose_selfEval_comp_eq]

  -- There are no more pre's in the equation
  --Very bad
  have : β_ ((ihom v).obj w) v = β_ (Ehom V V v w) v := rfl
  rw [this]
  --
  rw [braiding_naturality_right_assoc]
  simp only [braiding_tensor_right, Functor.id_obj, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc]
  simp only [symmetry, id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [symmetry, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- Forced to unfold uncurry
  rw [uncurry_eq]
  rw [(ihom.ev_naturality u)]
  -- lemma about the enriched structure on V
  have : eComp V u v w = comp u v w := rfl
  rw [this]
  have : u ◁ comp u v w ≫ (ihom.ev u).app w
    = uncurry (comp u v w) := rfl
  have := eq_whisker this wx.cone
  simp only [Category.assoc] at this
  rw [this]
  rw [comp_eq]
  rw [uncurry_curry]
  rw [MonoidalClosed.compTranspose_eq]
  simp only [Category.assoc]
  exact rfl

theorem precompose_id_eq {x : C} {v : V} (vx : Cotensor v x) :
    eId V v ≫ EhomPrecompose V vx vx = eId V vx.obj := by
  -- Copied from the last proof
  apply (cancel_mono (vx.coneNatTrans _)).mp
  simp only [Category.assoc]
  rw [EhomPrecompose_coneNatTrans_eq]
  apply uncurry_injective
  simp only [uncurry_natural_left]
  rw [vx.coneNatTrans_eq]
  simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
    Category.assoc]
  rw [uncurry_eq]

  rw [← whisker_exchange_assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  simp only [e_id_comp, Category.comp_id]
  rw [ihom.ev_naturality]

  -- Annoying
  have : eId V v = MonoidalClosed.id v := rfl
  rw [this]
  -- Even more annoying - this came up in the enriched thing!
  rw [MonoidalClosed.id_eq]
  have := uncurry_eq (curry (ρ_ v).hom)
  have := eq_whisker this.symm vx.cone
  simp only [Category.assoc] at this
  rw [this]
  --
  rw [uncurry_curry]

/-- Naturality of postcomposition with precoposition -/
theorem post_pre_eq_pre_post {x y : C} {w v : V} (wx : Cotensor w x) (wy : Cotensor w y)
    (vx : Cotensor v x) (vy : Cotensor v y) :
  (EhomPrecompose V wx vx ⊗ postcompose V wx wy) ≫ eComp V vx.obj wx.obj wy.obj =
    (EhomPrecompose V wy vy ⊗ postcompose V vx vy) ≫ (β_ _ _).hom
      ≫ eComp V vx.obj vy.obj wy.obj := by
  -- Turn EHom to IHom, uncurry, and simplify the result
  apply (cancel_mono (wy.coneNatTrans _)).mp
  apply uncurry_injective
  simp only [uncurry_natural_left]
  unfold Precotensor.coneNatTrans
  rw [uncurry_curry]
  rw [MonoidalCategory.tensorHom_def]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

  -- Remove post w from the LHS
  rw [braiding_naturality_right_assoc]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  -- simp only [MonoidalCategory.comp_whiskerRight]
  -- simp only [Category.assoc]

  rw [← (e_assoc' V vx.obj wx.obj wy.obj y)]

  rw [associator_naturality_right_assoc]
  rw [associator_naturality_middle_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [postcompose_selfEval_comp_eq]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

  -- Remove pre x from the LHS
  rw [braiding_tensor_right_assoc]
  rw [Iso.inv_hom_id_assoc]
  -- This uses the symmetry!
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [symmetry, whiskerLeft_id_assoc]
  --
  rw [associator_inv_naturality_middle_assoc]
  -- Candidate for moving to its own lemma
  rw [← comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  rw [comp_whiskerRight_assoc]
  --
  rw [← (e_assoc V vx.obj wx.obj x y)]
  rw [← whisker_assoc_assoc]
  repeat rw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [EhomPrecompose_selfEval_comp_eq]

  -- Remove pre y from the RHS
  rw [MonoidalCategory.tensorHom_def']
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  rw [← e_assoc']
  rw [associator_naturality_right_assoc]
  rw [braiding_tensor_right_assoc]
  rw [Iso.inv_hom_id_assoc]
  -- Candidate for moving to its own lemma
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_left]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rw [associator_naturality_right_assoc]
  -- Candidate for moving to its own lemma
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_right]
  --
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [EhomPrecompose_selfEval_comp_eq]
  -- Very bad

  have t := symmetry_assoc w (Ehom V V w v) ((ihom.ev w).app v ≫ vy.cone)
  have u : (β_ (Ehom V V w v) w).hom = (β_ ((ihom w).obj v) w).hom := rfl
  rw [u] at t
  rw [t]
  --

  -- Remove post x from the RHS
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  -- Candidate again...
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_right]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [associator_inv_naturality_middle_assoc]
  -- Candidate on the right
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  nth_rw 2 [MonoidalCategory.comp_whiskerRight_assoc]
  --
  rw [associator_naturality_left_assoc]
  rw [← whisker_exchange_assoc]
  simp only [Functor.id_obj]
  rw [postcompose_selfEval_comp_eq]

  -- There are no more post's or pre's in the equation
  simp only [comp_whiskerRight, Category.assoc, braiding_naturality_right_assoc,
    braiding_tensor_right, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc]
  -- Very bad again...
  have t' := symmetry w (Ehom V V w v)
  have u' : (β_ (Ehom V V w v) w).hom = (β_ ((ihom w).obj v) w).hom := rfl
  rw [u'] at t'
  rw [t']
  --
  nth_rw 3 [← comp_whiskerRight_assoc]
  simp only [symmetry, id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [symmetry, MonoidalCategory.whiskerLeft_id, Category.id_comp]

class CotensoredCategory (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
    [SymmetricCategory V] (C : Type v) [EnrichedCategory V C] where
  cotensor : (v : V) → (x : C) → Cotensor v x

open CotensoredCategory eOpposite

def cotensor_bifunc [CotensoredCategory V C] : EnrichedFunctor V ((eOpposite V V) ⊗[V] C) C :=
  enrichedTensor.eBifuncConstr V (eOpposite V V) C
    (fun v x ↦ (cotensor (unop v) x).obj)
    (fun v w x ↦ EhomPrecompose V (cotensor (unop w) x) (cotensor (unop v) x))
    (fun v x y ↦ postcompose V (cotensor (unop v) x) (cotensor (unop v) y))
    (fun v x ↦ precompose_id_eq V (cotensor (unop v) x))
    (fun v x ↦ postcompose_id_eq V (cotensor (unop v) x))
    (fun u v w x ↦ by
      have : eComp V u v w = (β_ _ _).hom ≫ eComp V (unop w) (unop v) (unop u) := rfl
      simp only [this, Category.assoc]
      rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
      apply (Iso.inv_comp_eq _).mpr
      rw [← BraidedCategory.braiding_naturality_assoc]
      exact precompose_comp_eq V
        (cotensor (unop w) x) (cotensor (unop v) x) (cotensor (unop u) x))
    (fun v x y z ↦ postcompose_comp_eq V
      (cotensor (unop v) x)
      (cotensor (unop v) y)
      (cotensor (unop v) z))
    (fun w v x y ↦ post_pre_eq_pre_post V
      (cotensor (unop v) x)
      (cotensor (unop v) y)
      (cotensor (unop w) x)
      (cotensor (unop w) y))

end Cotensor

end Enriched

end CategoryTheory
