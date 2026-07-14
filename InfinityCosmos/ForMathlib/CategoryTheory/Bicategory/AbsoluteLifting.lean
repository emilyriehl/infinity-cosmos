import Mathlib.CategoryTheory.Bicategory.Kan.IsKan
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Absolute left liftings in bicategories
-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

namespace LeftLift

@[simp]
theorem homMk_right {a b c : B} {f : b ⟶ a} {g : c ⟶ a} {s t : LeftLift f g}
    (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit) :
    (homMk η w).right = η :=
  rfl

section Paste

variable {a b c d : B} {f : b ⟶ a} {g : d ⟶ a} {h : c ⟶ b}

/-- Given a left lift `t` of `g` along `f` and a left lift `s` of `t` along `h`, then we obtain a
left lift `t.paste s` of `g` along `f ≫ h`.
```
            b                 c                     c
          ◹ |               ◹ |                   ◹ |
 t.lift /   |      s.lift /   |      paste.lift /   |
      /  ⇑  | f         /  ⇑  | h             /  ⇑  | f ≫ h
    /       ▽         /       ▽             /       ▽
  d - - - ▷ a       d - - - ▷ b           d - - - ▷ a
       g              t.lift                   g
```
-/
def paste (t : LeftLift f g) (s : LeftLift h t.lift) : LeftLift (h ≫ f) g :=
  .mk s.lift (t.unit ≫ s.unit ▷ f ≫ (α_ s.lift h f).hom)

variable {t : LeftLift f g} {s : LeftLift h t.lift}

@[simp]
theorem paste_lift : (t.paste s).lift = s.lift :=
  rfl

@[simp]
theorem paste_unit :
    (t.paste s).unit = t.unit ≫ s.unit ▷ f ≫ (α_ s.lift h f).hom :=
  rfl

/-- Whiskering a pasted left lift is isomorphic to pasting the whiskered left lifts. -/
def pasteWhiskerIso (t : LeftLift f g) (s : LeftLift h t.lift) {x : B} (k : x ⟶ d) :
    (t.paste s).whisker k ≅ (t.whisker k).paste (s.whisker k) :=
  { hom := LeftLift.homMk (𝟙 _) <| by
      dsimp only [paste_lift, paste_unit, whisker_lift, whisker_unit]
      bicategory
    inv := LeftLift.homMk (𝟙 _) <| by
      dsimp only [paste_lift, paste_unit, whisker_lift, whisker_unit]
      bicategory
    hom_inv_id := by ext; simp
    inv_hom_id := by ext; simp }

/-- Given a left Kan lift `t` of `g` along `f`, a left lift `u` of `g` along `h ≫ f` induces,
via the universal property of `t`, a left lift of `t.lift` along `h`.
```
            b                 c                       c
          ◹ |               ◹ |                     ◹ |
 t.lift /   |      u.lift /   |                   /   |
      /  ⇑  | f         /  ⇑  | f ≫ h           /  ⇑  | h
    /       ▽         /       ▽               /       ▽
  d - - - ▷ a       d - - - ▷ a             d - - - ▷ b
       g                 g                    t.lift
```
-/
def IsKan.ofIsKanTop (Ht : IsKan t) (u : LeftLift (h ≫ f) g) : LeftLift h t.lift :=
  .mk u.lift (Ht.desc (.mk (u.lift ≫ h) (u.unit ≫ (α_ u.lift h f).inv)))

@[simp]
theorem IsKan.ofIsKanTop_lift (Ht : IsKan t) (u : LeftLift (h ≫ f) g) :
    (Ht.ofIsKanTop u).lift = u.lift :=
  rfl

theorem IsKan.ofIsKanTop_fac (Ht : IsKan t) (u : LeftLift (h ≫ f) g) :
    t.unit ≫ (Ht.ofIsKanTop u).unit ▷ f = u.unit ≫ (α_ u.lift h f).inv := by
  simpa [IsKan.ofIsKanTop] using Ht.fac (.mk (u.lift ≫ h) (u.unit ≫ (α_ u.lift h f).inv))

set_option backward.isDefEq.respectTransparency false in
/-- Pasting of left lifts preserves being Kan. -/
def IsKan.paste (Ht : IsKan t) (Hs : IsKan s) : IsKan (t.paste s) :=
  IsKan.mk
    (fun u ↦
      LeftLift.homMk (Hs.desc (Ht.ofIsKanTop u)) <| by
        rw [paste_unit, ← cancel_mono (α_ u.lift h f).inv, ← Ht.ofIsKanTop_fac,
          ← Hs.fac (Ht.ofIsKanTop u)]
        bicategory)
    (fun u τ ↦ by
      ext
      apply Hs.hom_ext
      apply Ht.hom_ext
      rw [homMk_right, Hs.fac, Ht.ofIsKanTop_fac, ← LeftLift.w τ, paste_unit]
      bicategory)

set_option backward.isDefEq.respectTransparency false in
/-- Given a left lift `t` of `g` along `f` and a left lift `s` of `t` along `h`, if `t` and
`t.paste s` are Kan, then so is `s`. -/
def IsKan.ofPaste (Ht : IsKan t) (Hp : IsKan (t.paste s)) : IsKan s :=
  IsKan.mk
    (fun v ↦
      LeftLift.homMk (Hp.desc (t.paste v)) <| Ht.hom_ext <| by
        rw [← cancel_mono (α_ v.lift h f).hom, Category.assoc, Category.assoc, ← paste_unit,
          ← Hp.fac (t.paste v), paste_unit]
        bicategory)
    (fun v τ ↦ by
      ext
      apply Hp.hom_ext
      rw [homMk_right, Hp.fac, paste_unit, paste_unit, ← LeftLift.w τ]
      bicategory)

/-- Let `t` be a left Kan lift of `g` along `f` and `s` a left lift of `t` along `h`. Then `s` is
Kan if and only if `t.paste s` is Kan. -/
def isKanEquivIsKanPaste (Ht : IsKan t) : (IsKan s) ≃ (IsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton Ht.paste Ht.ofPaste

/-- Pasting of left lifts preserves being absolute Kan. -/
noncomputable def IsAbsKan.paste (H : IsAbsKan t) (Hs : IsAbsKan s) :
    IsAbsKan (t.paste s) :=
  fun k ↦ ((H k).paste (Hs k)).ofIsoKan (pasteWhiskerIso t s k).symm

/-- Given a left lift `t` of `g` along `f` and a left lift `s` of `t` along `h`, if `t` and
`t.paste s` are absolute Kan, then so is `s`. -/
noncomputable def IsAbsKan.ofPaste (H : IsAbsKan t) (Hp : IsAbsKan (t.paste s)) :
    IsAbsKan s :=
  fun k ↦ (H k).ofPaste ((Hp k).ofIsoKan (pasteWhiskerIso t s k))

/-- Let `t` be an abslute left Kan lift of `g` along `f` and `s` a left lift of `t` along `h`. Then
`s` is absolute Kan if and only if `t.paste s` is absolute Kan. -/
noncomputable def isAbsKanEquivIsAbsKanPaste (H : IsAbsKan t) :
    (IsAbsKan s) ≃ (IsAbsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton H.paste H.ofPaste

end Paste

section OfIso

variable {a b c : B} {f f' : b ⟶ a} {g g' : c ⟶ a}

/-- The equivalence between the categories of left lifts induced by isomorphisms of the two
boundary 1-cells: postcomposing along `ef : f ≅ f'` and reindexing along `eg : g ≅ g'`. -/
def isoEquiv (ef : f ≅ f') (eg : g ≅ g') : LeftLift f g ≌ LeftLift f' g' :=
  (StructuredArrow.mapNatIso ((postcomposing c b a).mapIso ef)).trans (StructuredArrow.mapIso eg)

/-- Transport a left lift along isomorphisms of its two boundary 1-cells, as the image of `t`
under `LeftLift.isoEquiv`. Such isomorphisms arise, for instance, from the unitors and associators
of a bicategory. -/
def ofIso (ef : f ≅ f') (eg : g ≅ g') (t : LeftLift f g) : LeftLift f' g' :=
  (isoEquiv ef eg).functor.obj t

@[simp]
theorem ofIso_lift (ef : f ≅ f') (eg : g ≅ g') (t : LeftLift f g) :
    (t.ofIso ef eg).lift = t.lift :=
  rfl

@[simp]
theorem ofIso_unit (ef : f ≅ f') (eg : g ≅ g') (t : LeftLift f g) :
    (t.ofIso ef eg).unit = eg.inv ≫ t.unit ≫ t.lift ◁ ef.hom :=
  rfl

/-- `LeftLift.ofIso` preserves Kan lifts: being a left Kan lift is invariant under transporting
the boundary 1-cells along isomorphisms. -/
noncomputable def IsKan.ofIso {t : LeftLift f g} (H : t.IsKan) (ef : f ≅ f') (eg : g ≅ g') :
    (t.ofIso ef eg).IsKan :=
  Limits.IsInitial.isInitialObj (isoEquiv ef eg).functor t H

/-- Whiskering commutes with `LeftLift.ofIso` (in the source variable). -/
def whiskerOfIso (ef : f ≅ f') (eg : g ≅ g') (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).ofIso ef (whiskerLeftIso h eg) ≅ (t.ofIso ef eg).whisker h :=
  StructuredArrow.isoMk (Iso.refl _) <| by
    simp [postcomp]

/-- `LeftLift.ofIso` preserves absolute left Kan lifts. -/
noncomputable def IsAbsKan.ofIso {t : LeftLift f g} (H : t.IsAbsKan) (ef : f ≅ f') (eg : g ≅ g') :
    (t.ofIso ef eg).IsAbsKan :=
  fun h ↦ ((H h).ofIso ef (whiskerLeftIso h eg)).ofIsoKan (whiskerOfIso ef eg t h)

end OfIso

section Whisker

variable {a b c x : B} {f : b ⟶ a} {g : c ⟶ a}

/-- Whiskering twice agrees, up to the associator, with whiskering by the composite. -/
def whiskerWhiskerIso (t : LeftLift f g) {y : B} (h : x ⟶ c) (k : y ⟶ x) :
    (t.whisker (k ≫ h)).ofIso (Iso.refl _) (α_ k h g) ≅ (t.whisker h).whisker k where
  hom := LeftLift.homMk (α_ k h t.lift).hom <| by
    dsimp only [ofIso_unit, ofIso_lift, whisker_unit, whisker_lift]
    bicategory
  inv := LeftLift.homMk (α_ k h t.lift).inv <| by
    dsimp only [ofIso_unit, ofIso_lift, whisker_unit, whisker_lift]
    bicategory
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-- Whiskering an absolute left Kan lift yields an absolute left Kan lift. -/
noncomputable def IsAbsKan.whisker {t : LeftLift f g} (H : t.IsAbsKan) (h : x ⟶ c) :
    (t.whisker h).IsAbsKan := by
  intro y k
  exact ((H (k ≫ h)).ofIso (Iso.refl _) (α_ k h g)).ofIsoKan (whiskerWhiskerIso t h k)

end Whisker

end LeftLift

end Bicategory

end CategoryTheory
