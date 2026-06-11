import Mathlib.CategoryTheory.Bicategory.Kan.IsKan
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Absolute left liftings in bicategories

Mathlib defines `LeftLift f g`, its whiskering `LeftLift.whisker`, and the notion of an
absolute left Kan lift `LeftLift.IsAbsKan`. We add the pasting of left lifts here, together
with the composition and cancelation lemma for absolute left lifting diagrams
([RV] Lemma 2.4.1).

## References
* [E. Riehl and D. Verity, *Elements of ∞-Category Theory*][RiehlVerity2022], Lemma 2.4.1
-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

namespace LeftLift

section Paste

variable {a b c d : B} {f : b ⟶ a} {g : c ⟶ b} {h : d ⟶ a}

/-- Given a left lift `t = (r, ρ)` of `h` along `f` and a left lift `s = (s, σ)` of `r`
along `g`, the pasted diagram `(s, σf · ρ)` is a left lift of `h` along `g ≫ f`:
```
            c
          ◹ | g
      s /   ▽
      / ⇗σ  b
    /  r ◹  | f    ⇗ρ
  d - - - ▷ a
       h
```
-/
def paste (t : LeftLift f h) (s : LeftLift g t.lift) : LeftLift (g ≫ f) h :=
  .mk s.lift (t.unit ≫ s.unit ▷ f ≫ (α_ s.lift g f).hom)

variable {t : LeftLift f h} {s : LeftLift g t.lift}

@[simp]
theorem paste_lift : (t.paste s).lift = s.lift :=
  rfl

@[simp]
theorem paste_unit :
    (t.paste s).unit = t.unit ≫ s.unit ▷ f ≫ (α_ s.lift g f).hom :=
  rfl

/-- Whiskering a pasted left lift is isomorphic to pasting the whiskered left lifts. -/
def pasteWhiskerIso (t : LeftLift f h) (s : LeftLift g t.lift) {x : B} (k : x ⟶ d) :
    (t.whisker k).paste (s.whisker k) ≅ (t.paste s).whisker k :=
  { hom := LeftLift.homMk (𝟙 _) <| by
      dsimp only [paste_lift, paste_unit, whisker_lift, whisker_unit]
      bicategory
    inv := LeftLift.homMk (𝟙 _) <| by
      dsimp only [paste_lift, paste_unit, whisker_lift, whisker_unit]
      bicategory
    hom_inv_id := by ext; simp
    inv_hom_id := by ext; simp }

/-- Given a left Kan lift `t` of `h` along `f`, a left lift of `h` along `g ≫ f` induces,
via the universal property of `t`, a left lift of `t.lift` along `g`. -/
def IsKan.unpaste (Ht : IsKan t) (u : LeftLift (g ≫ f) h) : LeftLift g t.lift :=
  .mk u.lift (Ht.desc (.mk (u.lift ≫ g) (u.unit ≫ (α_ u.lift g f).inv)))

@[simp]
theorem IsKan.unpaste_lift (Ht : IsKan t) (u : LeftLift (g ≫ f) h) :
    (Ht.unpaste u).lift = u.lift :=
  rfl

theorem IsKan.unpaste_fac (Ht : IsKan t) (u : LeftLift (g ≫ f) h) :
    t.unit ≫ (Ht.unpaste u).unit ▷ f = u.unit ≫ (α_ u.lift g f).inv := by
  simpa [unpaste] using Ht.fac (.mk (u.lift ≫ g) (u.unit ≫ (α_ u.lift g f).inv))

/-- Composition of left Kan lifts: if `t` is a left Kan lift of `h` along `f` and `s` is
a left Kan lift of `t.lift` along `g`, then the pasted diagram `t.paste s` is a left Kan
lift of `h` along `g ≫ f`. -/
def IsKan.paste (Ht : IsKan t) (Hs : IsKan s) : IsKan (t.paste s) :=
  IsKan.mk
    (fun u ↦
      LeftLift.homMk (Hs.desc (Ht.unpaste u)) <| by
        rw [← cancel_mono (α_ u.lift g f).inv, ← Ht.unpaste_fac u, ← Hs.fac (Ht.unpaste u)]
        dsimp only [paste_lift, paste_unit]
        bicategory)
    (fun u τ ↦ by
      ext
      apply Hs.hom_ext
      refine Eq.trans ?_ (Hs.fac (Ht.unpaste u)).symm
      apply Ht.hom_ext
      refine Eq.trans ?_ (Ht.unpaste_fac u).symm
      have hw := LeftLift.w τ
      dsimp only [paste_lift, paste_unit] at hw
      rw [← hw]
      bicategory)

/-- Cancelation of left Kan lifts: if `t` is a left Kan lift of `h` along `f` and the
pasted diagram `t.paste s` is a left Kan lift of `h` along `g ≫ f`, then `s` is a left
Kan lift of `t.lift` along `g`. -/
def IsKan.ofPaste (Ht : IsKan t) (Hp : IsKan (t.paste s)) : IsKan s :=
  IsKan.mk
    (fun v ↦
      LeftLift.homMk (Hp.desc (t.paste v)) <| Ht.hom_ext <| by
        rw [← cancel_mono (α_ v.lift g f).hom]
        have hf := Hp.fac (t.paste v)
        dsimp only [paste_lift, paste_unit] at hf
        simp only [Category.assoc] at hf ⊢
        rw [← hf]
        bicategory)
    (fun v τ ↦ by
      ext
      apply Hp.hom_ext
      refine Eq.trans ?_ (Hp.fac (t.paste v)).symm
      have hw := LeftLift.w τ
      dsimp only [paste_lift, paste_unit]
      rw [← hw]
      bicategory)

/-- Composition of absolute left lifting diagrams ([RV] Lemma 2.4.1, "if" direction):
if `(r, ρ)` is an absolute left lifting of `h` through `f` and `(s, σ)` is an absolute
left lifting of `r` through `g`, then the pasted diagram `(s, σf · ρ)` is an absolute
left lifting of `h` through `g ≫ f`. -/
noncomputable def IsAbsKan.paste (H : IsAbsKan t) (Hs : IsAbsKan s) :
    IsAbsKan (t.paste s) :=
  fun k ↦ ((H k).paste (Hs k)).ofIsoKan (pasteWhiskerIso t s k)

/-- Cancelation of absolute left lifting diagrams ([RV] Lemma 2.4.1, "only if" direction):
if `(r, ρ)` is an absolute left lifting of `h` through `f` and the pasted diagram
`(s, σf · ρ)` is an absolute left lifting of `h` through `g ≫ f`, then `(s, σ)` is an
absolute left lifting of `r` through `g`. -/
noncomputable def IsAbsKan.ofPaste (H : IsAbsKan t) (Hp : IsAbsKan (t.paste s)) :
    IsAbsKan s :=
  fun k ↦ (H k).ofPaste ((Hp k).ofIsoKan (pasteWhiskerIso t s k).symm)

/-- Composition and cancelation of absolute left lifting diagrams ([RV] Lemma 2.4.1),
stated as a bi-implication. -/
theorem isAbsKan_paste_iff (H : IsAbsKan t) :
    Nonempty (IsAbsKan s) ↔ Nonempty (IsAbsKan (t.paste s)) :=
  ⟨fun ⟨Hs⟩ ↦ ⟨H.paste Hs⟩, fun ⟨Hp⟩ ↦ ⟨H.ofPaste Hp⟩⟩

end Paste

end LeftLift

end Bicategory

end CategoryTheory
