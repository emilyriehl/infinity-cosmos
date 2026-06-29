/-
Copyright (c) 2025 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CosliceProjLeftFibration

section
/-!
# The `i = last` special-outer-horn filler via the coslice / Leibniz-join route

Builds `specialOuterHornFiller_last_leibniz`, the Leibniz-join form of the special-outer-horn
filler for the missing last edge. A special outer horn is
encoded as coslice data, transported along the left fibration `thetaMap` (conservative, from
`CosliceProjLeftFibration`), the missing edge is lifted, and the filler is decoded back. The horn
lifting problem is moved via `outerHornLast_iso_leibnizJoin` to the Leibniz join and decomposed
through the pushout `sqLeibCo`, the face algebra handled by `inl_ι`/`inr_ι`, `isPushout.w` and the
`joinInl'` naturalities. The encode/decode lemmas are proved for general `A, B` and specialized to
`A = Δ[0]`, `B = Δ[1]` downstream. Feeds the `i = last` filler `SpecialOuterHorn.fill_last`.
-/

open CategoryTheory MonoidalCategory Simplicial Opposite Limits MorphismProperty
namespace SSet
universe u
noncomputable section

variable {S T C D : SSet.{u}} (jST : S ⟶ T) {A B : SSet.{u}} (g : A ⟶ B)
  (top : (sqLeibCo jST g).pt ⟶ C)

/-- The front simplex `f := joinInl' T A ≫ (inl ≫ top)`. -/
def encF : T ⟶ C := joinInl' T A ≫ (sqLeibCo jST g).inl ≫ top

/-- The front-vertex block `α = inl ≫ top` is a simplex of `C_{f/}` (the vertex `x̄`). -/
def encXbar : CoOverPt (encF jST g top) A :=
  ⟨(sqLeibCo jST g).inl ≫ top, rfl⟩

/-- The back-boundary block `β = inr ≫ top` restricts to `f0 = jST ≫ f` — i.e. it is a
simplex of `C_{f0/}`.  Pure pushout algebra: `joinInl'` naturalities + `isPushout.w`. -/
theorem encBeta_restricts :
    joinInl' S B ≫ ((sqLeibCo jST g).inr ≫ top) = jST ≫ encF jST g top := by
  have hr := joinInl'_naturality_right g S
  have hl := joinInl'_naturality_left jST A
  have hw := (sqLeibCo jST g).isPushout.w
  -- term-level `Category.assoc`/`congrArg` (the matcher chokes on `rw [Category.assoc]` here)
  have sub : joinInl' S B ≫ (sqLeibCo jST g).inr
      = jST ≫ joinInl' T A ≫ (sqLeibCo jST g).inl :=
    calc joinInl' S B ≫ (sqLeibCo jST g).inr
        = (joinInl' S A ≫ (joinFunctor.obj S).map g) ≫ (sqLeibCo jST g).inr :=
          congrArg (· ≫ (sqLeibCo jST g).inr) hr.symm
      _ = joinInl' S A ≫ ((joinFunctor.obj S).map g ≫ (sqLeibCo jST g).inr) :=
          Category.assoc _ _ _
      _ = joinInl' S A ≫ ((joinFunctor.map jST).app A ≫ (sqLeibCo jST g).inl) :=
          congrArg (joinInl' S A ≫ ·) hw.symm
      _ = (joinInl' S A ≫ (joinFunctor.map jST).app A) ≫ (sqLeibCo jST g).inl :=
          (Category.assoc _ _ _).symm
      _ = (jST ≫ joinInl' T A) ≫ (sqLeibCo jST g).inl :=
          congrArg (· ≫ (sqLeibCo jST g).inl) hl
      _ = jST ≫ joinInl' T A ≫ (sqLeibCo jST g).inl := Category.assoc _ _ _
  calc joinInl' S B ≫ ((sqLeibCo jST g).inr ≫ top)
      = (joinInl' S B ≫ (sqLeibCo jST g).inr) ≫ top := (Category.assoc _ _ _).symm
    _ = (jST ≫ joinInl' T A ≫ (sqLeibCo jST g).inl) ≫ top := congrArg (· ≫ top) sub
    _ = jST ≫ (joinInl' T A ≫ (sqLeibCo jST g).inl) ≫ top := Category.assoc _ _ _
    _ = jST ≫ joinInl' T A ≫ (sqLeibCo jST g).inl ≫ top :=
        congrArg (jST ≫ ·) (Category.assoc _ _ _)
    _ = jST ≫ encF jST g top := rfl

/-- The base `bot` restricts to `f ≫ q` on the front (so it is a simplex of `D_{(qf)/}`).
Uses `inl_ι` + the lifting square `hsq`. -/
theorem encBot_restricts (q : C ⟶ D) (bot : (joinFunctor.obj T).obj B ⟶ D)
    (hsq : (sqLeibCo jST g).ι ≫ bot = top ≫ q) :
    joinInl' T B ≫ bot = encF jST g top ≫ q := by
  have hr := joinInl'_naturality_right g T
  have hαq : (joinFunctor.obj T).map g ≫ bot = (sqLeibCo jST g).inl ≫ (top ≫ q) :=
    calc (joinFunctor.obj T).map g ≫ bot
        = ((sqLeibCo jST g).inl ≫ (sqLeibCo jST g).ι) ≫ bot :=
          congrArg (· ≫ bot) (sqLeibCo jST g).inl_ι.symm
      _ = (sqLeibCo jST g).inl ≫ ((sqLeibCo jST g).ι ≫ bot) := Category.assoc _ _ _
      _ = (sqLeibCo jST g).inl ≫ (top ≫ q) := congrArg ((sqLeibCo jST g).inl ≫ ·) hsq
  calc joinInl' T B ≫ bot
      = (joinInl' T A ≫ (joinFunctor.obj T).map g) ≫ bot := congrArg (· ≫ bot) hr.symm
    _ = joinInl' T A ≫ ((joinFunctor.obj T).map g ≫ bot) := Category.assoc _ _ _
    _ = joinInl' T A ≫ ((sqLeibCo jST g).inl ≫ (top ≫ q)) :=
        congrArg (joinInl' T A ≫ ·) hαq
    _ = joinInl' T A ≫ ((sqLeibCo jST g).inl ≫ top) ≫ q :=
        congrArg (joinInl' T A ≫ ·) (Category.assoc _ _ _).symm
    _ = (joinInl' T A ≫ (sqLeibCo jST g).inl ≫ top) ≫ q := (Category.assoc _ _ _).symm
    _ = encF jST g top ≫ q := rfl

/-- The pullback agreement: `β ≫ q = (joinFunctor.map jST).app B ≫ bot` (the `C_{f0/}` and
`D_{(qf)/}` edges agree in `D_{(qf0)/}`).  Uses `inr_ι` + the square `hsq`. -/
theorem encAgree (q : C ⟶ D) (bot : (joinFunctor.obj T).obj B ⟶ D)
    (hsq : (sqLeibCo jST g).ι ≫ bot = top ≫ q) :
    ((sqLeibCo jST g).inr ≫ top) ≫ q = (joinFunctor.map jST).app B ≫ bot :=
  calc ((sqLeibCo jST g).inr ≫ top) ≫ q
      = (sqLeibCo jST g).inr ≫ (top ≫ q) := Category.assoc _ _ _
    _ = (sqLeibCo jST g).inr ≫ ((sqLeibCo jST g).ι ≫ bot) :=
        congrArg ((sqLeibCo jST g).inr ≫ ·) hsq.symm
    _ = ((sqLeibCo jST g).inr ≫ (sqLeibCo jST g).ι) ≫ bot := (Category.assoc _ _ _).symm
    _ = (joinFunctor.map jST).app B ≫ bot := congrArg (· ≫ bot) (sqLeibCo jST g).inr_ι

end
end SSet
end

section
/-!
# Edge-in-E construction for the special-outer-horn filler
-/

open CategoryTheory MonoidalCategory Simplicial Opposite Limits MorphismProperty
namespace SSet
universe u
noncomputable section

variable {S T C D : SSet.{u}} (jST : S ⟶ T) {A B : SSet.{u}} (g : A ⟶ B)
  (top : (sqLeibCo jST g).pt ⟶ C) (q : C ⟶ D)
  (bot : (joinFunctor.obj T).obj B ⟶ D)
  (hsq : (sqLeibCo jST g).ι ≫ bot = top ≫ q)

/-- The `C_{f0/}` edge as a map `B ⟶ cosliceUnder (jST ≫ f)`. -/
def encBmap : B ⟶ cosliceUnder (jST ≫ encF jST g top) :=
  cosliceHomEquiv (jST ≫ encF jST g top) B
    ⟨(sqLeibCo jST g).inr ≫ top, encBeta_restricts jST g top⟩

/-- The `D_{(qf)/}` edge as a map `B ⟶ cosliceUnder (f ≫ q)`. -/
def encDmap : B ⟶ cosliceUnder (encF jST g top ≫ q) :=
  cosliceHomEquiv (encF jST g top ≫ q) B ⟨bot, encBot_restricts jST g top q bot hsq⟩

/-- THE PULLBACK AGREEMENT: the `C_{f0/}` and `D_{(qf)/}` edges agree in `D_{(qf0)/}`,
so they assemble into an edge of `E`.  Reduces to `encAgree` via the `cosliceHomEquiv`
naturalities + injectivity. -/
theorem encEdge_agree :
    encBmap jST g top ≫ cosliceMapTarget (p := jST ≫ encF jST g top) q
      = encDmap jST g top q bot hsq ≫
          cosliceMapBase jST (rfl : jST ≫ (encF jST g top ≫ q) = jST ≫ (encF jST g top ≫ q)) := by
  rw [encBmap, encDmap,
    ← cosliceHomEquiv_naturality_target q B
      ⟨(sqLeibCo jST g).inr ≫ top, encBeta_restricts jST g top⟩,
    ← cosliceHomEquiv_naturality_base jST B
      ⟨bot, encBot_restricts jST g top q bot hsq⟩]
  exact congrArg (cosliceHomEquiv _ B) (Subtype.ext (encAgree jST g top q bot hsq))

/-- The edge `v̄` as a map `B ⟶ E` (the fiber product). -/
def encVmap : B ⟶ fiberProductE jST (encF jST g top) q :=
  pullback.lift (encBmap jST g top) (encDmap jST g top q bot hsq)
    (encEdge_agree jST g top q bot hsq)

@[simp] theorem encVmap_fst :
    encVmap jST g top q bot hsq ≫ pullback.fst _ _ = encBmap jST g top :=
  pullback.lift_fst _ _ _

@[simp] theorem encVmap_snd :
    encVmap jST g top q bot hsq ≫ pullback.snd _ _ = encDmap jST g top q bot hsq :=
  pullback.lift_snd _ _ _

/-- The vertex `x̄` as a map `A ⟶ C_{f/}`. -/
def encXmap : A ⟶ cosliceUnder (encF jST g top) :=
  cosliceHomEquiv (encF jST g top) A (encXbar jST g top)

/-- THE FACE-MATCH (`ρ(x̄) = tgt(v̄)`): precomposing `v̄` with the edge cell `g` (= the `d₀`
face) equals `x̄ ≫ ρ`.  Via `pullback.hom_ext` + the `cosliceHomEquiv` naturalities +
`isPushout.w` (fst) / `inl_ι` (snd).  General in `g`. -/
theorem encVface :
    g ≫ encVmap jST g top q bot hsq
      = encXmap jST g top ≫ cosliceProj jST (encF jST g top) q := by
  apply pullback.hom_ext
  · -- fst leg: reduces to `isPushout.w` precomposed with `top`
    simp only [Category.assoc, encVmap_fst, cosliceProj_fst]
    rw [encBmap, encXmap, cosliceHomEquiv_naturality_left,
      ← cosliceHomEquiv_naturality_base]
    refine congrArg (cosliceHomEquiv _ A) (Subtype.ext ?_)
    show (joinFunctor.obj S).map g ≫ ((sqLeibCo jST g).inr ≫ top)
      = (joinFunctor.map jST).app A ≫ ((sqLeibCo jST g).inl ≫ top)
    calc (joinFunctor.obj S).map g ≫ ((sqLeibCo jST g).inr ≫ top)
        = ((joinFunctor.obj S).map g ≫ (sqLeibCo jST g).inr) ≫ top := (Category.assoc _ _ _).symm
      _ = ((joinFunctor.map jST).app A ≫ (sqLeibCo jST g).inl) ≫ top :=
          congrArg (· ≫ top) (sqLeibCo jST g).isPushout.w.symm
      _ = (joinFunctor.map jST).app A ≫ ((sqLeibCo jST g).inl ≫ top) := Category.assoc _ _ _
  · -- snd leg: reduces to `inl_ι` + the square `hsq`
    simp only [Category.assoc, encVmap_snd, cosliceProj_snd]
    rw [encDmap, encXmap, cosliceHomEquiv_naturality_left,
      ← cosliceHomEquiv_naturality_target]
    refine congrArg (cosliceHomEquiv _ A) (Subtype.ext ?_)
    show (joinFunctor.obj T).map g ≫ bot = ((sqLeibCo jST g).inl ≫ top) ≫ q
    calc (joinFunctor.obj T).map g ≫ bot
        = ((sqLeibCo jST g).inl ≫ (sqLeibCo jST g).ι) ≫ bot :=
          congrArg (· ≫ bot) (sqLeibCo jST g).inl_ι.symm
      _ = (sqLeibCo jST g).inl ≫ ((sqLeibCo jST g).ι ≫ bot) := Category.assoc _ _ _
      _ = (sqLeibCo jST g).inl ≫ (top ≫ q) := congrArg ((sqLeibCo jST g).inl ≫ ·) hsq
      _ = ((sqLeibCo jST g).inl ≫ top) ≫ q := (Category.assoc _ _ _).symm

end
end SSet
end

section
/-!
# v̄ as an Edge in E + the lift (steps 2-3), specialized to g = δ0, A=Δ[0], B=Δ[1].
-/

open CategoryTheory Simplicial Opposite Limits MorphismProperty
namespace SSet
universe u
noncomputable section

variable {S T C D : SSet.{u}} (jST : S ⟶ T)
  (top : (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).pt ⟶ C) (q : C ⟶ D)
  (bot : (joinFunctor.obj T).obj (Δ[1] : SSet.{u}) ⟶ D)
  (hsq : (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).ι ≫ bot = top ≫ q)

/-- `σ`: the `1`-simplex of `E` underlying `v̄`. -/
def encSigma : (fiberProductE jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q) _⦋1⦌ :=
  yonedaEquiv (encVmap jST (stdSimplex.δ (0 : Fin 2)) top q bot hsq)

/-- `x̄`: the target vertex (`0`-simplex of `C_{f/}`). -/
def encXbar0 : (cosliceUnder (encF jST (stdSimplex.δ (0 : Fin 2)) top)) _⦋0⦌ :=
  yonedaEquiv (encXmap jST (stdSimplex.δ (0 : Fin 2)) top)

/-- THE FACE-VERTEX EQUALITY: `E.δ 0 σ = ρ.app x̄` (the `tgt(v̄) = ρ(x̄)` at the simplex
level).  From `encVface` (with `g = δ0` the `d₀` face) + yoneda naturality. -/
theorem encFace :
    (fiberProductE jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q).δ 0
        (encSigma jST top q bot hsq)
      = (cosliceProj jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q).app _
          (encXbar0 jST top) := by
  apply yonedaEquiv.symm.injective
  rw [encSigma, encXbar0]
  dsimp only [SimplicialObject.δ]
  rw [← yonedaEquiv_symm_naturality (SimplexCategory.δ (0 : Fin 2))
      (yonedaEquiv (encVmap jST (stdSimplex.δ (0 : Fin 2)) top q bot hsq)),
    Equiv.symm_apply_apply, ← yonedaEquiv_comp, Equiv.symm_apply_apply]
  exact encVface jST (stdSimplex.δ (0 : Fin 2)) top q bot hsq

/-- The edge `v̄ : Edge s₀ (ρ.app x̄)` in `E`. -/
def encEdge :
    Edge ((fiberProductE jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q).δ 1
        (encSigma jST top q bot hsq))
      ((cosliceProj jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q).app _
        (encXbar0 jST top)) :=
  (Edge.mk' (encSigma jST top q bot hsq)).ofEq rfl (encFace jST top q bot hsq)

/-- STEPS 2-3: from `θ(v̄)` invertible (the conservativity input), lift `v̄` through
`ρ = cosliceProj` (a left fibration, `C_{f/}` a quasicategory) to an edge `ẽ` of `C_{f/}`
with `ρ(ẽ) = v̄` strictly and target `x̄`. -/
theorem encLift [Mono jST] [Quasicategory C] [Quasicategory D] [InnerFibration q]
    (hinv : Nonempty
      ((encEdge jST top q bot hsq).map
        (thetaMap jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q)).IsIso) :
    ∃ (x₀ : (cosliceUnder (encF jST (stdSimplex.δ (0 : Fin 2)) top)) _⦋0⦌)
      (ee : Edge x₀ (encXbar0 jST top)),
      (ee.map (cosliceProj jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q)).edge
        = encSigma jST top q bot hsq := by
  have hv : Nonempty (encEdge jST top q bot hsq).IsIso :=
    thetaMap_conservative jST _ q (encEdge jST top q bot hsq) hinv
  obtain ⟨x₀, ee, _, hρ, _⟩ :=
    leftFibration_isofibration_target (encEdge jST top q bot hsq) hv
  exact ⟨x₀, ee, hρ⟩

end
end SSet
end

section
/-!
# Step 4: decode + restrict-to-horn → specialOuterHornFiller (leibnizJoin form)
-/

open CategoryTheory MonoidalCategory Simplicial Opposite Limits MorphismProperty
namespace SSet
universe u
noncomputable section

/-- yoneda–cosliceHomEquiv compatibility at representables: the round trip is the identity. -/
theorem yonedaEquiv_cosliceHomEquiv {K C : SSet.{u}} (p : K ⟶ C) (m : SimplexCategory)
    (X : CoOverPt p (stdSimplex.obj m)) :
    yonedaEquiv (cosliceHomEquiv p (stdSimplex.obj m) X) = X := by
  apply Subtype.ext
  rw [show yonedaEquiv (cosliceHomEquiv p (stdSimplex.obj m) X)
        = (cosliceHomEquiv p (stdSimplex.obj m) X).app (op m)
            (yonedaEquiv (𝟙 (stdSimplex.obj m))) from rfl,
    cosliceHomEquiv_app_coe]
  rw [show uliftYonedaEquiv.symm (yonedaEquiv (𝟙 (stdSimplex.obj m)))
        = 𝟙 (stdSimplex.obj m) from Equiv.symm_apply_apply _ _]
  exact (congrArg (· ≫ X.1) ((joinFunctor.obj K).map_id _)).trans (Category.id_comp _)

/-- At representables, `cosliceHomEquiv` is `yonedaEquiv.symm`. -/
theorem cosliceHomEquiv_eq_yonedaEquiv_symm {K C : SSet.{u}} (p : K ⟶ C) (m : SimplexCategory)
    (X : CoOverPt p (stdSimplex.obj m)) :
    cosliceHomEquiv p (stdSimplex.obj m) X = yonedaEquiv.symm X := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_cosliceHomEquiv, Equiv.apply_symm_apply]

variable {S T C D : SSet.{u}} (jST : S ⟶ T)
  (top : (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).pt ⟶ C) (q : C ⟶ D)
  (bot : (joinFunctor.obj T).obj (Δ[1] : SSet.{u}) ⟶ D)
  (hsq : (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).ι ≫ bot = top ≫ q)

/-- **`specialOuterHornFiller_last_leibniz`** (leibnizJoin form): the lifting problem
`(sqLeibCo jST δ0).ι` over `q`, with the encoded edge `θ(v̄)` invertible, has a filler. -/
theorem specialOuterHornFiller_last_leibniz [Mono jST] [Quasicategory C] [Quasicategory D]
    [InnerFibration q]
    (hinv : Nonempty ((encEdge jST top q bot hsq).map
      (thetaMap jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q)).IsIso) :
    ∃ filler : (joinFunctor.obj T).obj (Δ[1] : SSet.{u}) ⟶ C,
      (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).ι ≫ filler = top ∧ filler ≫ q = bot := by
  obtain ⟨x₀, ee, hρ⟩ := encLift jST top q bot hsq hinv
  set f := encF jST (stdSimplex.δ (0 : Fin 2)) top with hf
  -- the map form of ρ(ẽ) = v̄
  have hmap : yonedaEquiv.symm ee.edge ≫ cosliceProj jST f q
      = encVmap jST (stdSimplex.δ (0 : Fin 2)) top q bot hsq := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hρ
  have hemap : yonedaEquiv.symm ee.edge = cosliceHomEquiv f Δ[1] ee.edge :=
    (cosliceHomEquiv_eq_yonedaEquiv_symm f ⦋1⦌ ee.edge).symm
  -- (a) fst leg ⟹ `coOverPtMapBase jST ẽ = βCo`
  have hfst : cosliceHomEquiv f Δ[1] ee.edge ≫
      cosliceMapBase jST (rfl : jST ≫ f = jST ≫ f)
      = encBmap jST (stdSimplex.δ (0 : Fin 2)) top := by
    rw [← hemap]
    have := congrArg (· ≫ pullback.fst _ _) hmap
    simpa only [Category.assoc, cosliceProj_fst, encVmap_fst] using this
  have hβ : ((joinFunctor.map jST).app Δ[1] ≫ ee.edge.1)
      = (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).inr ≫ top := by
    have key : coOverPtMapBase jST Δ[1] ee.edge
        = (⟨(sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).inr ≫ top,
            encBeta_restricts jST (stdSimplex.δ (0 : Fin 2)) top⟩ : CoOverPt (jST ≫ f) Δ[1]) := by
      apply (cosliceHomEquiv (jST ≫ f) Δ[1]).injective
      rw [cosliceHomEquiv_naturality_base]; exact hfst
    exact congrArg Subtype.val key
  -- (b) snd leg ⟹ `coOverPtPost q ẽ = botCo`
  have hsnd : cosliceHomEquiv f Δ[1] ee.edge ≫ cosliceMapTarget q =
      encDmap jST (stdSimplex.δ (0 : Fin 2)) top q bot hsq := by
    rw [← hemap]
    have := congrArg (· ≫ pullback.snd _ _) hmap
    simpa only [Category.assoc, cosliceProj_snd, encVmap_snd] using this
  have hbot : ee.edge.1 ≫ q = bot := by
    have key : coOverPtPost q ee.edge
        = (⟨bot, encBot_restricts jST (stdSimplex.δ (0 : Fin 2)) top q bot hsq⟩ :
            CoOverPt (f ≫ q) Δ[1]) := by
      apply (cosliceHomEquiv (f ≫ q) Δ[1]).injective
      rw [cosliceHomEquiv_naturality_target]; exact hsnd
    exact congrArg Subtype.val key
  -- (c) target vertex ⟹ inl-block matches
  have htgt : ((joinFunctor.obj T).map (stdSimplex.δ (0 : Fin 2)) ≫ ee.edge.1)
      = (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).inl ≫ top := by
    have h := congrArg Subtype.val ee.tgt_eq
    have hx : (encXbar0 jST top).1
        = (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).inl ≫ top := by
      show (yonedaEquiv (cosliceHomEquiv f (stdSimplex.obj ⦋0⦌)
          (encXbar jST (stdSimplex.δ (0 : Fin 2)) top))).1 = _
      rw [yonedaEquiv_cosliceHomEquiv]
      rfl
    exact h.trans hx
  refine ⟨ee.edge.1, ?_, ?_⟩
  · apply (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).isPushout.hom_ext
    · rw [← Category.assoc, (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).inl_ι]; exact htgt
    · rw [← Category.assoc, (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).inr_ι]; exact hβ
  · exact hbot

end
end SSet
end

section
/-!
# `cosliceAbsProj_eq`: absProj of a coslice edge = its free-factor restriction.
Connects `θ(v̄)` to the literal final edge `u`.
-/

open CategoryTheory MonoidalCategory Simplicial Opposite Limits MorphismProperty
namespace SSet
universe u
noncomputable section

/-- `botIso ∘ cosliceHomEquiv = joinInr ⊥` restriction. -/
theorem cosliceHomEquiv_botIso {C : SSet.{u}} (h : (⊥_ SSet.{u}) ⟶ C) {Y : SSet.{u}}
    (Z : CoOverPt h Y) :
    cosliceHomEquiv h Y Z ≫ (cosliceUnderBotIso h).hom = joinInr (⊥_ SSet.{u}) Y ≫ Z.1 := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  show (cosliceUnderBotIso h).hom.app n ((cosliceHomEquiv h Y Z).app n z)
    = (joinInr (⊥_ SSet.{u}) Y ≫ Z.1).app n z
  simp only [cosliceUnderBotIso, NatIso.ofComponents_hom_app, Equiv.toIso_hom_hom_apply]
  show yonedaEquiv (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop)
      ≫ ((cosliceHomEquiv h Y Z).app n z).1) = _
  rw [cosliceHomEquiv_app_coe]
  have hmapeq : joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop)
        ≫ ((joinFunctor.obj (⊥_ SSet.{u})).map (uliftYonedaEquiv.symm z) ≫ Z.1)
      = uliftYonedaEquiv.symm z ≫ (joinInr (⊥_ SSet.{u}) Y ≫ Z.1) :=
    calc joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop)
          ≫ ((joinFunctor.obj (⊥_ SSet.{u})).map (uliftYonedaEquiv.symm z) ≫ Z.1)
        = (joinInr (⊥_ SSet.{u}) (stdSimplex.obj n.unop)
            ≫ (joinFunctor.obj (⊥_ SSet.{u})).map (uliftYonedaEquiv.symm z)) ≫ Z.1 :=
          (Category.assoc _ _ _).symm
      _ = (uliftYonedaEquiv.symm z ≫ joinInr (⊥_ SSet.{u}) Y) ≫ Z.1 :=
          congrArg (· ≫ Z.1) (joinInr_naturality_right (⊥_ SSet.{u}) (uliftYonedaEquiv.symm z))
      _ = uliftYonedaEquiv.symm z ≫ (joinInr (⊥_ SSet.{u}) Y ≫ Z.1) := Category.assoc _ _ _
  refine (congrArg yonedaEquiv hmapeq).trans ?_
  refine (yonedaEquiv_comp (uliftYonedaEquiv.symm z)
    (joinInr (⊥_ SSet.{u}) Y ≫ Z.1)).trans ?_
  congr 1
  exact Equiv.apply_symm_apply yonedaEquiv z

/-- **`cosliceAbsProj_eq`**: the absolute coslice projection of `cosliceHomEquiv p Y X` is the
free-factor restriction `joinInr K Y ≫ X.1`. -/
theorem cosliceAbsProj_eq {K C : SSet.{u}} (p : K ⟶ C) {Y : SSet.{u}} (X : CoOverPt p Y) :
    cosliceHomEquiv p Y X ≫ cosliceAbsProj p = joinInr K Y ≫ X.1 := by
  show cosliceHomEquiv p Y X ≫
      (cosliceMapBase (initial.to K) (rfl : initial.to K ≫ p = initial.to K ≫ p)
        ≫ (cosliceUnderBotIso (initial.to K ≫ p)).hom) = _
  rw [← Category.assoc, ← cosliceHomEquiv_naturality_base, cosliceHomEquiv_botIso]
  show joinInr (⊥_ SSet.{u}) Y ≫ ((joinFunctor.map (initial.to K)).app Y ≫ X.1)
    = joinInr K Y ≫ X.1
  calc joinInr (⊥_ SSet.{u}) Y ≫ ((joinFunctor.map (initial.to K)).app Y ≫ X.1)
      = (joinInr (⊥_ SSet.{u}) Y ≫ (joinFunctor.map (initial.to K)).app Y) ≫ X.1 :=
        (Category.assoc _ _ _).symm
    _ = joinInr K Y ≫ X.1 :=
        congrArg (· ≫ X.1) (joinInr_naturality_left (initial.to K) Y)

/-- **`θ(v̄) = u`**: the image of the encoded edge under `θ` is the distinguished final edge
`u = joinInr S Δ[1] ≫ β`.  This discharges the `θ(v̄)`-invertible hypothesis from the final
edge being invertible. -/
theorem encThetaEdge_eq {S T C D : SSet.{u}} (jST : S ⟶ T)
    (top : (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).pt ⟶ C) (q : C ⟶ D)
    (bot : (joinFunctor.obj T).obj (Δ[1] : SSet.{u}) ⟶ D)
    (hsq : (sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).ι ≫ bot = top ≫ q) :
    ((encEdge jST top q bot hsq).map
        (thetaMap jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q)).edge
      = yonedaEquiv (joinInr S (Δ[1] : SSet.{u})
          ≫ ((sqLeibCo jST (stdSimplex.δ (0 : Fin 2))).inr ≫ top)) := by
  rw [Edge.map_edge]
  show (thetaMap jST (encF jST (stdSimplex.δ (0 : Fin 2)) top) q).app _
      (encSigma jST top q bot hsq) = _
  rw [encSigma, ← yonedaEquiv_comp]
  congr 1
  show encVmap jST (stdSimplex.δ (0 : Fin 2)) top q bot hsq ≫
      (pullback.fst _ _ ≫ cosliceAbsProj (jST ≫ encF jST (stdSimplex.δ (0 : Fin 2)) top)) = _
  rw [← Category.assoc, encVmap_fst, encBmap, cosliceAbsProj_eq]

end
end SSet
end
