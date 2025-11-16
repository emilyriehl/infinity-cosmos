import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory Simplicial SimplexCategory Limits

namespace SimplexCategory

def δ_zero_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 0 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) j := by
  ext x
  fin_cases x
  aesop

def δ_one_mkOfLe {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SimplexCategory.δ 1 ≫ mkOfLe i j h =
  (SimplexCategory.mk 0).const (SimplexCategory.mk n) i := by
  ext x
  fin_cases x
  aesop

/- `IsDegeneracy f` if `f` is a composite of (a potentially empty list of) degeneracy maps -/
inductive IsDegeneracy : ∀ {x y : SimplexCategory}, (x ⟶ y) → Prop
  | id (x : SimplexCategory) : IsDegeneracy (𝟙 x)
  | sigma {n : ℕ} (i : Fin (n + 1)) : IsDegeneracy (σ i)
  | comp {x y z : SimplexCategory} {f : x ⟶ y} {g : y ⟶ z} (_ : IsDegeneracy f) (_ : IsDegeneracy g) : IsDegeneracy (f ≫ g)

theorem epi_IsDegeneracy {m n : ℕ} (f : mk m ⟶ mk n) [Epi f] : IsDegeneracy f := by
  have hrec : ∀ (k : ℕ) {m n : ℕ} (h : m - n = k) (f : mk m ⟶ mk n) [Epi f], IsDegeneracy f := by
    intro k
    induction k with
    | zero      => intro m _ h f _ 
                   have := le_antisymm (Nat.le_of_sub_eq_zero h) (le_of_epi f)
                   subst this
                   simpa only [eq_id_of_epi f] using IsDegeneracy.id (mk m)
    | succ i ih => intro m n h f _
                   have nmlen : ¬m ≤ n := fun nlem => Nat.succ_ne_zero i (by simp only [Nat.sub_eq_zero_of_le nlem, Nat.right_eq_add, Nat.add_eq_zero, one_ne_zero, and_false] at h)
                   have ninj : ¬Function.Injective f := by intro finj
                                                           have := Fintype.card_le_of_injective f finj
                                                           simp only [len_mk, Fintype.card_fin, add_le_add_iff_right] at this
                                                           contradiction
                   cases m with
                   | zero   => exact (nmlen (Nat.zero_le n)).elim
                   | succ m => obtain ⟨j, g, fsjg⟩ := eq_σ_comp_of_not_injective f ninj
                               have := epi_of_epi_fac fsjg.symm
                               have : m - n = i := by rwa [Nat.sub_add_comm (by simp only [not_le, Nat.lt_succ] at nmlen; exact nmlen), Nat.succ_inj] at h
                               have := IsDegeneracy.comp (IsDegeneracy.sigma j) (ih this g)
                               rwa [fsjg]
  exact hrec (m - n) rfl f

/- `IsFace f` if `f` is a composite of (a potentially empty list of) face maps -/
inductive IsFace : ∀ {x y : SimplexCategory}, (x ⟶ y) → Prop
  | id (x : SimplexCategory) : IsFace (𝟙 x)
  | delta {n : ℕ} (i : Fin (n + 2)) : IsFace (δ i)
  | comp {x y z : SimplexCategory} {f : x ⟶ y} {g : y ⟶ z} (_ : IsFace f) (_ : IsFace g) : IsFace (f ≫ g)

theorem mono_IsFace {m n : ℕ} (f : mk m ⟶ mk n) [Mono f] : IsFace f := by
    have hrec : ∀ (k : ℕ) {m n : ℕ} (h : n - m = k) (f : mk m ⟶ mk n) [Mono f], IsFace f := by
      intro k
      induction k with
      | zero      => intro _ n h f _
                     have := le_antisymm (Nat.le_of_sub_eq_zero h) (le_of_mono f)
                     subst this
                     simpa only [eq_id_of_mono f] using IsFace.id (mk n)
      | succ i ih => intro m n h f _
                     have nnlem : ¬n ≤ m := fun nlem => Nat.succ_ne_zero i (by simp only [Nat.sub_eq_zero_of_le nlem, Nat.right_eq_add, Nat.add_eq_zero, one_ne_zero, and_false] at h)
                     have nsur : ¬Function.Surjective f := by intro fsur
                                                              have := Fintype.card_le_of_surjective f fsur
                                                              simp only [len_mk, Fintype.card_fin, add_le_add_iff_right] at this
                                                              contradiction
                     cases n with
                     | zero   => exact (nnlem (Nat.zero_le m)).elim
                     | succ n => obtain ⟨j, g, fgdj⟩ := eq_comp_δ_of_not_surjective f nsur
                                 have := mono_of_mono_fac fgdj.symm
                                 have : n - m = i := by rwa [Nat.sub_add_comm (by simp only [not_le, Nat.lt_succ] at nnlem; exact nnlem), Nat.succ_inj] at h
                                 have := IsFace.comp (ih this g) (IsFace.delta j)
                                 rwa [fgdj]
    exact hrec (n - m) rfl f

end SimplexCategory
