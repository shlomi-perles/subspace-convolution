/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Algorithm
import SubspaceConvolution.Circuit.Arith
import SubspaceConvolution.Coloring.Completion

/-!
# Proposition 7.3 with the cost of Theorem 1.1

`SubspaceConvolution.Completion` proves the identity behind Proposition 7.3
(`completionSum_eq_zetaOn`: `B_g(U) = (Z_r^{⊗c} g)(U₁^⊥, …, U_c^⊥)`), the coordinatewise
evaluation of `Z_r^{⊗c}` (`zetaOn_univ_eq_foldr`), and the arithmetic of the running time with
the cost `K · N log N` of one call of the one-dimensional transform `Z_r` left as a parameter
(`completion_cost_le`).  Here that parameter is replaced by the proved **Theorem 1.1**
(`fast_subspace_summation`, for `K = F₂`, `V = F₂^r`, `k = r`), and the whole computation is
assembled into one circuit in the cost models of `Circuit/SLP.lean` and `Circuit/Arith.lean`.

* `LinCost.alongCoord` — a transform applied along one coordinate of `ι → S`, the other
  coordinates held fixed (`N^{c-1}` independent copies, `LinCost.sigma`);
  `LinCost.foldr_zetaCoord` — the `c` passes composed (`LinCost.comp`).
* `CompAux.zetaAll_linCost` — the one-dimensional transform `Z_r = zetaAll` on the subspaces
  of `F₂^r` is Theorem 1.1's `Z_{r,r}` (every subspace of `F₂^r` has dimension at most `r`):
  `O(r² N)` gates with `N = N₂(r)`; `zetaCoord_eq_zetaAll` — `zetaCoord i` is `Z_r` in the
  argument `i`.
* `completionSum_linCost` — all sums `B_g` with `c · C₁ r² S` gates, `S = N^c`
  (`card_profileTuples`).
* `CompAux.mul_sq_le_log` — `c r² ≤ 7 log₂ S` (from `N₂(r) ≥ 2^{⌊r²/4⌋}`).
* `fast_completionSum`, `fast_completion_count` — **Proposition 7.3**: the sums `B_g` and the
  number `∑_U f(U) B_g(U)` take `O(S log S)` arithmetic operations, over every commutative ring
  in which `2` is invertible.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u

/-! ### The one-dimensional transform and its coordinatewise application -/

section Coord

variable {R : Type*} [CommRing R] {C : Set R}

/-- Splitting off coordinate `i`: `(t, w) ↦ (t at i, w elsewhere)` evaluated at the restriction
of `W` is `Function.update W i t`. -/
theorem CompAux.funSplitAt_symm_restrict {ι S : Type*} [DecidableEq ι] (i : ι) (W : ι → S) (t : S) :
    (Equiv.funSplitAt i S).symm (t, fun j => W j.1) = Function.update W i t := by
  funext j
  rw [Equiv.funSplitAt_symm_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- **A transform along one coordinate.**  Applying a map `M` of cost `A · |S|` to the argument
`i` of a table on `ι → S`, holding the other arguments fixed, takes `|S|^{|ι|-1}` independent copies
of `M` (one for each value of the other arguments), of total cost `A · |S|^{|ι|}`. -/
theorem Circuit.LinCost.alongCoord {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]
    {M : (S → R) → S → R} {A : ℕ} (h : LinCost C M (A * Fintype.card S)) (i : ι) :
    LinCost C (fun (g : (ι → S) → R) (W : ι → S) => M (fun t => g (Function.update W i t)) (W i))
      (A * Fintype.card (ι → S)) := by
  have hs := LinCost.sigma (ι := {j // j ≠ i} → S) (I' := fun _ => S) (O' := fun _ => S)
    (fun _ => M) (fun _ => A * Fintype.card S) (fun _ => h)
  have h2 := hs.reindex
    (fun p : (Σ _ : {j // j ≠ i} → S, S) => (Equiv.funSplitAt i S).symm (p.2, p.1))
    (fun W : ι → S => (⟨fun j => W j.1, W i⟩ : Σ _ : {j // j ≠ i} → S, S))
  refine (h2.congr ?_).mono (le_of_eq ?_)
  · funext g W
    simp only [CompAux.funSplitAt_symm_restrict]
  · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_congr (Equiv.funSplitAt i S), Fintype.card_prod]
    ring

/-- The `c` passes of the coordinatewise evaluation of `Z^{⊗c}`, composed: the costs add. -/
theorem Circuit.LinCost.foldr_zetaCoord {ι S : Type*} [DecidableEq ι] [Fintype S]
    [PartialOrder S] {T : ℕ} (h : ∀ i : ι, LinCost C (zetaCoord (S := S) (R := R) i) T)
    (l : List ι) :
    LinCost C (fun g => l.foldr (zetaCoord (S := S) (R := R)) g) (l.length * T) := by
  induction l with
  | nil => exact (LinCost.id.congr (by funext g; rfl)).mono (by simp)
  | cons i l ih =>
    exact ((ih.comp (h i)).congr (by funext g; rfl)).mono
      (le_of_eq (by simp only [List.length_cons, Nat.succ_mul]))

end Coord

/-! ### Theorem 1.1 on the subspaces of `F₂^r` -/

namespace CompAux

/-- Every subspace of `F₂^r` has dimension at most `r`. -/
theorem finrank_sub_le {r : ℕ} (U : Submodule F2 (Fin r → F2)) : finrank F2 U ≤ r :=
  (Submodule.finrank_le U).trans_eq (Module.finrank_fin_fun F2)

/-- `SubLE F₂ F₂^r r` is the type of all subspaces of `F₂^r`. -/
def subLEEquiv (r : ℕ) : SubLE F2 (Fin r → F2) r ≃ Submodule F2 (Fin r → F2) :=
  Equiv.subtypeUnivEquiv finrank_sub_le

/-- `Z_{r,r}` read on all subspaces of `F₂^r` is the full zeta transform `Z_r = zetaAll`. -/
theorem zeta_subLEEquiv {R : Type*} [CommRing R] (r : ℕ) (g : Submodule F2 (Fin r → F2) → R)
    (W : Submodule F2 (Fin r → F2)) :
    zeta (K := F2) (V := Fin r → F2) r (fun U => g (subLEEquiv r U)) ((subLEEquiv r).symm W) =
      zetaAll g W := by
  classical
  unfold zeta zetaAll
  refine Finset.sum_equiv (subLEEquiv r) (fun U => ?_) (fun U _ => rfl)
  simp [subLEEquiv]

/-- **Theorem 1.1 for the one-dimensional transform `Z_r` on `Sub(F₂^r)`**: over every
commutative ring in which `2` is invertible, `zetaAll` on the `N = N₂(r)` subspaces of `F₂^r`
costs `O(r² N)` gates. -/
theorem zetaAll_linCost :
    ∃ C₁ : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (2 : R) → ∀ r : ℕ,
      LinCost (Set.univ : Set R) (zetaAll (K := F2) (V := Fin r → F2))
        (C₁ * r * r * Fintype.card (Submodule F2 (Fin r → F2))) := by
  obtain ⟨C₁, hC₁⟩ := fast_subspace_summation.{u, 0, 0} F2
  refine ⟨C₁, fun R _ hR r => ?_⟩
  have hR' : IsUnit ((ringChar F2 : ℕ) : R) := by
    rw [ZMod.ringChar_zmod_n]
    exact_mod_cast hR
  have hfin : finrank F2 (Fin r → F2) = r := Module.finrank_fin_fun F2
  have h := (hC₁ R hR' (Fin r → F2) r hfin.ge).1
  refine ((h.reindex (subLEEquiv r) (subLEEquiv r).symm).congr ?_).mono (le_of_eq ?_)
  · funext g W
    exact zeta_subLEEquiv r g W
  · rw [hfin, Fintype.card_congr (subLEEquiv r)]

end CompAux

/-! ### The sums `B_g` -/

/-- `zetaCoord i` on `c`-tuples of subspaces of `F₂^r` is the one-dimensional transform
`Z_r = zetaAll` in the argument `i`, the other arguments held fixed. -/
theorem zetaCoord_eq_zetaAll {R : Type*} [CommRing R] {c r : ℕ} (i : Fin c)
    (g : (Fin c → Submodule F2 (Fin r → F2)) → R) (W : Fin c → Submodule F2 (Fin r → F2)) :
    zetaCoord i g W = zetaAll (K := F2) (fun t => g (Function.update W i t)) (W i) :=
  rfl

/-- **All sums `B_g` as one circuit**: if the one-dimensional transform `Z_r` on `Sub(F₂^r)`
costs `A · N`, the `c` coordinatewise passes cost `c · A · S` (`S = N^c`); the final reindexing
`U ↦ (U₁^⊥, …, U_c^⊥)` is free. -/
theorem completionSum_linCost {R : Type*} [CommRing R] {C : Set R} (c r : ℕ) {A : ℕ}
    (h : LinCost C (zetaAll (K := F2) (V := Fin r → F2) (R := R))
      (A * Fintype.card (Submodule F2 (Fin r → F2)))) :
    LinCost C (fun g : (Fin c → Submodule F2 (Fin r → F2)) → R => completionSum g)
      (c * (A * Fintype.card (Fin c → Submodule F2 (Fin r → F2)))) := by
  have hcoord : ∀ i : Fin c, LinCost C (zetaCoord (S := Submodule F2 (Fin r → F2)) (R := R) i)
      (A * Fintype.card (Fin c → Submodule F2 (Fin r → F2))) := fun i =>
    (h.alongCoord i).congr (by funext g W; exact (zetaCoord_eq_zetaAll i g W).symm)
  have hfold := LinCost.foldr_zetaCoord hcoord (univ : Finset (Fin c)).toList
  rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin] at hfold
  refine (hfold.reindex id (fun U i => perp (U i))).congr ?_
  funext g U
  rw [completionSum_eq_zetaOn, zetaOn_univ_eq_foldr]
  rfl

/-- The number of `c`-tuples of subspaces of `F₂^r` is `S = N₂(r)^c`. -/
theorem card_profileTuples (c r : ℕ) :
    Fintype.card (Fin c → Submodule F2 (Fin r → F2)) = numSubspaces r ^ c := by
  rw [Fintype.card_fun, Fintype.card_fin, numSubspaces, Nat.card_eq_fintype_card]

/-- **The arithmetic of the running time**: `c r² ≤ 7 log₂ S` with `S = N₂(r)^c`, since
`N₂(r) ≥ 2^{⌊r²/4⌋}` gives `r² ≤ 4 log₂ N₂(r) + 3`, and `log₂ N₂(r) ≥ 1` for `r ≥ 1`. -/
theorem CompAux.mul_sq_le_log (c r : ℕ) :
    c * (r * r) ≤ 7 * Nat.log 2 (Fintype.card (Fin c → Submodule F2 (Fin r → F2))) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  rw [card_profileTuples]
  have hN0 : numSubspaces r ≠ 0 := (numSubspaces_pos r).ne'
  have h1 : r * r / 4 ≤ Nat.log 2 (numSubspaces r) :=
    Nat.le_log_of_pow_le one_lt_two (le_numSubspaces r)
  have h2 : 1 ≤ Nat.log 2 (numSubspaces r) := by
    refine Nat.le_log_of_pow_le one_lt_two ?_
    have := numSubspaces_mono (show 1 ≤ r from hr)
    rw [numSubspaces_one] at this
    simpa using this
  have h3 : c * Nat.log 2 (numSubspaces r) ≤ Nat.log 2 (numSubspaces r ^ c) := by
    refine Nat.le_log_of_pow_le one_lt_two ?_
    rw [pow_mul']
    exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hN0) c
  have h4 : r * r ≤ 7 * Nat.log 2 (numSubspaces r) := by
    generalize r * r = m at h1 ⊢
    omega
  calc c * (r * r) ≤ c * (7 * Nat.log 2 (numSubspaces r)) := Nat.mul_le_mul_left c h4
    _ = 7 * (c * Nat.log 2 (numSubspaces r)) := by ring
    _ ≤ 7 * Nat.log 2 (numSubspaces r ^ c) := Nat.mul_le_mul_left 7 h3

/-- **Proposition 7.3**, the sums `B_g`: `O(S log S)` arithmetic operations, `S = N₂(r)^c`.

This replaces the cost parameter `K` of `completion_cost_le` (the cost `K · N log N` of one call
of the one-dimensional transform `Z_r`) by the proved Theorem 1.1 (`fast_subspace_summation`):
the circuit applies `Z_r` along each of the `c` arguments (`c · N^{c-1}` calls) and reads the
result at `(U₁^⊥, …, U_c^⊥)` (`completionSum_eq_zetaOn`). -/
theorem fast_completionSum :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (2 : R) → ∀ (c r : ℕ),
      LinCost (Set.univ : Set R)
        (fun (g : (Fin c → Submodule F2 (Fin r → F2)) → R) => completionSum g)
        (C * Fintype.card (Fin c → Submodule F2 (Fin r → F2)) *
          (Nat.log 2 (Fintype.card (Fin c → Submodule F2 (Fin r → F2))) + 1)) := by
  obtain ⟨C₁, hC₁⟩ := CompAux.zetaAll_linCost.{u}
  refine ⟨7 * C₁, fun R _ hR c r => ?_⟩
  refine (completionSum_linCost c r (A := C₁ * r * r) (hC₁ R hR r)).mono ?_
  have hlog := CompAux.mul_sq_le_log c r
  generalize Fintype.card (Fin c → Submodule F2 (Fin r → F2)) = S at hlog ⊢
  calc c * (C₁ * r * r * S) = C₁ * S * (c * (r * r)) := by ring
    _ ≤ C₁ * S * (7 * Nat.log 2 S) := Nat.mul_le_mul_left _ hlog
    _ ≤ 7 * C₁ * S * (Nat.log 2 S + 1) := by
      rw [show C₁ * S * (7 * Nat.log 2 S) = 7 * C₁ * S * Nat.log 2 S by ring]
      exact Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- **Proposition 7.3**, the number `∑_U f(U) B_g(U)` (bilinear in `f` and `g`, given as the two
halves of one input table): `O(S log S)` arithmetic operations, `S = N₂(r)^c`.  The sums `B_g`
(`fast_completionSum`), then `S` products `f(U) B_g(U)` (`ArithCost.mulPointwise`) and their
sum (one dense all-ones row, `S` gates). -/
theorem fast_completion_count :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (2 : R) → ∀ (c r : ℕ),
      ArithCost
        (fun (x : (Fin c → Submodule F2 (Fin r → F2)) ⊕ (Fin c → Submodule F2 (Fin r → F2)) → R)
          (_ : Unit) => ∑ U, x (Sum.inl U) * completionSum (fun W => x (Sum.inr W)) U)
        (C * Fintype.card (Fin c → Submodule F2 (Fin r → F2)) *
          (Nat.log 2 (Fintype.card (Fin c → Submodule F2 (Fin r → F2))) + 1)) := by
  obtain ⟨C₀, hC₀⟩ := fast_completionSum.{u}
  refine ⟨C₀ + 2, fun R _ hR c r => ?_⟩
  have h1 := LinCost.sumElim
    ((LinCost.id (C := (Set.univ : Set R)) (I := Fin c → Submodule F2 (Fin r → F2))).reindex
      Sum.inl id)
    ((hC₀ R hR c r).reindex Sum.inr id)
  have h2 := (ArithCost.of_linCost h1).comp
    (ArithCost.mulPointwise (R := R) (J := Fin c → Submodule F2 (Fin r → F2)))
  have h3 := h2.comp (ArithCost.of_linCost (LinCost.dense (C := (Set.univ : Set R))
    (fun (_ : Unit) (_ : Fin c → Submodule F2 (Fin r → F2)) => (1 : R))
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)))
  refine (h3.congr ?_).mono ?_
  · funext x _
    simp only [Sum.elim_inl, Sum.elim_inr, id, one_mul]
  · rw [Fintype.card_unit, one_mul]
    generalize Fintype.card (Fin c → Submodule F2 (Fin r → F2)) = S
    have : C₀ * S * (Nat.log 2 S + 1) + S + S ≤ (C₀ + 2) * S * (Nat.log 2 S + 1) := by
      have hS : S ≤ S * (Nat.log 2 S + 1) := Nat.le_mul_of_pos_right S (Nat.succ_pos _)
      calc C₀ * S * (Nat.log 2 S + 1) + S + S
          ≤ C₀ * S * (Nat.log 2 S + 1) + S * (Nat.log 2 S + 1) + S * (Nat.log 2 S + 1) := by
            omega
        _ = (C₀ + 2) * S * (Nat.log 2 S + 1) := by ring
    omega

end SubspaceConvolution
