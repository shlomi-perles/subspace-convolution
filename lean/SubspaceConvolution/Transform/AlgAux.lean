/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Step

/-!
# Helper lemmas for Theorem 1

* `subsingleton_subLE` and `zeta_eq_id_of_subsingleton` (etc.): for `k = 0` or `dim V = 0`
  there is a single subspace and all four transforms are the identity.
* `card_subLE_succ`, `sum_card_subLE_ker`: the entry counts of one recursion step.
* `budget_step`: the induction step of the budget `(4q+2) n k M_q(n,k)` (Section 3.3).
* `zeta_map`, `zetaInv_map`: the transforms commute with ring homomorphisms (base change).
* `transposeMap_zeta`, `transposeMap_zetaInv`: `Zᵀ` and `(Zᵀ)⁻¹` are the transposes of `Z` and
  `Z⁻¹` (transposition principle).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

namespace AlgAux

section Basic

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type*} [CommRing R]

theorem subsingleton_subLE {k : ℕ} (h : k = 0 ∨ finrank K V = 0) :
    Subsingleton (SubLE K V k) := by
  have key : ∀ U : SubLE K V k, U.1 = ⊥ := by
    intro U
    have h1 : finrank K U.1 ≤ k := U.2
    have h2 := Submodule.finrank_le U.1
    rw [← Submodule.finrank_eq_zero]
    omega
  exact ⟨fun U W => Subtype.ext ((key U).trans (key W).symm)⟩

theorem zeta_eq_id_of_subsingleton {k : ℕ} [Subsingleton (SubLE K V k)] :
    (zeta k : (SubLE K V k → R) → SubLE K V k → R) = fun f => f := by
  funext f W
  rw [zeta, sum_le_eq_add_sum_lt]
  have : IsEmpty {U : SubLE K V k // U.1 < W.1} :=
    ⟨fun U => (ne_of_lt U.2) (congrArg Subtype.val (Subsingleton.elim U.1 W))⟩
  simp only [univ_eq_empty, sum_empty, add_zero]

theorem zetaT_eq_id_of_subsingleton {k : ℕ} [Subsingleton (SubLE K V k)] :
    (zetaT k : (SubLE K V k → R) → SubLE K V k → R) = fun f => f := by
  funext f U
  rw [zetaT, sum_ge_eq_add_sum_gt]
  have : IsEmpty {W : SubLE K V k // U.1 < W.1} :=
    ⟨fun W => (ne_of_lt W.2) (congrArg Subtype.val (Subsingleton.elim U W.1))⟩
  simp only [univ_eq_empty, sum_empty, add_zero]

theorem zetaInv_eq_id_of_subsingleton {k : ℕ} [Subsingleton (SubLE K V k)] :
    (zetaInv k : (SubLE K V k → R) → SubLE K V k → R) = fun f => f := by
  funext g
  have h : zeta k g = g := congrFun zeta_eq_id_of_subsingleton g
  calc zetaInv k g = zetaInv k (zeta k g) := by rw [h]
    _ = g := zetaInv_zeta k g

theorem zetaTInv_eq_id_of_subsingleton {k : ℕ} [Subsingleton (SubLE K V k)] :
    (zetaTInv k : (SubLE K V k → R) → SubLE K V k → R) = fun f => f := by
  funext g
  have h : zetaT k g = g := congrFun zetaT_eq_id_of_subsingleton g
  calc zetaTInv k g = zetaTInv k (zetaT k g) := by rw [h]
    _ = g := zetaTInv_zetaT k g

/-! ### Base change -/

theorem zeta_map {S : Type*} [CommRing S] (φ : R →+* S) (k : ℕ) (f : SubLE K V k → R) :
    zeta k (fun U => φ (f U)) = fun W => φ (zeta k f W) := by
  funext W
  simp only [zeta, map_sum]

theorem zetaInv_map {S : Type*} [CommRing S] (φ : R →+* S) (k : ℕ) (g : SubLE K V k → R) :
    zetaInv k (fun U => φ (g U)) = fun W => φ (zetaInv k g W) := by
  have h : (fun U => φ (g U)) = zeta k (fun W => φ (zetaInv k g W)) := by
    rw [zeta_map, zeta_zetaInv]
  rw [h, zetaInv_zeta]

/-! ### Transposes -/

theorem transposeMap_eq_of_adjoint {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    {M : (I → R) → O → R} {N : (O → R) → I → R}
    (h : ∀ f g, ∑ o, M f o * g o = ∑ i, f i * N g i) : transposeMap M = N := by
  funext g i
  simp only [transposeMap]
  rw [h]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

open Classical in
theorem zeta_adjoint (k : ℕ) (f g : SubLE K V k → R) :
    ∑ o, zeta k f o * g o = ∑ i, f i * zetaT k g i := by
  simp only [zeta, zetaT, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun o _ => ?_
  split_ifs <;> ring

theorem zetaInv_adjoint (k : ℕ) (f g : SubLE K V k → R) :
    ∑ o, zetaInv k f o * g o = ∑ i, f i * zetaTInv k g i := by
  have h := zeta_adjoint k (zetaInv k f) (zetaTInv k g)
  rw [zeta_zetaInv, zetaT_zetaTInv] at h
  exact h.symm

theorem transposeMap_zeta (k : ℕ) [DecidableEq (SubLE K V k)] :
    transposeMap (zeta (K := K) (V := V) (R := R) k) = zetaT k :=
  transposeMap_eq_of_adjoint (zeta_adjoint k)

theorem transposeMap_zetaInv (k : ℕ) [DecidableEq (SubLE K V k)] :
    transposeMap (zetaInv (K := K) (V := V) (R := R) k) = zetaTInv k :=
  transposeMap_eq_of_adjoint (zetaInv_adjoint k)

end Basic

/-! ### Counting the entries of one step -/

section Counts

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `|SubLE V (k+1)| = |SubLE H (k+1)| + ∑_{B ∈ SubLE H k} |H/B|` (inside and crossing). -/
theorem card_subLE_succ (D : HypData K V) (k : ℕ) :
    Fintype.card (SubLE K V (k + 1)) =
      Fintype.card (SubLE K D.H (k + 1)) + ∑ B : SubLE K D.H k, Fintype.card (D.H ⧸ B.1) := by
  rw [Fintype.card_congr (D.split (· ≤ k + 1) (· ≤ k) (StepAux.hPk k)), Fintype.card_sum,
    Fintype.card_sigma]

/-- The copies `SubLE (ker λ) k` have as many entries as the crossing tables. -/
theorem sum_card_subLE_ker {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (k : ℕ) :
    ∑ ξ : Module.Dual K W, Fintype.card (SubLE K (LinearMap.ker ξ) k) =
      ∑ B : SubLE K W k, Fintype.card (W ⧸ B.1) := by
  have h := Fintype.card_congr (freqEquiv (K := K) (W := W) (· ≤ k))
  rw [Fintype.card_sigma, Fintype.card_sigma] at h
  rw [← h]
  exact Finset.sum_congr rfl fun B _ => card_freq B.1

theorem budget_arith (q n k Y X T : ℕ) (hT : T ≤ (4 * q + 2) * n * k * X) :
    (4 * q + 2) * n * (k + 1) * Y + T + (2 * q + 1) * (n + 1) * (X + X) ≤
      (4 * q + 2) * (n + 1) * (k + 1) * (Y + X) := by
  have e : (4 * q + 2) * (n + 1) * (k + 1) * (Y + X) =
      (4 * q + 2) * n * (k + 1) * Y + (4 * q + 2) * n * k * X +
        (2 * q + 1) * (n + 1) * (X + X) + ((4 * q + 2) * (k + 1) * Y + (4 * q + 2) * k * X) := by
    ring
  rw [e]
  omega

/-- **Section 3.3**: the induction step of the budget `(4q+2) n k M_q(n,k)`. -/
theorem budget_step (D : HypData K V) (k : ℕ) :
    (4 * Fintype.card K + 2) * finrank K D.H * (k + 1) * Fintype.card (SubLE K D.H (k + 1)) +
      ∑ ξ : Module.Dual K D.H, (4 * Fintype.card K + 2) * finrank K (LinearMap.ker ξ) * k *
        Fintype.card (SubLE K (LinearMap.ker ξ) k) +
      stepWork K (finrank K V) (H := D.H) (· ≤ k) (· ≤ k) ≤
    (4 * Fintype.card K + 2) * finrank K V * (k + 1) * Fintype.card (SubLE K V (k + 1)) := by
  have hH := D.finrank_H
  have hT : ∑ ξ : Module.Dual K D.H, (4 * Fintype.card K + 2) * finrank K (LinearMap.ker ξ) *
        k * Fintype.card (SubLE K (LinearMap.ker ξ) k) ≤
      (4 * Fintype.card K + 2) * finrank K D.H * k *
        ∑ B : SubLE K D.H k, Fintype.card (D.H ⧸ B.1) := by
    rw [← sum_card_subLE_ker, Finset.mul_sum]
    refine Finset.sum_le_sum fun ξ _ => ?_
    have := Submodule.finrank_le (LinearMap.ker ξ)
    gcongr
  rw [card_subLE_succ D k, ← hH]
  exact budget_arith _ _ _ _ _ _ hT

end Counts

/-! ### The constants of Theorem 1 -/

theorem cost_le (P c n k M : ℕ) (h : 1 ≤ n * k) :
    2 * P ^ 2 * (c * n * k * M) + P * M ≤ (2 * P ^ 2 * c + P) * n * k * M := by
  have hM : M ≤ n * k * M := Nat.le_mul_of_pos_left M h
  calc 2 * P ^ 2 * (c * n * k * M) + P * M ≤ 2 * P ^ 2 * (c * n * k * M) + P * (n * k * M) := by
        gcongr
    _ = (2 * P ^ 2 * c + P) * n * k * M := by ring

theorem cost_le_T (A n k M s : ℕ) (h : 1 ≤ n * k) (hs : s ≤ A * n * k * M) :
    2 * s + M ≤ (2 * A + 1) * n * k * M := by
  have hM : M ≤ n * k * M := Nat.le_mul_of_pos_left M h
  calc 2 * s + M ≤ 2 * (A * n * k * M) + n * k * M := by gcongr
    _ = (2 * A + 1) * n * k * M := by ring

end AlgAux

end SubspaceConvolution
