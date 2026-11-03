/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Defs
import SubspaceConvolution.Transform.CountAux

/-!
# Counting subspaces over `F_q` and the running-time budgets (Appendices A, B; Section 3.3)

`gr K n j = |Gr(n, j)|` and `numLE K n k = M_q(n, k)` (defined in `Transform/Defs.lean` as
cardinalities of the subspace types of `K^n`).  Write `q = |K|`.

* Appendix A: `gr_mul_prod` (eq. 24), `gr_succ_succ` (eq. 25), `gr_symm` (annihilators),
  `pow_le_gr`/`gr_le` (`|Gr(n,r)| = Θ_q(q^{r(n-r)})`), `pow_le_numLE_self`/`numLE_self_le`
  (`N_q(n) = Θ_q(q^{⌊n²/4⌋})`), `numLE_le_two_mul_gr` (eq. 26), `coverPairs_*`
  (eq. 27).
* Section 3.3: `numLE_count` (eq. 11), `two_mul_numLE_le` (`M_q(n,k) - 2 M_q(n-1,k) ≥ 0`),
  `mul_le_log_numLE` (`nk = O(log M_q(n, k))`).
* Appendix B: `incidBound`, `slack` (eq. (28)), `incid_budget_step` (the induction step),
  `incidBound_le` (`n min(a, n-b) ≤ 2 log_q S`, hence `O(S log S)`).

Everything is derived from the product formula `gr_mul_prod` through the two ratio identities
`CountAux.gr_succ_right_mul` (`(q^{j+1} - 1) |Gr(n, j+1)| = (q^{n-j} - 1) |Gr(n, j)|`) and
`CountAux.gr_succ_left_mul` (`(q^{n+1-j} - 1) |Gr(n+1, j)| = (q^{n+1} - 1) |Gr(n, j)|`); the
elementary arithmetic is in `Transform/CountAux.lean`.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open CountAux

variable (K : Type*) [Field K] [Fintype K]

local notation "q" => Fintype.card K

namespace CountAux

theorem two_le_card : 2 ≤ q := Fintype.one_lt_card

/-- Eq. (24) with `qprod q j j = ∏_{i<j} (q^j - q^i)`. -/
theorem gr_mul_qprod {n j : ℕ} (h : j ≤ n) : gr K n j * qprod q j j = qprod q n j := by
  have := card_finrank_eq_mul_prod_fin (K := K) h
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ j - q ^ i),
    Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i)] at this
  rw [gr, ← Nat.card_eq_fintype_card]
  exact this

end CountAux

/-! ### Appendix A -/

theorem gr_zero_right (n : ℕ) : gr K n 0 = 1 := by
  rw [gr]
  have : Unique (Grass K (Fin n → K) 0) :=
    { default := ⟨⊥, finrank_bot K (Fin n → K)⟩
      uniq := fun U => Subtype.ext (Submodule.finrank_eq_zero.1 U.2) }
  exact Fintype.card_unique

theorem gr_eq_zero_of_lt {n j : ℕ} (h : n < j) : gr K n j = 0 := by
  rw [gr, Fintype.card_eq_zero_iff]
  refine ⟨fun U => ?_⟩
  have h1 := Submodule.finrank_le U.1
  have h2 : finrank K U.1 = j := U.2
  rw [Module.finrank_fin_fun] at h1
  omega

theorem gr_self (n : ℕ) : gr K n n = 1 := by
  rw [gr]
  have : Unique (Grass K (Fin n → K) n) :=
    { default := ⟨⊤, by rw [finrank_top, Module.finrank_fin_fun]⟩
      uniq := fun U => Subtype.ext (Submodule.eq_top_of_finrank_eq (by
        have h : finrank K U.1 = n := U.2
        rw [h, Module.finrank_fin_fun])) }
  exact Fintype.card_unique

theorem gr_pos {n j : ℕ} (h : j ≤ n) : 0 < gr K n j := by
  have h1 := gr_mul_qprod K h
  have h2 : 0 < qprod q n j := qprod_pos (two_le_card K) h
  rw [← h1] at h2
  exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h2

/-- Equation (24): counting ordered bases. -/
theorem gr_mul_prod {n j : ℕ} (h : j ≤ n) :
    gr K n j * ∏ i ∈ range j, (q ^ j - q ^ i) = ∏ i ∈ range j, (q ^ n - q ^ i) :=
  gr_mul_qprod K h

namespace CountAux

/-- Ratio identity: `(q^{j+1} - 1) |Gr(n, j+1)| = (q^{n-j} - 1) |Gr(n, j)|` (for all `n, j`). -/
theorem gr_succ_right_mul (n j : ℕ) :
    gr K n (j + 1) * (q ^ (j + 1) - 1) = gr K n j * (q ^ (n - j) - 1) := by
  rcases Nat.lt_or_ge j n with hjn | hjn
  · have h1 := gr_mul_qprod K (show j + 1 ≤ n by omega)
    have h2 := gr_mul_qprod K hjn.le
    have hpos : 0 < q ^ j * qprod q j j :=
      Nat.mul_pos (Nat.pow_pos (by have := two_le_card K; omega))
        (qprod_pos (two_le_card K) le_rfl)
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc gr K n (j + 1) * (q ^ (j + 1) - 1) * (q ^ j * qprod q j j)
        = gr K n (j + 1) * qprod q (j + 1) (j + 1) := by rw [qprod_self_succ]; ring
      _ = qprod q n (j + 1) := h1
      _ = qprod q n j * (q ^ j * (q ^ (n - j) - 1)) := by
          rw [qprod_succ, pow_sub_pow_eq q hjn.le]
      _ = gr K n j * qprod q j j * (q ^ j * (q ^ (n - j) - 1)) := by rw [h2]
      _ = gr K n j * (q ^ (n - j) - 1) * (q ^ j * qprod q j j) := by ring
  · rw [gr_eq_zero_of_lt K (by omega : n < j + 1), Nat.sub_eq_zero_of_le hjn, pow_zero,
      Nat.sub_self, zero_mul, mul_zero]

/-- Ratio identity: `(q^{n+1-j} - 1) |Gr(n+1, j)| = (q^{n+1} - 1) |Gr(n, j)|` (for all `n, j`). -/
theorem gr_succ_left_mul (n j : ℕ) :
    gr K (n + 1) j * (q ^ (n + 1 - j) - 1) = gr K n j * (q ^ (n + 1) - 1) := by
  cases j with
  | zero => simp [gr_zero_right]
  | succ j =>
    rcases Nat.lt_or_ge j n with hjn | hjn
    · have h1 := gr_mul_qprod K (show j + 1 ≤ n + 1 by omega)
      have h2 := gr_mul_qprod K (show j + 1 ≤ n by omega)
      have hD : 0 < qprod q (j + 1) (j + 1) := qprod_pos (two_le_card K) le_rfl
      have e : n + 1 - (j + 1) = n - j := by omega
      refine Nat.eq_of_mul_eq_mul_right hD ?_
      calc gr K (n + 1) (j + 1) * (q ^ (n + 1 - (j + 1)) - 1) * qprod q (j + 1) (j + 1)
          = qprod q (n + 1) (j + 1) * (q ^ (n - j) - 1) := by rw [← h1, e]; ring
        _ = (q ^ (n + 1) - 1) * q ^ j * qprod q n j * (q ^ (n - j) - 1) := by
            rw [qprod_succ_succ]
        _ = qprod q n (j + 1) * (q ^ (n + 1) - 1) := by
            rw [qprod_succ, pow_sub_pow_eq q hjn.le]; ring
        _ = gr K n (j + 1) * (q ^ (n + 1) - 1) * qprod q (j + 1) (j + 1) := by rw [← h2]; ring
    · rw [show n + 1 - (j + 1) = 0 by omega, pow_zero, Nat.sub_self, mul_zero,
        gr_eq_zero_of_lt K (by omega : n < j + 1), zero_mul]

end CountAux

/-- Equation (25): `|Gr(n+1, j+1)| = |Gr(n, j+1)| + q^{n-j} |Gr(n, j)|`. -/
theorem gr_succ_succ (n j : ℕ) : gr K (n + 1) (j + 1) = gr K n (j + 1) + q ^ (n - j) * gr K n j := by
  rcases Nat.lt_trichotomy j n with hjn | rfl | hjn
  · have h1 := gr_succ_left_mul K n (j + 1)
    have h2 := gr_succ_right_mul K n j
    rw [show n + 1 - (j + 1) = n - j by omega] at h1
    have hq := two_le_card K
    have hu : 1 < q ^ (n - j) := Nat.one_lt_pow (by omega) (by omega)
    have hv : 1 ≤ q ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
    have hw : 1 ≤ q ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
    have hqn : q ^ (n + 1) = q ^ (n - j) * q ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    refine Nat.eq_of_mul_eq_mul_right (show 0 < q ^ (n - j) - 1 by omega) ?_
    rw [h1, hqn]
    have hw' : 1 ≤ q ^ (n - j) * q ^ (j + 1) := hqn ▸ hw
    zify [hu.le, hv, hw'] at h2 ⊢
    linear_combination ((q : ℤ) ^ (n - j)) * h2
  · simp [gr_self, gr_eq_zero_of_lt K (Nat.lt_succ_self j)]
  · simp [gr_eq_zero_of_lt K (by omega : n + 1 < j + 1), gr_eq_zero_of_lt K (by omega : n < j + 1),
      gr_eq_zero_of_lt K hjn]

namespace CountAux

/-- `|Gr(n, j)| · qfac q j · qfac q (n - j) = qfac q n` (the `q`-binomial formula). -/
theorem gr_mul_qfac {n j : ℕ} (h : j ≤ n) : gr K n j * qfac q j * qfac q (n - j) = qfac q n := by
  induction j with
  | zero => simp [gr_zero_right]
  | succ j ih =>
    have ih := ih (by omega)
    have h2 := gr_succ_right_mul K n j
    have e : n - j = (n - (j + 1)) + 1 := by omega
    rw [qfac_succ]
    calc gr K n (j + 1) * (qfac q j * (q ^ (j + 1) - 1)) * qfac q (n - (j + 1))
        = gr K n (j + 1) * (q ^ (j + 1) - 1) * qfac q j * qfac q (n - (j + 1)) := by ring
      _ = gr K n j * (q ^ (n - j) - 1) * qfac q j * qfac q (n - (j + 1)) := by rw [h2]
      _ = gr K n j * qfac q j * (qfac q (n - (j + 1)) * (q ^ (n - (j + 1) + 1) - 1)) := by
          rw [← e]; ring
      _ = gr K n j * qfac q j * qfac q (n - j) := by rw [← qfac_succ, ← e]
      _ = qfac q n := ih

end CountAux

/-- Annihilators: `|Gr(n, n-j)| = |Gr(n, j)|`. -/
theorem gr_symm {n j : ℕ} (h : j ≤ n) : gr K n (n - j) = gr K n j := by
  have h1 := gr_mul_qfac K (Nat.sub_le n j)
  have h2 := gr_mul_qfac K h
  rw [Nat.sub_sub_self h] at h1
  have hq : 1 < q := two_le_card K
  have hpos : 0 < qfac q j * qfac q (n - j) := Nat.mul_pos (qfac_pos hq _) (qfac_pos hq _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc gr K n (n - j) * (qfac q j * qfac q (n - j))
      = gr K n (n - j) * qfac q (n - j) * qfac q j := by ring
    _ = qfac q n := h1
    _ = gr K n j * (qfac q j * qfac q (n - j)) := by rw [← h2]; ring

/-- `[n]_q (q - 1) = q^n - 1`: the number of lines. -/
theorem gr_one_mul (n : ℕ) : gr K n 1 * (q - 1) = q ^ n - 1 := by
  have := gr_succ_right_mul K n 0
  simpa [gr_zero_right] using this

/-- Equation (24), lower bound. -/
theorem pow_le_gr {n j : ℕ} (h : j ≤ n) : q ^ (j * (n - j)) ≤ gr K n j := by
  have h1 := gr_mul_qprod K h
  have h2 := pow_mul_qprod_le (by have := two_le_card K; omega : 0 < q) h
  rw [← h1] at h2
  exact Nat.le_of_mul_le_mul_right h2 (qprod_pos (two_le_card K) le_rfl)

/-- Equation (24), upper bound (uniform in `q ≥ 2`). -/
theorem gr_le (n j : ℕ) : gr K n j ≤ 4 * q ^ (j * (n - j)) := by
  rcases Nat.lt_or_ge n j with h | h
  · rw [gr_eq_zero_of_lt K h]; exact Nat.zero_le _
  have h1 := gr_mul_qprod K h
  have h2 := pow_le_four_mul_qprod (two_le_card K) j
  have h3 := qprod_le q n j
  have h4 : n * j = j * (n - j) + j * j := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h, Nat.mul_comm]
  refine Nat.le_of_mul_le_mul_right (c := q ^ (j * j)) ?_
    (Nat.pow_pos (by have := two_le_card K; omega))
  calc gr K n j * q ^ (j * j) ≤ gr K n j * (4 * qprod q j j) := Nat.mul_le_mul_left _ h2
    _ = 4 * (gr K n j * qprod q j j) := by ring
    _ = 4 * qprod q n j := by rw [h1]
    _ ≤ 4 * q ^ (n * j) := Nat.mul_le_mul_left _ h3
    _ = 4 * q ^ (j * (n - j)) * q ^ (j * j) := by rw [h4, pow_add, mul_assoc]

/-- `|Gr(n, j)| / |Gr(n+1, j)| ≤ q^{-j}`. -/
theorem pow_mul_gr_le (n j : ℕ) : q ^ j * gr K n j ≤ gr K (n + 1) j := by
  rcases Nat.lt_or_ge n j with h | h
  · rw [gr_eq_zero_of_lt K h, mul_zero]; exact Nat.zero_le _
  have h1 := gr_succ_left_mul K n j
  have hq := two_le_card K
  have hm : 1 < q ^ (n + 1 - j) := Nat.one_lt_pow (by omega) (by omega)
  have h2 : q ^ j * (q ^ (n + 1 - j) - 1) ≤ q ^ (n + 1) - 1 := by
    rw [← pow_sub_pow_eq q (by omega : j ≤ n + 1)]
    exact Nat.sub_le_sub_left (Nat.one_le_pow _ _ (by omega)) _
  refine Nat.le_of_mul_le_mul_right (c := q ^ (n + 1 - j) - 1) ?_ (by omega)
  calc q ^ j * gr K n j * (q ^ (n + 1 - j) - 1)
      = gr K n j * (q ^ j * (q ^ (n + 1 - j) - 1)) := by ring
    _ ≤ gr K n j * (q ^ (n + 1) - 1) := Nat.mul_le_mul_left _ h2
    _ = gr K (n + 1) j * (q ^ (n + 1 - j) - 1) := h1.symm

theorem numLE_eq_sum (n k : ℕ) : numLE K n k = ∑ j ∈ range (k + 1), gr K n j := by
  let f : SubLE K (Fin n → K) k → Fin (k + 1) := fun U => ⟨finrank K U.1, Nat.lt_succ_of_le U.2⟩
  rw [← Fin.sum_univ_eq_sum_range (fun j => gr K n j), numLE, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gr, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1.1, congrArg Fin.val x.2⟩
      invFun := fun W => ⟨⟨W.1, by
          have h1 : finrank K W.1 = j := W.2
          have h2 := j.2
          show finrank K W.1 ≤ k
          omega⟩, Fin.ext W.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

namespace CountAux

theorem gr_le_numLE {n j k : ℕ} (h : j ≤ k) : gr K n j ≤ numLE K n k := by
  rw [numLE_eq_sum]
  exact single_le_sum (f := fun i => gr K n i) (fun i _ => Nat.zero_le _)
    (mem_range.2 (by omega))

end CountAux

/-- `N_q(n) = Θ_q(q^{⌊n²/4⌋})`, lower bound. -/
theorem pow_le_numLE_self (n : ℕ) : q ^ (n * n / 4) ≤ numLE K n n := by
  rw [mul_self_div_four]
  exact (pow_le_gr K (Nat.div_le_self n 2)).trans (gr_le_numLE K (Nat.div_le_self n 2))

/-- `N_q(n) = Θ_q(q^{⌊n²/4⌋})`, upper bound. -/
theorem numLE_self_le (n : ℕ) : numLE K n n ≤ 16 * q ^ (n * n / 4) := by
  rw [numLE_eq_sum]
  calc ∑ j ∈ range (n + 1), gr K n j ≤ ∑ j ∈ range (n + 1), 4 * q ^ (j * (n - j)) :=
        sum_le_sum fun j _ => gr_le K n j
    _ = 4 * ∑ j ∈ range (n + 1), q ^ (j * (n - j)) := by rw [mul_sum]
    _ ≤ 4 * (4 * q ^ (n * n / 4)) :=
        Nat.mul_le_mul_left _ (sum_pow_mul_sub_le (two_le_card K) n)
    _ = 16 * q ^ (n * n / 4) := by ring

namespace CountAux

/-- Below the middle, `|Gr(n, j)|` at least doubles: `2 |Gr(n, j)| ≤ |Gr(n, j+1)|` for
`2(j+1) ≤ n`. -/
theorem two_mul_gr_le_gr_succ {n j : ℕ} (h : 2 * (j + 1) ≤ n) :
    2 * gr K n j ≤ gr K n (j + 1) := by
  have h1 := gr_succ_right_mul K n j
  have hq := two_le_card K
  have h2 : 2 * q ^ (j + 1) ≤ q ^ (n - j) := by
    calc 2 * q ^ (j + 1) ≤ q * q ^ (j + 1) := Nat.mul_le_mul_right _ hq
      _ = q ^ (j + 2) := by ring
      _ ≤ q ^ (n - j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 1 < q ^ (j + 1) := Nat.one_lt_pow (by omega) (by omega)
  refine Nat.le_of_mul_le_mul_right (c := q ^ (j + 1) - 1) ?_ (by omega)
  rw [h1]
  calc 2 * gr K n j * (q ^ (j + 1) - 1) = gr K n j * (2 * (q ^ (j + 1) - 1)) := by ring
    _ ≤ gr K n j * (q ^ (n - j) - 1) := Nat.mul_le_mul_left _ (by omega)

theorem gr_mul_two_pow_le {n k : ℕ} (h : 2 * k ≤ n) :
    ∀ t ≤ k, gr K n (k - t) * 2 ^ t ≤ gr K n k := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := two_mul_gr_le_gr_succ K (n := n) (j := k - (t + 1)) (by omega)
    rw [show k - (t + 1) + 1 = k - t by omega] at h1
    calc gr K n (k - (t + 1)) * 2 ^ (t + 1) = 2 * gr K n (k - (t + 1)) * 2 ^ t := by ring
      _ ≤ gr K n (k - t) * 2 ^ t := Nat.mul_le_mul_right _ h1
      _ ≤ gr K n k := ih (by omega)

end CountAux

/-- Equation (26): `M_q(n, k) = Θ_q(|Gr(n, k)|)` for `k ≤ n/2`. -/
theorem numLE_le_two_mul_gr {n k : ℕ} (h : 2 * k ≤ n) : numLE K n k ≤ 2 * gr K n k := by
  rw [numLE_eq_sum, ← sum_range_reflect]
  refine sum_le_two_mul_of_mul_pow_le fun t ht => ?_
  rw [show k + 1 - 1 - t = k - t by omega]
  exact gr_mul_two_pow_le K h t (by omega)

/-- The number of pairs `U < W` with `dim W = dim U + 1`. -/
noncomputable def coverPairs (n : ℕ) : ℕ := ∑ r ∈ range n, gr K n r * gr K (n - r) 1

namespace CountAux

/-- `q^{m-1} ≤ [m]_q`. -/
theorem pow_pred_le_gr_one {m : ℕ} (hm : 1 ≤ m) : q ^ (m - 1) ≤ gr K m 1 := by
  have h := gr_one_mul K m
  have hq := two_le_card K
  refine Nat.le_of_mul_le_mul_right (c := q - 1) ?_ (by omega)
  rw [h]
  have e : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hm]
  have h1 : 1 ≤ q ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
  rw [e, Nat.mul_sub_one]
  omega

/-- `[m]_q ≤ 2 q^{m-1}`. -/
theorem gr_one_le_two_mul_pow {m : ℕ} (hm : 1 ≤ m) : gr K m 1 ≤ 2 * q ^ (m - 1) := by
  have h := gr_one_mul K m
  have hq := two_le_card K
  refine Nat.le_of_mul_le_mul_right (c := q - 1) ?_ (by omega)
  rw [h]
  have e : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [e]
  obtain ⟨r, hr⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  obtain ⟨P, hP⟩ : ∃ P, q ^ (m - 1) = P := ⟨_, rfl⟩
  have h1 : 1 ≤ P := hP ▸ Nat.one_le_pow _ _ (by omega)
  rw [hP, hr, show r + 2 - 1 = r + 1 by omega]
  have : P * (r + 2) = P * r + 2 * P := by ring
  have : 2 * P * (r + 1) = 2 * (P * r) + 2 * P := by ring
  omega

end CountAux

/-- Equation (27), lower bound. -/
theorem pow_le_coverPairs {n : ℕ} (hn : 1 ≤ n) :
    q ^ ((n + 1) * (n + 1) / 4 - 1) ≤ coverPairs K n := by
  obtain ⟨s, hs⟩ : ∃ s, s = (n + 1) / 2 := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by omega
  have hsn : s ≤ n := by omega
  have hexp : (n + 1) * (n + 1) / 4 = s * (n + 1 - s) := by rw [hs]; exact mul_self_div_four _
  have hterm : q ^ ((n + 1) * (n + 1) / 4 - 1) ≤ gr K n (s - 1) * gr K (n - (s - 1)) 1 := by
    have h1 := pow_le_gr K (show s - 1 ≤ n by omega)
    have h2 := pow_pred_le_gr_one K (show 1 ≤ n - (s - 1) by omega)
    calc q ^ ((n + 1) * (n + 1) / 4 - 1)
        = q ^ ((s - 1) * (n - (s - 1))) * q ^ (n - (s - 1) - 1) := by
          rw [← pow_add, hexp]
          congr 1
          obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
          obtain ⟨u, hu⟩ : ∃ u, n - t = u + 1 := ⟨n - t - 1, by omega⟩
          rw [show n + 1 - (t + 1) = u + 1 by omega, show t + 1 - 1 = t by omega, hu,
            Nat.add_sub_cancel, show (t + 1) * (u + 1) = t * (u + 1) + u + 1 by ring,
            Nat.add_sub_cancel]
      _ ≤ gr K n (s - 1) * gr K (n - (s - 1)) 1 := Nat.mul_le_mul h1 h2
  exact hterm.trans (single_le_sum (f := fun r => gr K n r * gr K (n - r) 1)
    (fun i _ => Nat.zero_le _) (mem_range.2 (by omega)))

/-- Equation (27), upper bound. -/
theorem coverPairs_le (n : ℕ) : coverPairs K n ≤ 64 * q ^ ((n + 1) * (n + 1) / 4 - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coverPairs]
  have hq := two_le_card K
  have hterm : ∀ r ∈ range n,
      q * (gr K n r * gr K (n - r) 1) ≤ 8 * q ^ ((r + 1) * (n + 1 - (r + 1))) := by
    intro r hr
    have hr' := mem_range.1 hr
    have h1 := gr_le K n r
    have h2 := gr_one_le_two_mul_pow K (show 1 ≤ n - r by omega)
    calc q * (gr K n r * gr K (n - r) 1)
        ≤ q * (4 * q ^ (r * (n - r)) * (2 * q ^ (n - r - 1))) := by gcongr
      _ = 8 * q ^ (r * (n - r) + (n - r - 1) + 1) := by rw [pow_succ, pow_add]; ring
      _ = 8 * q ^ ((r + 1) * (n + 1 - (r + 1))) := by
          congr 2
          rw [show n + 1 - (r + 1) = n - r by omega, add_mul, one_mul]
          omega
  have hsub : ∑ r ∈ range n, q ^ ((r + 1) * (n + 1 - (r + 1))) ≤
      ∑ j ∈ range (n + 1 + 1), q ^ (j * (n + 1 - j)) := by
    rw [sum_range_succ' (fun j => q ^ (j * (n + 1 - j))), sum_range_succ]
    omega
  have hsum : q * coverPairs K n ≤ 8 * (4 * q ^ ((n + 1) * (n + 1) / 4)) := by
    calc q * coverPairs K n = ∑ r ∈ range n, q * (gr K n r * gr K (n - r) 1) := by
          rw [coverPairs, mul_sum]
      _ ≤ ∑ r ∈ range n, 8 * q ^ ((r + 1) * (n + 1 - (r + 1))) := sum_le_sum hterm
      _ = 8 * ∑ r ∈ range n, q ^ ((r + 1) * (n + 1 - (r + 1))) := by rw [mul_sum]
      _ ≤ 8 * ∑ j ∈ range (n + 1 + 1), q ^ (j * (n + 1 - j)) := Nat.mul_le_mul_left _ hsub
      _ ≤ 8 * (4 * q ^ ((n + 1) * (n + 1) / 4)) :=
          Nat.mul_le_mul_left _ (sum_pow_mul_sub_le hq (n + 1))
  have hexp : 1 ≤ (n + 1) * (n + 1) / 4 := by
    have : 4 ≤ (n + 1) * (n + 1) := by nlinarith
    omega
  have e : q ^ ((n + 1) * (n + 1) / 4) = q * q ^ ((n + 1) * (n + 1) / 4 - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hexp]
  rw [e] at hsum
  have h32 : coverPairs K n ≤ 32 * q ^ ((n + 1) * (n + 1) / 4 - 1) := by
    refine Nat.le_of_mul_le_mul_left (c := q) ?_ (by omega)
    calc q * coverPairs K n ≤ 8 * (4 * (q * q ^ ((n + 1) * (n + 1) / 4 - 1))) := hsum
      _ = q * (32 * q ^ ((n + 1) * (n + 1) / 4 - 1)) := by ring
  omega

/-! ### Section 3.3 -/

namespace CountAux

/-- The fixed-dimension version of eq. (11):
`|Gr(n+2, j+1)| = |Gr(n+1, j+1)| + |Gr(n+1, j)| + (q^{n+1} - 1) |Gr(n, j)|`. -/
theorem gr_count (n j : ℕ) :
    gr K (n + 2) (j + 1) =
      gr K (n + 1) (j + 1) + gr K (n + 1) j + (q ^ (n + 1) - 1) * gr K n j := by
  have h1 : gr K (n + 2) (j + 1) = gr K (n + 1) (j + 1) + q ^ (n + 1 - j) * gr K (n + 1) j :=
    gr_succ_succ K (n + 1) j
  have h2 := gr_succ_left_mul K n j
  have hq := two_le_card K
  have hm : 1 ≤ q ^ (n + 1 - j) := Nat.one_le_pow _ _ (by omega)
  rw [h1]
  obtain ⟨t, ht⟩ : ∃ t, q ^ (n + 1 - j) = t + 1 := ⟨_, (Nat.sub_add_cancel hm).symm⟩
  rw [ht, Nat.add_sub_cancel] at h2
  rw [ht]
  linarith

end CountAux

/-- Equation (11): the Goldman–Rota recurrence with a cutoff. -/
theorem numLE_count (n k : ℕ) :
    numLE K (n + 2) (k + 1) =
      numLE K (n + 1) (k + 1) + numLE K (n + 1) k + (q ^ (n + 1) - 1) * numLE K n k := by
  simp only [numLE_eq_sum]
  rw [sum_range_succ' (fun j => gr K (n + 2) j), sum_range_succ' (fun j => gr K (n + 1) j)]
  simp only [gr_count, gr_zero_right, sum_add_distrib, mul_sum]
  ring

/-- Section 3.3: `M_q(n, k) - 2 M_q(n-1, k) ≥ 0`: at least half the entries go to the
transforms with cutoff `k - 1`. -/
theorem two_mul_numLE_le (n k : ℕ) : 2 * numLE K n (k + 1) ≤ numLE K (n + 1) (k + 1) := by
  have e : ∀ m, ∑ j ∈ range (k + 1 + 1), gr K m j =
      ∑ i ∈ range k, gr K m (i + 1 + 1) + gr K m (0 + 1) + 1 := by
    intro m
    rw [sum_range_succ', sum_range_succ', gr_zero_right]
  simp only [numLE_eq_sum]
  rw [e n, e (n + 1)]
  have hq := two_le_card K
  have h1 : ∑ i ∈ range k, 2 * gr K n (i + 1 + 1) ≤
      ∑ i ∈ range k, gr K (n + 1) (i + 1 + 1) := by
    refine sum_le_sum fun i _ => ?_
    have h := pow_mul_gr_le K n (i + 1 + 1)
    have h2 : 2 ≤ q ^ (i + 1 + 1) := hq.trans (Nat.le_self_pow (by omega) q)
    exact (Nat.mul_le_mul_right _ h2).trans h
  have h2 : gr K (n + 1) (0 + 1) = gr K n (0 + 1) + q ^ n := by
    rw [gr_succ_succ, gr_zero_right, Nat.sub_zero, mul_one]
  have h3 : gr K n 1 + 1 ≤ q ^ n := by
    have h := gr_one_mul K n
    have h4 : gr K n 1 ≤ gr K n 1 * (q - 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h5 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    omega
  rw [← mul_sum] at h1
  rw [h2]
  simp only [zero_add] at h3 ⊢
  omega

namespace CountAux

/-- `nk ≤ 2 log₂ |Gr(n, k)|` for `2k ≤ n` (from `|Gr(n, k)| ≥ q^{k(n-k)}`). -/
theorem mul_le_two_mul_log_gr {n k : ℕ} (hkn : 2 * k ≤ n) :
    n * k ≤ 2 * Nat.log 2 (gr K n k) := by
  have h1 : k * (n - k) ≤ Nat.log 2 (gr K n k) :=
    Nat.le_log_of_pow_le one_lt_two
      ((Nat.pow_le_pow_left (two_le_card K) _).trans (pow_le_gr K (by omega)))
  have h2 : n * k ≤ 2 * (k * (n - k)) := by
    obtain ⟨r, rfl⟩ : ∃ r, n = 2 * k + r := ⟨n - 2 * k, by omega⟩
    rw [show 2 * k + r - k = k + r by omega]
    nlinarith [Nat.zero_le (k * r)]
  omega

end CountAux

/-- `nk = O(log M_q(n, k))` (end of Section 3.3). -/
theorem mul_le_log_numLE {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    n * k ≤ 5 * Nat.log 2 (numLE K n k) := by
  rcases Nat.lt_or_ge n (2 * k) with h | h
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · obtain rfl : n = 1 := by omega
      obtain rfl : k = 1 := by omega
      have h1 : numLE K 1 1 = 2 := by
        rw [numLE_eq_sum]
        simp [sum_range_succ, gr_zero_right, gr_self]
      have h2 : 1 ≤ Nat.log 2 (numLE K 1 1) := by
        rw [h1]; exact Nat.le_log_of_pow_le one_lt_two (by norm_num)
      omega
    · have h1 : n * n / 4 ≤ Nat.log 2 (numLE K n k) := by
        apply Nat.le_log_of_pow_le one_lt_two
        calc 2 ^ (n * n / 4) ≤ q ^ (n * n / 4) := Nat.pow_le_pow_left (two_le_card K) _
          _ = q ^ (n / 2 * (n - n / 2)) := by rw [mul_self_div_four]
          _ ≤ gr K n (n / 2) := pow_le_gr K (Nat.div_le_self n 2)
          _ ≤ numLE K n k := gr_le_numLE K (by omega)
      have h2 := mul_self_le_five_mul_div_four hn
      have h3 : n * k ≤ n * n := Nat.mul_le_mul_left _ hkn
      omega
  · have h1 := mul_le_two_mul_log_gr K h
    have h2 : Nat.log 2 (gr K n k) ≤ Nat.log 2 (numLE K n k) :=
      Nat.log_mono_right (gr_le_numLE K le_rfl)
    omega

/-- `nk = O(log |Gr(n, k)|)` for `k ≤ n/2`. -/
theorem mul_le_log_gr {n k : ℕ} (hkn : 2 * k ≤ n) : n * k ≤ 2 * Nat.log 2 (gr K n k) :=
  mul_le_two_mul_log_gr K hkn

/-! ### Appendix B -/

/-- The budget `C n min(a, n-b) S + S`, `S = |Gr(n,a)| + |Gr(n,b)|`. -/
noncomputable def incidBound (C n a b : ℕ) : ℕ :=
  C * n * min a (n - b) * (gr K n a + gr K n b) + (gr K n a + gr K n b)

namespace CountAux

/-- Increasing below the middle: `|Gr(n, j)| ≤ |Gr(n, j+1)|` for `2j + 1 ≤ n`. -/
theorem gr_le_gr_succ {n j : ℕ} (h : 2 * j + 1 ≤ n) : gr K n j ≤ gr K n (j + 1) := by
  have h1 := gr_succ_right_mul K n j
  have hq := two_le_card K
  have h2 : q ^ (j + 1) ≤ q ^ (n - j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 1 < q ^ (j + 1) := Nat.one_lt_pow (by omega) (by omega)
  refine Nat.le_of_mul_le_mul_right (c := q ^ (j + 1) - 1) ?_ (by omega)
  rw [h1]
  exact Nat.mul_le_mul_left _ (by omega)

theorem gr_mono {n i j : ℕ} (hij : i ≤ j) (hj : 2 * j ≤ n) : gr K n i ≤ gr K n j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (gr_le_gr_succ K (by omega))

/-- Unimodality: `|Gr(n, a)| ≤ |Gr(n, b)|` for `a ≤ b ≤ n - a`. -/
theorem gr_le_gr {n a b : ℕ} (hab : a ≤ b) (hb : a + b ≤ n) : gr K n a ≤ gr K n b := by
  rcases Nat.lt_or_ge n (2 * b) with h | h
  · rw [← gr_symm K (show b ≤ n by omega)]
    exact gr_mono K (by omega) (by omega)
  · exact gr_mono K hab h

/-- `|Gr(n, a)| = |Gr(n-1, a)| + |Gr(n-1, a-1)| + (q^{n-1} - 1) |Gr(n-2, a-1)|` for
`1 ≤ a`, `2 ≤ n`. -/
theorem gr_count' {n a : ℕ} (ha : 1 ≤ a) (hn : 2 ≤ n) :
    gr K n a =
      gr K (n - 1) a + gr K (n - 1) (a - 1) + (q ^ (n - 1) - 1) * gr K (n - 2) (a - 1) := by
  have := gr_count K (n - 2) (a - 1)
  rwa [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega,
    show a - 1 + 1 = a by omega] at this

/-- `q^j |Gr(n-1, j)| ≤ |Gr(n, j)|` for `1 ≤ n`. -/
theorem pow_mul_gr_pred_le {n : ℕ} (j : ℕ) (hn : 1 ≤ n) :
    q ^ j * gr K (n - 1) j ≤ gr K n j := by
  have := pow_mul_gr_le K (n - 1) j
  rwa [show n - 1 + 1 = n by omega] at this

/-- The dual ratio bound `q^{n-j} |Gr(n-1, j-1)| ≤ |Gr(n, j)|` for `1 ≤ j ≤ n`. -/
theorem pow_mul_gr_pred_pred_le {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    q ^ (n - j) * gr K (n - 1) (j - 1) ≤ gr K n j := by
  have h1 := pow_mul_gr_le K (n - 1) (n - j)
  have h2 := gr_symm K (show j - 1 ≤ n - 1 by omega)
  have h3 := gr_symm K hjn
  rw [show n - 1 - (j - 1) = n - j by omega] at h2
  rw [show n - 1 + 1 = n by omega, h2, h3] at h1
  exact h1

end CountAux

/-- Equation (28): the recursive calls of an interior call `0 < a < b < n` have total budget
`∑ min(a', c') S'` at least `S/4` below `min(a, c) S` (`c = n - b`). -/
theorem slack {n a b : ℕ} (ha : 0 < a) (hab : a < b) (hbn : b < n) :
    4 * (min a (n - 1 - b) * (gr K (n - 1) a + gr K (n - 1) b) +
        min a (n - b) * (gr K (n - 1) a + gr K (n - 1) (b - 1)) +
        min (a - 1) (n - b) * (gr K (n - 1) (a - 1) + gr K (n - 1) (b - 1)) +
        (q ^ (n - 1) - 1) * (min (a - 1) (n - 1 - b) * (gr K (n - 2) (a - 1) + gr K (n - 2) (b - 1))))
      + (gr K n a + gr K n b) ≤ 4 * (min a (n - b) * (gr K n a + gr K n b)) := by
  have hq := two_le_card K
  have hA := gr_count' K (n := n) (a := a) (by omega) (by omega)
  have hB := gr_count' K (n := n) (a := b) (by omega) (by omega)
  have hx := pow_mul_gr_pred_le K (n := n) a (by omega)
  have hy := pow_mul_gr_pred_le K (n := n) b (by omega)
  have hz := pow_mul_gr_pred_pred_le K (n := n) (j := b) (by omega) (by omega)
  have hw := pow_mul_gr_pred_pred_le K (n := n) (j := a) (by omega) (by omega)
  rcases lt_trichotomy a (n - b) with h | h | h
  · have hAB : gr K n a ≤ gr K n b := gr_le_gr K hab.le (by omega)
    have core := slack_core hq hx hy hz (by omega : a + 1 ≤ b) (by omega : a + 1 ≤ n - b) hAB
    exact slack_arith_lt (d := a - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      hA hB core
  · have hz' : q ^ a * gr K (n - 1) (b - 1) ≤ gr K n b := by rw [h]; exact hz
    have core := slack_core_eq hq (m := a) (J := gr K (n - 1) a + gr K (n - 1) (b - 1))
      (S := gr K n a + gr K n b) (by rw [mul_add]; exact Nat.add_le_add hx hz')
    exact slack_arith_eq (d := a - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      hA hB core
  · have hBA : gr K n b ≤ gr K n a := by
      rw [← gr_symm K (show b ≤ n by omega)]
      exact gr_le_gr K (by omega) (by omega)
    have core := slack_core hq hz hw hx (by omega : n - b + 1 ≤ n - a)
      (by omega : n - b + 1 ≤ a) hBA
    exact slack_arith_gt (e := n - b - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      hA hB core

/-- The induction step for the incidence budget (Appendix B). -/
theorem incid_budget_step (C₁ : ℕ) {n a b : ℕ} (ha : 0 < a) (hab : a < b) (hbn : b < n) :
    incidBound K (4 * C₁ + 4) (n - 1) a b + incidBound K (4 * C₁ + 4) (n - 1) a (b - 1) +
        incidBound K (4 * C₁ + 4) (n - 1) (a - 1) (b - 1) +
        (q ^ (n - 1) - 1) * incidBound K (4 * C₁ + 4) (n - 2) (a - 1) (b - 1) +
        C₁ * n * (gr K n a + gr K n b) ≤
      incidBound K (4 * C₁ + 4) n a b := by
  have hs := slack K ha hab hbn
  have hA := gr_count' K (n := n) (a := a) (by omega) (by omega)
  have hB := gr_count' K (n := n) (a := b) (by omega) (by omega)
  have hJ : gr K (n - 1) a + gr K (n - 1) (b - 1) ≤ gr K n a + gr K n b := by
    have h1 : gr K (n - 1) a ≤ gr K n a := by rw [hA]; omega
    have h2 : gr K (n - 1) (b - 1) ≤ gr K n b := by rw [hB]; omega
    omega
  simp only [incidBound]
  rw [show n - 1 - (b - 1) = n - b by omega, show n - 2 - (b - 1) = n - 1 - b by omega]
  exact budget_arith (by omega) (by omega) (by omega) (by rw [hA, hB]; ring) hJ hs

theorem two_le_gr_add_gr {n a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) : 2 ≤ gr K n a + gr K n b := by
  have h1 := gr_pos K (hab.trans hbn)
  have h2 := gr_pos K hbn
  omega

/-- `n min(a, n-b) ≤ 2 log_q S`, hence the budget is `O(S log S)`. -/
theorem incidBound_le (C : ℕ) {n a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    incidBound K C n a b ≤
      (2 * C + 1) * (gr K n a + gr K n b) * Nat.log 2 (gr K n a + gr K n b) := by
  have hS := two_le_gr_add_gr K hab hbn
  have hq := two_le_card K
  have hlogA : a * (n - a) ≤ Nat.log 2 (gr K n a + gr K n b) :=
    Nat.le_log_of_pow_le one_lt_two ((Nat.pow_le_pow_left hq _).trans
      ((pow_le_gr K (hab.trans hbn)).trans (Nat.le_add_right _ _)))
  have hlogB : b * (n - b) ≤ Nat.log 2 (gr K n a + gr K n b) :=
    Nat.le_log_of_pow_le one_lt_two ((Nat.pow_le_pow_left hq _).trans
      ((pow_le_gr K hbn).trans (Nat.le_add_left _ _)))
  have hL1 : 1 ≤ Nat.log 2 (gr K n a + gr K n b) :=
    Nat.le_log_of_pow_le one_lt_two (by simpa using hS)
  set S := gr K n a + gr K n b
  set L := Nat.log 2 S
  have hkey : n * min a (n - b) ≤ 2 * L := by
    rcases le_total a (n - b) with h | h
    · rw [min_eq_left h]
      obtain ⟨c, hc⟩ : ∃ c, n - b = c := ⟨_, rfl⟩
      have hn : n = b + c := by omega
      rw [hc] at h hlogB
      rw [hn]
      have h1 : b * a ≤ b * c := Nat.mul_le_mul_left b h
      have h2 : a * c ≤ b * c := Nat.mul_le_mul_right c hab
      nlinarith
    · rw [min_eq_right h]
      obtain ⟨t, ht⟩ : ∃ t, n - a = t := ⟨_, rfl⟩
      have hn : n = a + t := by omega
      have hct : n - b ≤ t := by omega
      rw [ht] at hlogA
      obtain ⟨c, hc⟩ : ∃ c, n - b = c := ⟨_, rfl⟩
      rw [hc] at h hct ⊢
      rw [hn]
      have h1 : a * c ≤ a * t := Nat.mul_le_mul_left a hct
      have h2 : t * c ≤ t * a := Nat.mul_le_mul_left t h
      nlinarith
  have h1 : C * n * min a (n - b) * S ≤ C * (2 * L) * S := by
    calc C * n * min a (n - b) * S = C * (n * min a (n - b)) * S := by ring
      _ ≤ C * (2 * L) * S := by gcongr
  have h2 : S ≤ S * L := Nat.le_mul_of_pos_right S hL1
  unfold incidBound
  calc C * n * min a (n - b) * S + S ≤ C * (2 * L) * S + S * L := Nat.add_le_add h1 h2
    _ = (2 * C + 1) * S * L := by ring

end SubspaceConvolution
