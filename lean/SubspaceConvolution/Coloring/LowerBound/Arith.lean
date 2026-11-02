/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Complexity

/-!
# The exponent arithmetic of Theorem C.1

With `s = √(log₂ k)` and `d = ⌈s⌉` (the least `d` with `k ≤ 2^{d²}`), a layout of width
`r ≤ 2d + 12 ≤ 2s + 14` gives, by convexity of `b(t) = t²/4 - 17 t`,

  `2^{b(r)} ≤ max {1, 2^{b(2s+14)}} = max {1, k · 2^{-20 s - 189}}`

(paper, proof of Theorem C.1).  `two_rpow_b_le` is this inequality; `d_le_sqrt_log` is
`d ≤ s + 1`.
-/

open Real

namespace SubspaceConvolution

/-- `d ≤ √(log₂ k) + 1` for the least `d` with `k ≤ 2^{d²}`. -/
theorem d_le_sqrt_log {k d : ℕ} (hk : 1 ≤ k) (hmin : ∀ d' < d, 2 ^ (d' * d') < k) :
    (d : ℝ) ≤ √(logb 2 k) + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero]
    positivity
  · have h := hmin (d - 1) (by omega)
    -- `(d-1)² < log₂ k`
    have hlog : (((d - 1 : ℕ) : ℝ)) ^ 2 < logb 2 k := by
      have h' : ((2 : ℝ) ^ ((d - 1) * (d - 1) : ℕ)) < k := by exact_mod_cast h
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by exact_mod_cast hk)]
      rw [show ((((d - 1 : ℕ) : ℝ)) ^ 2) = (((d - 1) * (d - 1) : ℕ) : ℝ) by push_cast; ring]
      rw [Real.rpow_natCast]
      exact h'
    have hsq : ((d - 1 : ℕ) : ℝ) < √(logb 2 k) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg (d - 1))]
      exact Real.sqrt_lt_sqrt (by positivity) hlog
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    linarith

/-- **The exponent bound of Theorem C.1**: for `r ≤ 2d + 12` with `d ≤ √(log₂ k) + 1`,
`2^{r²/4 - 17 r} ≤ max {1, k · 2^{-20 √(log₂ k) - 189}}`. -/
theorem two_rpow_b_le {k : ℕ} (hk : 1 ≤ k) {d r : ℕ} (hd : (d : ℝ) ≤ √(logb 2 k) + 1)
    (hr : r ≤ 2 * d + 12) :
    (2 : ℝ) ^ ((r : ℝ) ^ 2 / 4 - 17 * r) ≤ max 1 (k * (2 : ℝ) ^ (-20 * √(logb 2 k) - 189)) := by
  set s := √(logb 2 k) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlog0 : 0 ≤ logb 2 (k : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hk)
  have hss : s ^ 2 = logb 2 k := Real.sq_sqrt hlog0
  have hrR : (r : ℝ) ≤ 2 * s + 14 := by
    have : (r : ℝ) ≤ 2 * d + 12 := by exact_mod_cast hr
    linarith
  have hb := quad_le_max (Nat.cast_nonneg r) hrR
  rw [quad_at, hss] at hb
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc (2 : ℝ) ^ ((r : ℝ) ^ 2 / 4 - 17 * r)
      ≤ (2 : ℝ) ^ (max 0 (logb 2 k - 20 * s - 189)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hb
    _ = max 1 (k * (2 : ℝ) ^ (-20 * s - 189)) := by
        rcases le_total 0 (logb 2 k - 20 * s - 189) with h | h
        · rw [max_eq_right h, max_eq_right]
          · rw [show logb 2 (k : ℝ) - 20 * s - 189 = logb 2 k + (-20 * s - 189) by ring,
              Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hk']
          · rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by simp, ← Real.rpow_logb (b := 2)
              (by norm_num) (by norm_num) hk', ← Real.rpow_add (by norm_num)]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        · rw [max_eq_left h, max_eq_left]
          · simp
          · rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by simp, ← Real.rpow_logb (b := 2)
              (by norm_num) (by norm_num) hk', ← Real.rpow_add (by norm_num)]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- `k · 2^{-20 √(log₂ k) - 189} = o(k)`: the ratio `2^{-20 √(log₂ k) - 189}` tends to `0`. -/
theorem tendsto_ratio_zero :
    Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ (-20 * √(logb 2 k) - 189)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun k : ℕ => √(logb 2 (k : ℝ))) Filter.atTop Filter.atTop := by
    have := (Real.tendsto_logb_atTop (b := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact Real.tendsto_sqrt_atTop.comp this
  have h2 : Filter.Tendsto (fun k : ℕ => -20 * √(logb 2 (k : ℝ)) - 189) Filter.atTop
      Filter.atBot := by
    apply Filter.tendsto_atBot_add_const_right
    exact Filter.Tendsto.const_mul_atTop_of_neg (by norm_num) h1
  exact (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp h2

end SubspaceConvolution
