/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Common

/-!
# An abstract cost model, running-time transfers, and the asymptotic arithmetic

The paper's lower bounds are relationships between running times ("The reductions give quantitative
implications without assuming ETH … ETH is used only to exclude the resulting SAT running times",
Section 1.2).  We formalize them over an *abstract cost model*: a predicate `M.Runs f t`, read
"some algorithm computes `f` within `t x` steps on input `x`", assumed only to be monotone in the
time bound and closed under composition (time adds up).  Every reasonable machine model (Turing
machines, RAMs) is such a model.  Nothing else about `M` is assumed, so all results hold for every
such model.

* `CostModel`, `CostModel.Runs.reduce` — the transfer through a reduction.
* `exists_tendsto_sup_mul` — the "sup trick" turning `2^{ε(r) r²}` with `ε → 0` and `r ≤ B(n)`,
  `B(n)² = O(n)`, into `2^{ε'(n) (n+1)}` with `ε' → 0`.
* `quad_le_max` — convexity of `t²/4 - 17 t` (used in Theorem 8).
-/

open Filter Topology

namespace SubspaceConvolution

/-- An abstract cost model: `Runs f t` means that some algorithm computes `f` within time
`t x` on every input `x`. -/
structure CostModel where
  /-- `Runs f t`: `f` is computable within time `t`. -/
  Runs : {α β : Type} → (α → β) → (α → ℕ) → Prop
  /-- running-time bounds can be weakened -/
  mono : ∀ {α β : Type} {f : α → β} {t t' : α → ℕ}, Runs f t → (∀ x, t x ≤ t' x) → Runs f t'
  /-- composition: first compute `f`, then `g` on its output -/
  comp : ∀ {α β γ : Type} {f : α → β} {g : β → γ} {t : α → ℕ} {s : β → ℕ},
    Runs f t → Runs g s → Runs (g ∘ f) (fun x => t x + s (f x))

namespace CostModel

variable (M : CostModel)

/-- **Transfer through a reduction.**  If the target problem `P` is computable within `T`, the
reduction `red` within `R`, and the source problem `Q` factors as `Q = P ∘ red`, then `Q` is
computable within `R + T ∘ red`. -/
theorem Runs.reduce {α β γ : Type} {P : β → γ} {Q : α → γ} {red : α → β} {T : β → ℕ}
    {R : α → ℕ} (hP : M.Runs P T) (hred : M.Runs red R) (hQ : ∀ x, Q x = P (red x)) :
    M.Runs Q (fun x => R x + T (red x)) := by
  have : Q = P ∘ red := funext hQ
  rw [this]
  exact M.comp hred hP

/-- The transfer with a weakened time bound. -/
theorem Runs.reduce_le {α β γ : Type} {P : β → γ} {Q : α → γ} {red : α → β} {T : β → ℕ}
    {R : α → ℕ} {S : α → ℕ} (hP : M.Runs P T) (hred : M.Runs red R)
    (hQ : ∀ x, Q x = P (red x)) (hS : ∀ x, R x + T (red x) ≤ S x) : M.Runs Q S :=
  M.mono (Runs.reduce M hP hred hQ) hS

end CostModel

/-! ### The sup trick -/

/-- If `ε(r) → 0` and `B(n)² ≤ a (n+1)`, then `max_{r ≤ B(n)} ε(r) r² = ε'(n) (n+1)` with
`ε'(n) → 0`. -/
theorem exists_tendsto_sup_mul {ε : ℕ → ℝ} (hε0 : ∀ r, 0 ≤ ε r)
    (hε : Tendsto ε atTop (𝓝 0)) (B : ℕ → ℕ) (a : ℝ) (ha : 0 < a)
    (hB : ∀ n, ((B n : ℕ) : ℝ) ^ 2 ≤ a * (n + 1)) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧ (∀ n, 0 ≤ ε' n) ∧
      ∀ n r, r ≤ B n → ε r * (r : ℝ) ^ 2 ≤ ε' n * (n + 1) := by
  -- the maximum over `r ≤ B n`
  let S : ℕ → ℝ := fun n =>
    (Finset.range (B n + 1)).sup' (by simp) fun r => ε r * (r : ℝ) ^ 2
  refine ⟨fun n => S n / (n + 1), ?_, fun n => ?_, fun n r hr => ?_⟩
  · rw [Metric.tendsto_atTop]
    intro η hη
    -- `ε r ≤ η / (2a)` for `r ≥ R₀`
    obtain ⟨R₀, hR₀⟩ := (Metric.tendsto_atTop.1 hε) (η / (2 * a)) (by positivity)
    -- the finitely many small `r` contribute at most `K₀`
    set K₀ : ℝ := (Finset.range (R₀ + 1)).sup' (by simp) fun r => ε r * (r : ℝ) ^ 2
    have hK₀ : 0 ≤ K₀ := le_trans (by simp) (Finset.le_sup' (fun r => ε r * (r : ℝ) ^ 2)
      (Finset.mem_range.2 (Nat.succ_pos R₀)))
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * K₀ / η)
    refine ⟨n₀, fun n hn => ?_⟩
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hSn : S n ≤ K₀ + η / (2 * a) * (a * (n + 1)) := by
      apply Finset.sup'_le
      intro r hr
      by_cases hrR : r ≤ R₀
      · have : ε r * (r : ℝ) ^ 2 ≤ K₀ :=
          Finset.le_sup' (fun r => ε r * (r : ℝ) ^ 2) (Finset.mem_range.2 (Nat.lt_succ_of_le hrR))
        have : 0 ≤ η / (2 * a) * (a * (n + 1)) := by positivity
        linarith
      · have hεr : ε r ≤ η / (2 * a) := by
          have := hR₀ r (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (hε0 r)] at this
          exact this.le
        have hrB : (r : ℝ) ^ 2 ≤ a * (n + 1) := by
          have : r ≤ B n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
          calc (r : ℝ) ^ 2 ≤ (B n : ℝ) ^ 2 := by gcongr
            _ ≤ a * (n + 1) := hB n
        calc ε r * (r : ℝ) ^ 2 ≤ η / (2 * a) * (a * (n + 1)) := by
              apply mul_le_mul hεr hrB (by positivity) (by positivity)
          _ ≤ K₀ + η / (2 * a) * (a * (n + 1)) := by linarith
    have hS0 : 0 ≤ S n := le_trans (by simp) (Finset.le_sup' (fun r => ε r * (r : ℝ) ^ 2)
      (Finset.mem_range.2 (Nat.succ_pos (B n))))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hS0 hn1.le), div_lt_iff₀ hn1]
    have hnn : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have hK : K₀ < η / 2 * (n + 1) := by
      have := (div_lt_iff₀ hη).1 hn₀
      nlinarith
    calc S n ≤ K₀ + η / (2 * a) * (a * (n + 1)) := hSn
      _ = K₀ + η / 2 * (n + 1) := by field_simp
      _ < η / 2 * (n + 1) + η / 2 * (n + 1) := by linarith
      _ = η * (n + 1) := by ring
  · have hS0 : 0 ≤ S n := le_trans (by simp) (Finset.le_sup' (fun r => ε r * (r : ℝ) ^ 2)
      (Finset.mem_range.2 (Nat.succ_pos (B n))))
    positivity
  · have hn1 : (0 : ℝ) < n + 1 := by positivity
    rw [div_mul_cancel₀ _ hn1.ne']
    exact Finset.le_sup' (fun r => ε r * (r : ℝ) ^ 2) (Finset.mem_range.2 (Nat.lt_succ_of_le hr))

/-! ### Convexity of `b(t) = t²/4 - 17t` -/

/-- For `0 ≤ t ≤ R`: `t²/4 - 17 t ≤ max 0 (R²/4 - 17 R)` (convexity of `b`, Theorem 8). -/
theorem quad_le_max {t R : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    t ^ 2 / 4 - 17 * t ≤ max 0 (R ^ 2 / 4 - 17 * R) := by
  by_cases h : t ≤ 68
  · exact le_trans (by nlinarith) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    nlinarith

/-- `b(2s + 14) = s² - 20 s - 189`. -/
theorem quad_at (s : ℝ) : (2 * s + 14) ^ 2 / 4 - 17 * (2 * s + 14) = s ^ 2 - 20 * s - 189 := by
  ring

end SubspaceConvolution
