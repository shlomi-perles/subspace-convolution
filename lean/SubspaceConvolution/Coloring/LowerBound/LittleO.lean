/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Arith

/-!
# One-sided little-o bounds

For running-time exponents we use one-sided little-o statements:

* `SubLin e` — `e(n) ≤ η n` eventually, for every `η > 0` (i.e. `e(n) ≤ o(n)`);
* `SubQuad f` — `f(r) ≤ η r²` eventually, for every `η > 0` (i.e. `f(r) ≤ o(r²)`).

`SubLin.sup_of_subQuad` is the "sup trick": if `f ≤ o(r²)` and `B(n)² = O(n)` then
`max_{r ≤ B(n)} f(r) ≤ o(n)`.
-/

open Filter

namespace SubspaceConvolution

/-- `e(n) ≤ o(n)`. -/
def SubLin (e : ℕ → ℝ) : Prop := ∀ η > 0, ∀ᶠ n in atTop, e n ≤ η * n

/-- `f(r) ≤ o(r²)`. -/
def SubQuad (f : ℕ → ℝ) : Prop := ∀ η > 0, ∀ᶠ r in atTop, f r ≤ η * (r : ℝ) ^ 2

namespace SubLin

theorem mono {e e' : ℕ → ℝ} (h : SubLin e') (hle : ∀ n, e n ≤ e' n) : SubLin e := fun η hη =>
  (h η hη).mono fun n hn => (hle n).trans hn

theorem add {e e' : ℕ → ℝ} (h : SubLin e) (h' : SubLin e') : SubLin (fun n => e n + e' n) :=
  fun η hη => ((h (η / 2) (by positivity)).and (h' (η / 2) (by positivity))).mono
    fun n ⟨h1, h2⟩ => by linarith

theorem max {e e' : ℕ → ℝ} (h : SubLin e) (h' : SubLin e') : SubLin (fun n => max (e n) (e' n)) :=
  fun η hη => ((h η hη).and (h' η hη)).mono fun _ ⟨h1, h2⟩ => max_le h1 h2

theorem const (c : ℝ) : SubLin (fun _ => c) := fun η hη => by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (c / η)
  refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
  have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have := (div_lt_iff₀ hη).1 hn₀
  nlinarith

theorem const_mul {e : ℕ → ℝ} (h : SubLin e) {c : ℝ} (hc : 0 ≤ c) : SubLin (fun n => c * e n) :=
  fun η hη => by
    rcases hc.eq_or_lt with rfl | hc
    · refine eventually_atTop.2 ⟨0, fun n _ => ?_⟩
      simp only [zero_mul]
      positivity
    · exact (h (η / c) (by positivity)).mono fun n hn => by
        calc c * e n ≤ c * (η / c * n) := by gcongr
          _ = η * n := by field_simp

/-- `√n ≤ o(n)`. -/
theorem sqrt : SubLin (fun n => Real.sqrt n) := fun η hη => by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / η ^ 2)
  refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 1 / η ^ 2 < n := lt_of_lt_of_le hn₀ hn'
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn1
  -- `√n ≤ η n` iff `1 ≤ η² n`
  have h1 : 1 ≤ η ^ 2 * n := by
    rw [div_lt_iff₀ (by positivity)] at hn1
    linarith
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have h2 : (η * Real.sqrt n) ^ 2 = η ^ 2 * n := by rw [mul_pow, Real.sq_sqrt hnpos.le]
  have hx : 0 < η * Real.sqrt n := by positivity
  have h3 : 1 ≤ η * Real.sqrt n := by
    by_contra hlt
    push Not at hlt
    nlinarith
  show Real.sqrt n ≤ η * n
  calc Real.sqrt n = Real.sqrt n * 1 := (mul_one _).symm
    _ ≤ Real.sqrt n * (η * Real.sqrt n) := by gcongr
    _ = η * (Real.sqrt n * Real.sqrt n) := by ring
    _ = η * n := by rw [Real.mul_self_sqrt hnpos.le]

end SubLin

/-- **The sup trick.**  If `f(r) ≤ o(r²)` and `B(n)² ≤ a (n+1)`, then
`max_{r ≤ B(n)} f(r) ≤ o(n)`. -/
theorem SubLin.sup_of_subQuad {f : ℕ → ℝ} (hf : SubQuad f) (B : ℕ → ℕ) (a : ℝ) (ha : 0 < a)
    (hB : ∀ n, ((B n : ℕ) : ℝ) ^ 2 ≤ a * (n + 1)) :
    SubLin (fun n => (Finset.range (B n + 1)).sup' (by simp) f) := by
  intro η hη
  -- `f(r) ≤ η/(4a) r²` for `r ≥ R₀`
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hf (η / (4 * a)) (by positivity))
  -- small `r` contribute at most `K₀`
  set K₀ : ℝ := (Finset.range (R₀ + 1)).sup' (by simp) f
  have hK := (SubLin.const (|K₀|)) (η / 2) (by positivity)
  have hlin := (SubLin.const (η / 2)) (η / 2) (by positivity)
  refine (hK.and hlin).mono fun n ⟨hKn, hlinn⟩ => ?_
  apply Finset.sup'_le
  intro r hr
  have hrB : r ≤ B n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  by_cases hrR : r ≤ R₀
  · have : f r ≤ K₀ := Finset.le_sup' f (Finset.mem_range.2 (Nat.lt_succ_of_le hrR))
    have : K₀ ≤ |K₀| := le_abs_self K₀
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · have h1 := hR₀ r (by omega)
    have h2 : (r : ℝ) ^ 2 ≤ a * (n + 1) :=
      le_trans (by gcongr) (hB n)
    calc f r ≤ η / (4 * a) * (r : ℝ) ^ 2 := h1
      _ ≤ η / (4 * a) * (a * (n + 1)) := by gcongr
      _ = η / 4 * n + η / 4 := by field_simp
      _ ≤ η * n := by nlinarith

theorem floor_add_floor_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌊x⌋₊ + ⌊y⌋₊ ≤ ⌊x + y⌋₊ := by
  apply Nat.le_floor
  push_cast
  exact add_le_add (Nat.floor_le hx) (Nat.floor_le hy)

end SubspaceConvolution
