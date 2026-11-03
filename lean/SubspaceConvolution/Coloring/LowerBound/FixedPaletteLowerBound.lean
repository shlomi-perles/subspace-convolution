/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Main
import SubspaceConvolution.Coloring.LowerBound.LittleO

/-!
# Theorems 9 and 10: fixed-palette decision and counting lower bounds

For a 3-CNF formula `φ` with `n` variables and `m` clauses, put `k = max(1, ⌈√n⌉)` (`side n`),
pad `φ` onto the `k × k` grid (`CNF.toGrid`), build the graph `G_φ` of Appendix H, and for
`c = t + 3` colors add a universal `t`-clique placed first in the layout.

* `reduction_spec` — the unconditional content of Theorems 9/10 (exact vertex count, layout
  width `≤ 2k + 19 + t`, exact number of `c`-colorings
  `= c!/3! · 6 · 2^{2k+3m} · 16^m · 2^{k²-n} · #SAT(φ)`, and `c`-colorability ⟺ satisfiability),
  plus the caterpillar rank-decomposition of the same width.
* `fixed_palette_lower_bound` — **Theorem 9** in an abstract cost model `M`: if `M` satisfies
  ETH (no `2^{o(n)} poly(m)` algorithm for 3-SAT) and the reduction is computable within
  `2^{a k} (m+2)^{C₀}`, then for every fixed `c ≥ 3` no algorithm decides `c`-colorability of
  graphs supplied with a linear layout of width `r` within `2^{o(r²)} (N+2)^{O(1)}`.
* `fixed_palette_counting_lower_bound` — **Theorem 10**: the same for exact counting of proper
  `c`-colorings under #ETH (no `2^{o(n)} poly(m)` algorithm counting satisfying assignments),
  given that dividing by the explicitly known factor costs at most `2^{a k} (m+2)^{C₀}`.
-/

open Real Filter

namespace SubspaceConvolution.FixedPalette

/-! ### The grid side `k = max(1, ⌈√n⌉)` -/

theorem exists_side (n : ℕ) : ∃ k, 1 ≤ k ∧ n ≤ k * k := ⟨n + 1, by omega, by nlinarith⟩

/-- The least `k ≥ 1` with `n ≤ k²`. -/
def side (n : ℕ) : ℕ := Nat.find (exists_side n)

theorem one_le_side (n : ℕ) : 1 ≤ side n := (Nat.find_spec (exists_side n)).1

theorem le_side_sq (n : ℕ) : n ≤ side n * side n := (Nat.find_spec (exists_side n)).2

theorem side_le_sqrt (n : ℕ) : (side n : ℝ) ≤ √n + 1 := by
  set k₀ := max 1 ⌈√(n : ℝ)⌉₊ with hk₀
  have hk₀sq : n ≤ k₀ * k₀ := by
    have h1 : √(n : ℝ) ≤ (⌈√(n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (n : ℝ) ≤ (k₀ : ℝ) * k₀ := by
      have : (⌈√(n : ℝ)⌉₊ : ℝ) ≤ k₀ := by exact_mod_cast le_max_right _ _
      have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
      nlinarith [Real.sqrt_nonneg (n : ℝ)]
    exact_mod_cast h2
  have hle : side n ≤ k₀ := Nat.find_min' (exists_side n) ⟨le_max_left _ _, hk₀sq⟩
  have hk₀le : (k₀ : ℝ) ≤ √n + 1 := by
    rcases le_total 1 ⌈√(n : ℝ)⌉₊ with h | h
    · rw [hk₀, max_eq_right h]
      exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
    · rw [hk₀, max_eq_left h]
      have := Real.sqrt_nonneg (n : ℝ)
      push_cast
      linarith
  exact (by exact_mod_cast hle : (side n : ℝ) ≤ k₀).trans hk₀le

/-! ### The reduction and its properties -/

/-- The grid formula of `φ`. -/
def grid {n : ℕ} (φ : CNF n) : GridCNF (side n) := φ.toGrid (side n) (le_side_sq n)

/-- The reduction graph for `t + 3` colors. -/
abbrev redGraph (t : ℕ) {n : ℕ} (φ : CNF n) := joinClique (graph (grid φ)) t

/-- The supplied linear layout. -/
abbrev redLayout (t : ℕ) {n : ℕ} (φ : CNF n) := joinCliqueLayout (layout (grid φ)) t

/-- **Theorems 9/10, unconditional part.** -/
theorem reduction_spec (t : ℕ) {n : ℕ} (φ : CNF n) :
    Fintype.card (Fin t ⊕ Vtx (side n) (grid φ).m) =
        t + (3 + (2 * side n + 3 * (grid φ).m) * (2 ^ (side n + 1) + 1) + 20 * (grid φ).m) ∧
      (redLayout t φ).width (redGraph t φ) ≤ 2 * side n + 19 + t ∧
      Fintype.card ((redGraph t φ).Coloring (Fin (t + 3))) =
        (t + 3).descFactorial t * (6 * 2 ^ (2 * side n + 3 * (grid φ).m) * 16 ^ (grid φ).m *
          (2 ^ (side n * side n - n) * φ.numSat)) ∧
      ((redGraph t φ).Colorable (t + 3) ↔ ∃ β, φ.Satisfies β) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_fin, card_vtx]
  · exact (width_joinCliqueLayout (graph (grid φ)) (layout (grid φ)) t).trans
      (by have := layout_width (grid φ); omega)
  · rw [redGraph, card_coloring_joinClique, card_coloring (one_le_side n), grid,
      numSat_toGrid]
  · rw [redGraph, colorable_joinClique_iff, colorable_iff (one_le_side n), grid,
      satisfiable_toGrid_iff]

/-! ### Problems, the reduction, and the transfers -/

open Classical in
/-- Deciding satisfiability of 3-CNF formulas (with their number of variables). -/
noncomputable def satDec : (Σ n, CNF n) → Bool := fun φ => decide (∃ β, φ.2.Satisfies β)

/-- Counting satisfying assignments. -/
noncomputable def satCount : (Σ n, CNF n) → ℕ := fun φ => φ.2.numSat

open Classical in
/-- Deciding `c`-colorability of a graph supplied with a linear layout. -/
noncomputable def colorDec (c : ℕ) : LayoutGraph → Bool := fun I => decide (I.G.Colorable c)

/-- Counting proper `c`-colorings of a graph supplied with a linear layout. -/
noncomputable def colorCount (c : ℕ) : LayoutGraph → ℕ :=
  fun I => Fintype.card (I.G.Coloring (Fin c))

/-- The reduction of Appendix H for `t + 3` colors. -/
noncomputable def red (t : ℕ) : (Σ n, CNF n) → LayoutGraph :=
  fun φ => LayoutGraph.ofGraph (redGraph t φ.2) (redLayout t φ.2)

/-- The known factor of the counting identity. -/
def factor (t : ℕ) (φ : Σ n, CNF n) : ℕ :=
  (t + 3).descFactorial t * (6 * 2 ^ (2 * side φ.1 + 3 * φ.2.m) * 16 ^ φ.2.m *
    2 ^ (side φ.1 * side φ.1 - φ.1))

theorem satDec_eq (t : ℕ) (φ : Σ n, CNF n) : satDec φ = colorDec (t + 3) (red t φ) := by
  unfold satDec colorDec red
  rw [decide_eq_decide, LayoutGraph.colorable_ofGraph_iff, (reduction_spec t φ.2).2.2.2]

theorem colorCount_eq (t : ℕ) (φ : Σ n, CNF n) :
    colorCount (t + 3) (red t φ) = factor t φ * satCount φ := by
  unfold colorCount red factor satCount
  rw [LayoutGraph.card_coloring_ofGraph, (reduction_spec t φ.2).2.2.1]
  have hm : (grid φ.2).m = φ.2.m := rfl
  rw [hm]
  ring

theorem red_width (t : ℕ) (φ : Σ n, CNF n) : (red t φ).width ≤ 2 * side φ.1 + 19 + t := by
  unfold red
  rw [LayoutGraph.width_ofGraph]
  exact (reduction_spec t φ.2).2.1

theorem red_N (t : ℕ) (φ : Σ n, CNF n) :
    (red t φ).N + 2 ≤ 2 ^ (2 * side φ.1 + t + 8) * (φ.2.m + 2) := by
  have hN : (red t φ).N = Fintype.card (Fin t ⊕ Vtx (side φ.1) (grid φ.2).m) := rfl
  rw [hN, (reduction_spec t φ.2).1]
  set k := side φ.1
  set m := (grid φ.2).m
  have hm : m = φ.2.m := rfl
  rw [← hm]
  have hk : 1 ≤ k := one_le_side _
  have h1 : 2 * k + 3 * m ≤ 2 ^ (k + 1) * (m + 1) := by
    have : 2 * k ≤ 2 ^ (k + 1) := by
      have := Nat.lt_two_pow_self (n := k)
      rw [pow_succ]
      omega
    have h4 : 4 ≤ 2 ^ (k + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have h2 : 2 ^ (k + 1) + 1 ≤ 2 ^ (k + 2) := by
    rw [pow_succ 2 (k + 1)]
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega
  have h3 : t + 26 ≤ 2 ^ (t + 5) := by
    have := Nat.lt_two_pow_self (n := t + 5)
    have h32 : 32 ≤ 2 ^ (t + 5) := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (t + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (t + 5) = 2 ^ t * 32 := by rw [pow_add]; norm_num
    have ht : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
    nlinarith
  have hprod : (2 * k + 3 * m) * (2 ^ (k + 1) + 1) ≤ 2 ^ (2 * k + 3) * (m + 1) := by
    calc (2 * k + 3 * m) * (2 ^ (k + 1) + 1) ≤ (2 ^ (k + 1) * (m + 1)) * 2 ^ (k + 2) :=
          Nat.mul_le_mul h1 h2
      _ = 2 ^ (2 * k + 3) * (m + 1) := by
          rw [show 2 * k + 3 = (k + 1) + (k + 2) by ring, pow_add]
          ring
  have hpow : 1 ≤ 2 ^ (2 * k + 3) := Nat.one_le_two_pow
  calc t + (3 + (2 * k + 3 * m) * (2 ^ (k + 1) + 1) + 20 * m) + 2
      ≤ 2 ^ (2 * k + 3) * (m + 1) + (t + 26) * (m + 2) := by nlinarith
    _ ≤ 2 ^ (2 * k + 3) * (m + 2) + 2 ^ (t + 5) * (m + 2) := by gcongr; omega
    _ ≤ 2 ^ (2 * k + 3) * 2 ^ (t + 5) * (m + 2) := by
        have hA : 2 ≤ 2 ^ (2 * k + 3) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (2 * k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hB : 2 ≤ 2 ^ (t + 5) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (t + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hAB : 2 ^ (2 * k + 3) + 2 ^ (t + 5) ≤ 2 ^ (2 * k + 3) * 2 ^ (t + 5) := by nlinarith
        calc 2 ^ (2 * k + 3) * (m + 2) + 2 ^ (t + 5) * (m + 2)
            = (2 ^ (2 * k + 3) + 2 ^ (t + 5)) * (m + 2) := by ring
          _ ≤ 2 ^ (2 * k + 3) * 2 ^ (t + 5) * (m + 2) := Nat.mul_le_mul_right _ hAB
    _ = 2 ^ (2 * k + t + 8) * (m + 2) := by
        rw [← pow_add]
        ring_nf

/-! ### ETH and #ETH in a cost model -/

/-- **ETH in the cost model `M`** (in the form used by the paper): no algorithm decides 3-SAT
within `2^{e(n)} (m+2)^C` with `e(n) ≤ o(n)`. -/
def ETH (M : CostModel) : Prop :=
  ∀ (e : ℕ → ℝ) (C : ℕ), SubLin e →
    ¬ M.Runs satDec (fun φ => ⌊(2 : ℝ) ^ (e φ.1) * ((φ.2.m : ℝ) + 2) ^ C⌋₊)

/-- **#ETH in the cost model `M`**: no algorithm counts the satisfying assignments of 3-CNF
formulas within `2^{e(n)} (m+2)^C` with `e(n) ≤ o(n)`. -/
def SharpETH (M : CostModel) : Prop :=
  ∀ (e : ℕ → ℝ) (C : ℕ), SubLin e →
    ¬ M.Runs satCount (fun φ => ⌊(2 : ℝ) ^ (e φ.1) * ((φ.2.m : ℝ) + 2) ^ C⌋₊)

/-- The arithmetic shared by Theorems 9 and 10: the time of the reduction plus a `2^{f(r)} (N+2)^C`
algorithm on its output is `2^{e(n)} (m+2)^{C'}` with `e(n) ≤ o(n)`. -/
theorem composite_time (t : ℕ) (a : ℝ) (ha : 0 ≤ a) (C₀ : ℕ) (f : ℕ → ℝ) (hf : SubQuad f)
    (C : ℕ) :
    ∃ e : ℕ → ℝ, SubLin e ∧ ∀ φ : Σ n, CNF n,
      ⌊(2 : ℝ) ^ (a * side φ.1) * ((φ.2.m : ℝ) + 2) ^ C₀⌋₊ +
          ⌊(2 : ℝ) ^ (f (red t φ).width) * (((red t φ).N : ℝ) + 2) ^ C⌋₊ ≤
        ⌊(2 : ℝ) ^ (e φ.1) * ((φ.2.m : ℝ) + 2) ^ (max C₀ C)⌋₊ := by
  -- the width bound `B(n) = 2 side(n) + 19 + t`, with `B(n)² ≤ a' (n+1)`
  let B : ℕ → ℕ := fun n => 2 * side n + 19 + t
  have hB : ∀ n, ((B n : ℕ) : ℝ) ^ 2 ≤ (8 + 2 * (21 + t) ^ 2) * (n + 1) := by
    intro n
    have hs := side_le_sqrt n
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hB' : ((B n : ℕ) : ℝ) ≤ 2 * √n + (21 + t) := by
      show ((2 * side n + 19 + t : ℕ) : ℝ) ≤ _
      push_cast
      linarith
    have h0 : (0 : ℝ) ≤ (B n : ℕ) := Nat.cast_nonneg _
    have : ((B n : ℕ) : ℝ) ^ 2 ≤ (2 * √n + (21 + t)) ^ 2 := by gcongr
    nlinarith [Real.sqrt_nonneg (n : ℝ), sq_nonneg (2 * √(n : ℝ) - (21 + t))]
  -- the sup trick
  let F : ℕ → ℝ := fun n => (Finset.range (B n + 1)).sup' (by simp) f
  have hF : SubLin F := SubLin.sup_of_subQuad hf B _ (by positivity) hB
  let e₁ : ℕ → ℝ := fun n => a * side n
  let e₂ : ℕ → ℝ := fun n => F n + C * (2 * side n + t + 8)
  let e : ℕ → ℝ := fun n => 1 + max (e₁ n) (e₂ n)
  have hside : SubLin (fun n => (side n : ℝ)) :=
    SubLin.mono ((SubLin.sqrt).add (SubLin.const 1)) fun n => side_le_sqrt n
  have he : SubLin e := by
    refine (SubLin.const 1).add (SubLin.max (hside.const_mul ha) ?_)
    refine hF.add ?_
    refine SubLin.mono (e' := fun n => (2 * C) * (side n : ℝ) + C * (t + 8))
      ((hside.const_mul (by positivity)).add (SubLin.const _)) fun n => ?_
    ring_nf
    rfl
  refine ⟨e, he, fun φ => ?_⟩
  set n := φ.1
  set m := φ.2.m
  set w := (red t φ).width
  set N := (red t φ).N
  have hm2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  -- the coloring term
  have hw : w ≤ B n := red_width t φ
  have hfw : f w ≤ F n := Finset.le_sup' f (Finset.mem_range.2 (Nat.lt_succ_of_le hw))
  have hN : ((N : ℝ) + 2) ≤ (2 : ℝ) ^ (2 * side n + t + 8 : ℕ) * ((m : ℝ) + 2) := by
    have := red_N t φ
    exact_mod_cast this
  have hcol : (2 : ℝ) ^ (f w) * ((N : ℝ) + 2) ^ C ≤
      (2 : ℝ) ^ (e₂ n) * ((m : ℝ) + 2) ^ C := by
    have h1 : (2 : ℝ) ^ (f w) ≤ (2 : ℝ) ^ (F n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfw
    have h2 : ((N : ℝ) + 2) ^ C ≤ ((2 : ℝ) ^ (2 * side n + t + 8 : ℕ) * ((m : ℝ) + 2)) ^ C :=
      pow_le_pow_left₀ (by positivity) hN C
    have h3 : ((2 : ℝ) ^ (2 * side n + t + 8 : ℕ) * ((m : ℝ) + 2)) ^ C =
        (2 : ℝ) ^ ((C : ℝ) * (2 * side n + t + 8)) * ((m : ℝ) + 2) ^ C := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_natCast]
      congr 2
      push_cast
      ring
    calc (2 : ℝ) ^ (f w) * ((N : ℝ) + 2) ^ C
        ≤ (2 : ℝ) ^ (F n) * ((2 : ℝ) ^ ((C : ℝ) * (2 * side n + t + 8)) * ((m : ℝ) + 2) ^ C) := by
          rw [← h3]
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (e₂ n) * ((m : ℝ) + 2) ^ C := by
          rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
  -- both terms are at most `2^{max} (m+2)^{C'}`
  have hmax1 : (2 : ℝ) ^ (e₁ n) * ((m : ℝ) + 2) ^ C₀ ≤
      (2 : ℝ) ^ (max (e₁ n) (e₂ n)) * ((m : ℝ) + 2) ^ (max C₀ C) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_left (e₁ n) (e₂ n)))
      (pow_le_pow_right₀ hm2 (le_max_left C₀ C)) (by positivity) (by positivity)
  have hmax2 : (2 : ℝ) ^ (e₂ n) * ((m : ℝ) + 2) ^ C ≤
      (2 : ℝ) ^ (max (e₁ n) (e₂ n)) * ((m : ℝ) + 2) ^ (max C₀ C) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_right (e₁ n) (e₂ n)))
      (pow_le_pow_right₀ hm2 (le_max_right C₀ C)) (by positivity) (by positivity)
  have he2 : (2 : ℝ) ^ (e n) = 2 * (2 : ℝ) ^ (max (e₁ n) (e₂ n)) := by
    show (2 : ℝ) ^ (1 + max (e₁ n) (e₂ n)) = _
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  calc ⌊(2 : ℝ) ^ (a * side n) * ((m : ℝ) + 2) ^ C₀⌋₊ + ⌊(2 : ℝ) ^ (f w) * ((N : ℝ) + 2) ^ C⌋₊
      ≤ ⌊(2 : ℝ) ^ (a * side n) * ((m : ℝ) + 2) ^ C₀ + (2 : ℝ) ^ (f w) * ((N : ℝ) + 2) ^ C⌋₊ :=
        floor_add_floor_le (by positivity) (by positivity)
    _ ≤ ⌊(2 : ℝ) ^ (e n) * ((m : ℝ) + 2) ^ (max C₀ C)⌋₊ := by
        apply Nat.floor_le_floor
        rw [he2]
        have : (2 : ℝ) ^ (a * side n) * ((m : ℝ) + 2) ^ C₀ = (2 : ℝ) ^ (e₁ n) * ((m : ℝ) + 2) ^ C₀ :=
          rfl
        linarith [hmax1, hmax2, hcol]

/-- **Theorem 9.**  If ETH holds in `M` and the reduction is computable within
`2^{a k} (m+2)^{C₀}`, then for every fixed number of colors `c = t + 3 ≥ 3`, no algorithm decides
`c`-colorability of `N`-vertex graphs supplied with a linear layout of width `r` within
`2^{f(r)} (N+2)^C` with `f(r) ≤ o(r²)`. -/
theorem fixed_palette_lower_bound (M : CostModel) (hETH : ETH M) (t : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (C₀ : ℕ) (hred : M.Runs (red t) (fun φ => ⌊(2 : ℝ) ^ (a * side φ.1) *
      ((φ.2.m : ℝ) + 2) ^ C₀⌋₊))
    (f : ℕ → ℝ) (hf : SubQuad f) (C : ℕ) :
    ¬ M.Runs (colorDec (t + 3)) (fun I => ⌊(2 : ℝ) ^ (f I.width) * ((I.N : ℝ) + 2) ^ C⌋₊) := by
  intro hcol
  obtain ⟨e, he, hbound⟩ := composite_time t a ha C₀ f hf C
  exact hETH e (max C₀ C) he
    (CostModel.Runs.reduce_le M hcol hred (satDec_eq t) fun φ => hbound φ)

/-- **Theorem 10.**  If #ETH holds in `M`, the reduction is computable within
`2^{a k} (m+2)^{C₀}`, and dividing an output by the known factor of the counting identity costs at
most `2^{a k} (m+2)^{C₀}` more, then for every fixed `c = t + 3 ≥ 3` no algorithm counts the proper
`c`-colorings of graphs supplied with a linear layout of width `r` within `2^{f(r)} (N+2)^C` with
`f(r) ≤ o(r²)`. -/
theorem fixed_palette_counting_lower_bound (M : CostModel) (hETH : SharpETH M) (t : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (C₀ : ℕ)
    (hred : M.Runs (red t) (fun φ => ⌊(2 : ℝ) ^ (a * side φ.1) * ((φ.2.m : ℝ) + 2) ^ C₀⌋₊))
    (hdiv : ∀ T : (Σ n, CNF n) → ℕ, M.Runs (fun φ => factor t φ * satCount φ) T →
      M.Runs satCount (fun φ => T φ + ⌊(2 : ℝ) ^ (a * side φ.1) * ((φ.2.m : ℝ) + 2) ^ C₀⌋₊))
    (f : ℕ → ℝ) (hf : SubQuad f) (C : ℕ) :
    ¬ M.Runs (colorCount (t + 3)) (fun I => ⌊(2 : ℝ) ^ (f I.width) * ((I.N : ℝ) + 2) ^ C⌋₊) := by
  intro hcol
  -- the scaled count
  have h1 := CostModel.Runs.reduce M hcol hred (Q := fun φ => factor t φ * satCount φ)
    (fun φ => (colorCount_eq t φ).symm)
  have h2 := hdiv _ h1
  -- time: (reduction + coloring) + division
  obtain ⟨e, he, hbound⟩ := composite_time t (2 * a) (by positivity) C₀ f hf C
  refine hETH (fun n => e n + 1) (max C₀ C) (he.add (SubLin.const 1)) (M.mono h2 fun φ => ?_)
  have hb := hbound φ
  set X := ⌊(2 : ℝ) ^ (a * side φ.1) * ((φ.2.m : ℝ) + 2) ^ C₀⌋₊
  set Y := ⌊(2 : ℝ) ^ (f (red t φ).width) * (((red t φ).N : ℝ) + 2) ^ C⌋₊
  have hX : X ≤ ⌊(2 : ℝ) ^ (2 * a * side φ.1) * ((φ.2.m : ℝ) + 2) ^ C₀⌋₊ := by
    apply Nat.floor_le_floor
    gcongr
    · norm_num
    · have : (0 : ℝ) ≤ a * side φ.1 := by positivity
      nlinarith
  have hm2 : (1 : ℝ) ≤ (φ.2.m : ℝ) + 2 := by
    have := (Nat.cast_nonneg φ.2.m : (0 : ℝ) ≤ φ.2.m); linarith
  -- `X + Y + X ≤ 2 · 2^{e} (m+2)^{C'} = 2^{e+1} (m+2)^{C'}`
  calc X + Y + X ≤ ⌊(2 : ℝ) ^ (e φ.1) * ((φ.2.m : ℝ) + 2) ^ (max C₀ C)⌋₊ +
        ⌊(2 : ℝ) ^ (e φ.1) * ((φ.2.m : ℝ) + 2) ^ (max C₀ C)⌋₊ := by
        have := Nat.add_le_add_right hX Y
        have h' : ⌊(2 : ℝ) ^ (2 * a * side φ.1) * ((φ.2.m : ℝ) + 2) ^ C₀⌋₊ + Y ≤
            ⌊(2 : ℝ) ^ (e φ.1) * ((φ.2.m : ℝ) + 2) ^ (max C₀ C)⌋₊ := hb
        have hXle : X ≤ ⌊(2 : ℝ) ^ (e φ.1) * ((φ.2.m : ℝ) + 2) ^ (max C₀ C)⌋₊ := by omega
        omega
    _ ≤ ⌊(2 : ℝ) ^ (e φ.1 + 1) * ((φ.2.m : ℝ) + 2) ^ (max C₀ C)⌋₊ := by
        refine (floor_add_floor_le (by positivity) (by positivity)).trans
          (Nat.floor_le_floor (le_of_eq ?_))
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
        ring

/-- The same exclusions hold with a supplied rank-decomposition: the caterpillar of the supplied
layout has the same width (`LinearLayout.width_toRankDecomposition_le`). -/
theorem caterpillar_width (t : ℕ) {n : ℕ} (φ : CNF n) (v : Fin t ⊕ Vtx (side n) (grid φ).m)
    (vs : List (Fin t ⊕ Vtx (side n) (grid φ).m)) (h : (redLayout t φ).order = v :: vs) :
    ((redLayout t φ).toRankDecomposition v vs h).width (redGraph t φ) ≤ 2 * side n + 19 + t :=
  ((redLayout t φ).width_toRankDecomposition_le (redGraph t φ) v vs h).trans
    (max_le (reduction_spec t φ).2.1 (by omega))

end SubspaceConvolution.FixedPalette
