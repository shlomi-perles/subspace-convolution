/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.CounterSize

/-!
# Theorem 8: the Chromatic Number lower bound with the coefficient `1/4`

* `reduction_spec` — the unconditional content: for a normalized instance `I`,
  `χ(G_I) ≤ η ⟺ I satisfiable` (Lemma 5), the supplied layout has width `r ≤ 2d + 12`
  (Lemma 6), `d ≤ √(log₂ k) + 1`, and `2^{r²/4 - 17r} ≤ max {1, k 2^{-20 √(log₂ k) - 189}}`;
  on the instance class of Lemma 4 also `N ≤ g(k) (n+1)^6` (`card_Vtx_le_poly`).
* `chromatic_lower_bound` — **Theorem 8**, as a statement about any abstract cost model `M`:
  if Lemma 4 holds in `M` (no `F(k) n^{o(k)}` algorithm for 4-Monotone min-CSP on its instance
  class; this is the ETH consequence proved in FGL+19), and the reduction is computable within
  `G(k) (n+1)^{C₁}` in `M`, then for every `f` and fixed `α ≥ 0` no algorithm decides
  `χ(G) ≤ η` on graphs supplied with a linear layout of width `r` within
  `f(r) N^{α + 2^{r²/4 - 17r}}`.
-/

open Real

namespace SubspaceConvolution.Counter

open Classical in
/-- Deciding `χ(G) ≤ η` for a graph supplied with a linear layout. -/
noncomputable def chromDec : LayoutGraph × ℕ → Bool := fun J => decide (J.1.G.Colorable J.2)

open Classical in
/-- Deciding 4-Monotone min-CSP on the instance class of Lemma 4. -/
noncomputable def minCSPDec (c₀ : ℕ) : {I : MinCSP // Restricted c₀ I} → Bool :=
  fun I => decide I.1.Satisfiable

/-- The counter reduction, with the graph relabelled onto `Fin N`. -/
noncomputable def red (c₀ : ℕ) : {I : MinCSP // Restricted c₀ I} → LayoutGraph × ℕ :=
  fun I => (LayoutGraph.ofGraph (graph I.1) (layout I.1), eta I.1)

theorem minCSPDec_eq (c₀ : ℕ) (I : {I : MinCSP // Restricted c₀ I}) :
    minCSPDec c₀ I = chromDec (red c₀ I) := by
  unfold minCSPDec chromDec red
  rw [decide_eq_decide]
  rw [LayoutGraph.colorable_ofGraph_iff, colorable_iff I.1 I.2.1]

theorem one_le_d {I : MinCSP} (hI : I.Normalized) : 1 ≤ d I := by
  by_contra h
  have h0 : d I = 0 := by omega
  have := Nat.find_spec (exists_sq_exponent I.k)
  rw [show Nat.find (exists_sq_exponent I.k) = d I from rfl, h0] at this
  have := hI.two_le_k
  simp at *
  omega

theorem one_le_card_Vtx {I : MinCSP} (hI : I.Normalized) : 1 ≤ Fintype.card (Vtx I) := by
  have h := card_Vtx I
  have hd := one_le_d hI
  have hQ : 1 ≤ Q I := Nat.one_le_iff_ne_zero.2 (by
    unfold Q M
    have := hI.one_le_n
    positivity)
  have : 1 ≤ d I * Q I := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

theorem d_le_sqrt_logb {I : MinCSP} (hI : I.Normalized) :
    (d I : ℝ) ≤ √(logb 2 I.k) + 1 :=
  d_le_sqrt_log (by have := hI.two_le_k; omega) fun d' hd' => by
    have := Nat.find_min (exists_sq_exponent I.k) hd'
    push Not at this
    exact this

/-- **Theorem 8, unconditional part.** -/
theorem reduction_spec (I : MinCSP) (hI : I.Normalized) :
    ((graph I).chromaticNumber ≤ eta I ↔ I.Satisfiable) ∧
      (layout I).width (graph I) ≤ 2 * d I + 12 ∧
      (d I : ℝ) ≤ √(logb 2 I.k) + 1 ∧
      (2 : ℝ) ^ (((layout I).width (graph I) : ℝ) ^ 2 / 4 - 17 * (layout I).width (graph I)) ≤
        max 1 (I.k * (2 : ℝ) ^ (-20 * √(logb 2 I.k) - 189)) := by
  refine ⟨?_, layout_width I hI, d_le_sqrt_logb hI, ?_⟩
  · rw [SimpleGraph.chromaticNumber_le_iff_colorable, colorable_iff I hI]
  · exact two_rpow_b_le (by have := hI.two_le_k; omega) (d_le_sqrt_logb hI) (layout_width I hI)

/-- **Lemma 4 in the cost model `M`** (FGL+19, Lemma 3.1, under ETH): no algorithm decides
4-Monotone min-CSP on the instances with `|C| ≤ c₀ k² n²` and `L ≤ max(n, 4)` within
`F(k) (n+1)^{e(k)}` with `e(k) ≤ o(k)`. -/
def MinCSPHard (M : CostModel) (c₀ : ℕ) : Prop :=
  ∀ (F : ℕ → ℝ) (e : ℕ → ℝ), SubLin e →
    ¬ M.Runs (minCSPDec c₀) (fun I => ⌊F I.1.k * ((I.1.n : ℝ) + 1) ^ (e I.1.k)⌋₊)

/-- **Theorem 8.**  Assume Lemma 4 in the cost model `M` and that the reduction is computable
within `G(k) (n+1)^{C₁}`.  Then for every function `f` and every fixed `α ≥ 0`, no algorithm
decides `χ(G) ≤ η` on `N`-vertex graphs supplied with a linear layout of width `r` within
`f(r) N^{α + 2^{r²/4 - 17r}}`. -/
theorem chromatic_lower_bound (M : CostModel) (c₀ : ℕ) (hhard : MinCSPHard M c₀)
    (G : ℕ → ℝ) (C₁ : ℝ)
    (hred : M.Runs (red c₀) (fun I => ⌊G I.1.k * ((I.1.n : ℝ) + 1) ^ C₁⌋₊))
    (f : ℕ → ℝ) (α : ℝ) (hα : 0 ≤ α) :
    ¬ M.Runs chromDec (fun J => ⌊f J.1.width *
      (J.1.N : ℝ) ^ (α + (2 : ℝ) ^ ((J.1.width : ℝ) ^ 2 / 4 - 17 * J.1.width))⌋₊) := by
  intro hcol
  -- the parameters of the composite algorithm
  let dk : ℕ → ℕ := fun k => Nat.find (exists_sq_exponent k)
  let F₀ : ℕ → ℝ := fun k => (Finset.range (2 * dk k + 13)).sup' (by simp) fun j => |f j|
  let g : ℕ → ℝ := fun k => (sizeFactor c₀ k : ℝ)
  let ρ : ℕ → ℝ := fun k => (2 : ℝ) ^ (-20 * √(logb 2 k) - 189)
  let e₂ : ℕ → ℝ := fun k => 6 * (α + max 1 (k * ρ k))
  let e : ℕ → ℝ := fun k => max C₁ (e₂ k)
  let F : ℕ → ℝ := fun k => |G k| + F₀ k * g k ^ (α + 1 + k)
  -- `e` is sublinear
  have he : SubLin e := by
    refine SubLin.max (SubLin.const C₁) ?_
    have hρ : SubLin (fun k => k * ρ k) := by
      intro η hη
      have := (tendsto_ratio_zero).eventually (gt_mem_nhds hη)
      refine this.mono fun k hk => ?_
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      calc (k : ℝ) * ρ k ≤ k * η := by gcongr
        _ = η * k := by ring
    refine SubLin.mono (e' := fun k => 6 * α + 6 + 6 * (k * ρ k))
      ((SubLin.const (6 * α + 6)).add (hρ.const_mul (by norm_num))) fun k => ?_
    show 6 * (α + max 1 (k * ρ k)) ≤ 6 * α + 6 + 6 * (k * ρ k)
    have : max 1 ((k : ℝ) * ρ k) ≤ 1 + k * ρ k := by
      have : 0 ≤ (k : ℝ) * ρ k := by positivity
      exact max_le (by linarith) (by linarith)
    linarith
  apply hhard F e he
  refine M.mono (CostModel.Runs.reduce M hcol hred (minCSPDec_eq c₀)) fun I => ?_
  obtain ⟨I, hI⟩ := I
  have hN : I.Normalized := hI.1
  -- notation for the instance
  set k := I.k
  set n := I.n
  set w := (red c₀ ⟨I, hI⟩).1.width with hw
  set N := (red c₀ ⟨I, hI⟩).1.N with hNdef
  have hwI : w = (layout I).width (graph I) := LayoutGraph.width_ofGraph _ _
  have hNI : N = Fintype.card (Vtx I) := rfl
  have hw12 : w ≤ 2 * dk k + 12 := hwI ▸ layout_width I hN
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNI]
    exact_mod_cast one_le_card_Vtx hN
  have hg1 : (1 : ℝ) ≤ g k := by
    show (1 : ℝ) ≤ (sizeFactor c₀ k : ℝ)
    have : 1 ≤ sizeFactor c₀ k := by
      unfold sizeFactor
      simp only
      have h2 : 1 ≤ (Nat.find (exists_sq_exponent k) + 1) *
          2 ^ (Nat.find (exists_sq_exponent k) * Nat.find (exists_sq_exponent k)) :=
        Nat.one_le_iff_ne_zero.2 (by positivity)
      exact h2.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact_mod_cast this
  have hNg' : (N : ℝ) ≤ g k * ((n : ℝ) + 1) ^ (6 : ℕ) := by
    rw [hNI]
    show (Fintype.card (Vtx I) : ℝ) ≤ (sizeFactor c₀ k : ℝ) * ((n : ℝ) + 1) ^ (6 : ℕ)
    exact_mod_cast card_Vtx_le_poly hI
  have hNg : (N : ℝ) ≤ g k * ((n : ℝ) + 1) ^ (6 : ℝ) := by
    have : ((n : ℝ) + 1) ^ (6 : ℝ) = ((n : ℝ) + 1) ^ (6 : ℕ) := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [this]
    exact hNg'
  -- the exponent: `α + 2^{b(w)} ≤ β := α + max 1 (k ρ(k)) ≤ α + 1 + k`
  have hb : (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w) ≤ max 1 (k * ρ k) := by
    rw [hwI]
    exact two_rpow_b_le (by have := hN.two_le_k; omega) (d_le_sqrt_logb hN) (layout_width I hN)
  set β := α + max 1 ((k : ℝ) * ρ k) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβk : β ≤ α + 1 + k := by
    have hρ1 : ρ k ≤ 1 := by
      show (2 : ℝ) ^ (-20 * √(logb 2 k) - 189) ≤ 1
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have := Real.sqrt_nonneg (logb 2 (k : ℝ))
      linarith
    have : (k : ℝ) * ρ k ≤ k := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (-20 * √(logb 2 k) - 189)]
    have : max 1 ((k : ℝ) * ρ k) ≤ 1 + k := max_le (by linarith [Nat.cast_nonneg (α := ℝ) k])
      (by linarith)
    linarith
  -- bound the coloring term
  have hcolor : |f w * (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w))| ≤
      F₀ k * g k ^ (α + 1 + k) * ((n : ℝ) + 1) ^ e k := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have hf : |f w| ≤ F₀ k :=
      Finset.le_sup' (fun j => |f j|) (Finset.mem_range.2 (by omega))
    have h1 : (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w)) ≤ (N : ℝ) ^ β :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : (N : ℝ) ^ β ≤ (g k * ((n : ℝ) + 1) ^ (6 : ℝ)) ^ β :=
      Real.rpow_le_rpow (by linarith) hNg hβ0
    have h3 : (g k * ((n : ℝ) + 1) ^ (6 : ℝ)) ^ β = g k ^ β * ((n : ℝ) + 1) ^ e₂ k := by
      rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul (by linarith)]
    have h4 : g k ^ β ≤ g k ^ (α + 1 + k) := Real.rpow_le_rpow_of_exponent_le hg1 hβk
    have h5 : ((n : ℝ) + 1) ^ e₂ k ≤ ((n : ℝ) + 1) ^ e k :=
      Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
    have hF0 : 0 ≤ F₀ k := le_trans (abs_nonneg _) hf
    calc |f w| * (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w))
        ≤ F₀ k * (g k ^ β * ((n : ℝ) + 1) ^ e₂ k) := by
          rw [← h3]
          exact mul_le_mul hf (h1.trans h2) (Real.rpow_nonneg (by linarith) _) hF0
      _ ≤ F₀ k * (g k ^ (α + 1 + k) * ((n : ℝ) + 1) ^ e k) := by
          gcongr
      _ = F₀ k * g k ^ (α + 1 + k) * ((n : ℝ) + 1) ^ e k := by ring
  -- bound the reduction term
  have hred' : |G k * ((n : ℝ) + 1) ^ C₁| ≤ |G k| * ((n : ℝ) + 1) ^ e k := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    gcongr
    exact le_max_left _ _
  -- combine
  have hfloor1 : ⌊G k * ((n : ℝ) + 1) ^ C₁⌋₊ ≤ ⌊|G k * ((n : ℝ) + 1) ^ C₁|⌋₊ :=
    Nat.floor_le_floor (le_abs_self _)
  have hfloor2 : ⌊f w * (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w))⌋₊ ≤
      ⌊|f w * (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w))|⌋₊ :=
    Nat.floor_le_floor (le_abs_self _)
  calc ⌊G k * ((n : ℝ) + 1) ^ C₁⌋₊ +
        ⌊f w * (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w))⌋₊
      ≤ ⌊|G k * ((n : ℝ) + 1) ^ C₁|⌋₊ +
          ⌊|f w * (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w))|⌋₊ :=
        Nat.add_le_add hfloor1 hfloor2
    _ ≤ ⌊|G k * ((n : ℝ) + 1) ^ C₁| +
          |f w * (N : ℝ) ^ (α + (2 : ℝ) ^ ((w : ℝ) ^ 2 / 4 - 17 * w))|⌋₊ :=
        SubspaceConvolution.floor_add_floor_le (abs_nonneg _) (abs_nonneg _)
    _ ≤ ⌊F k * ((n : ℝ) + 1) ^ e k⌋₊ := by
        apply Nat.floor_le_floor
        show _ ≤ (|G k| + F₀ k * g k ^ (α + 1 + k)) * ((n : ℝ) + 1) ^ e k
        nlinarith [hcolor, hred']

/-- The caterpillar rank-decomposition of the supplied layout has the same width bound `2d + 12`
(Theorem 8: "The same exclusion holds with a supplied rank-decomposition of width `r`"). -/
theorem caterpillar_width (I : MinCSP) (hI : I.Normalized) (v : Vtx I) (vs : List (Vtx I))
    (h : (layout I).order = v :: vs) :
    ((layout I).toRankDecomposition v vs h).width (graph I) ≤ 2 * d I + 12 :=
  ((layout I).width_toRankDecomposition_le (graph I) v vs h).trans
    (max_le (layout_width I hI) (by omega))

end SubspaceConvolution.Counter
