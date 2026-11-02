/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# Counting subspaces (Appendix A)

* `card_finrank_eq_mul_prod` — counting ordered bases: for `j ≤ n = dim V` over a finite field
  with `q` elements, `|Gr(V, j)| · ∏_{i<j} (q^j - q^i) = ∏_{i<j} (q^n - q^i)`.
* `numSubspaces r` — `N₂(r)`, the number of subspaces of `F₂^r`, and
  `card_submodule_eq_numSubspaces`, `numSubspaces_mono`, `card_submodules_le_of_finrank_le`.
* `numSubspacesOfDim r j = |Gr(r, j)|` and the bounds
  `2 ^ (j (r - j)) ≤ |Gr(r, j)| ≤ 4 · 2 ^ (j (r - j))` (`pow_le_numSubspacesOfDim`,
  `numSubspacesOfDim_le`), from `|GL_j(F₂)| ≥ 2 ^ (j²) / 4` (`pow_le_four_mul_prod`).
* `numSubspaces_le`, `le_numSubspaces` — `2 ^ ⌊r²/4⌋ ≤ N₂(r) ≤ 2 ^ (⌊r²/4⌋ + 4)`, i.e.
  `N₂(r) = 2 ^ (r²/4 + O(1))`.  The upper bound sums `4 · 2 ^ (j (r - j))` over `j`; completing
  the square, the exponent drops at least linearly away from `j = ⌊r/2⌋`
  (`sum_two_pow_mul_sub_le`).
* Small values: `numSubspaces_zero`, `numSubspaces_one`, `numSubspaces_two` (`1, 2, 5`).
-/

open Finset Module

namespace SubspaceConvolution

/-! ## Counting subspaces of a given dimension over a finite field -/

section Grassmannian

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The span of a linearly independent `j`-tuple, as a `j`-dimensional subspace. -/
def spanOfLinearIndependent {j : ℕ} (s : {s : Fin j → V // LinearIndependent K s}) :
    {W : Submodule K V // finrank K W = j} :=
  ⟨Submodule.span K (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- The linearly independent `j`-tuples spanning a `j`-dimensional subspace `W` are exactly the
ordered bases of `W`. -/
def spanOfLinearIndependentFiberEquiv {j : ℕ} (W : {W : Submodule K V // finrank K W = j})
    [FiniteDimensional K W.1] :
    {s // spanOfLinearIndependent s = W} ≃ {t : Fin j → W.1 // LinearIndependent K t} where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have h : (spanOfLinearIndependent s.1).1 = W.1 := congrArg Subtype.val s.2
      rw [← h]
      exact Submodule.subset_span (Set.mem_range_self i)⟩,
    LinearIndependent.of_comp W.1.subtype s.1.2⟩
  invFun t := ⟨⟨W.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, by
    apply Subtype.ext
    change Submodule.span K (Set.range (W.1.subtype ∘ t.1)) = W.1
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (t.1 i).2
    · rw [finrank_span_eq_card (t.2.map' _ (Submodule.ker_subtype _)), Fintype.card_fin, W.2]⟩
  left_inv s := rfl
  right_inv t := rfl

variable [Fintype K] [FiniteDimensional K V]

/-- **Counting ordered bases.** For `j ≤ n = dim V` over a finite field with `q` elements, the
number of `j`-dimensional subspaces times the number `∏_{i<j} (q^j - q^i)` of ordered bases of a
`j`-dimensional space equals the number `∏_{i<j} (q^n - q^i)` of linearly independent `j`-tuples
in `V`. -/
theorem card_finrank_eq_mul_prod {j : ℕ} (hj : j ≤ finrank K V) :
    Nat.card {W : Submodule K V // finrank K W = j} *
        ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin j, (Fintype.card K ^ finrank K V - Fintype.card K ^ (i : ℕ)) := by
  have : Finite V := Module.finite_of_finite K
  have : Fintype {W : Submodule K V // finrank K W = j} := Fintype.ofFinite _
  have hfib : ∀ W : {W : Submodule K V // finrank K W = j},
      Nat.card {s // spanOfLinearIndependent s = W} =
        ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) := by
    intro W
    rw [Nat.card_congr (spanOfLinearIndependentFiberEquiv W), card_linearIndependent W.2.ge, W.2]
  rw [← card_linearIndependent hj,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (spanOfLinearIndependent (K := K) (V := V) (j := j))),
    Nat.card_sigma, Finset.sum_congr rfl fun W _ => hfib W, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

/-- `card_finrank_eq_mul_prod` for `V = K^n`. -/
theorem card_finrank_eq_mul_prod_fin {n j : ℕ} (hj : j ≤ n) :
    Nat.card {W : Submodule K (Fin n → K) // finrank K W = j} *
        ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin j, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) := by
  have h := card_finrank_eq_mul_prod (K := K) (V := Fin n → K) (j := j)
    (by rwa [Module.finrank_fin_fun])
  rwa [Module.finrank_fin_fun] at h

end Grassmannian

/-- `card_finrank_eq_mul_prod` with the number of ordered bases of `K^j` written as `|GL_j(K)|`. -/
theorem card_finrank_mul_card_GL {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {j : ℕ} (hj : j ≤ finrank K V) :
    Nat.card {W : Submodule K V // finrank K W = j} * Nat.card (GL (Fin j) K) =
      ∏ i : Fin j, (Fintype.card K ^ finrank K V - Fintype.card K ^ (i : ℕ)) := by
  rw [Matrix.card_GL_field]
  exact card_finrank_eq_mul_prod hj

/-! ## The number `N₂(r)` of subspaces of `F₂^r` -/

/-- `N₂(r)`: the number of subspaces of `F₂^r`. -/
noncomputable def numSubspaces (r : ℕ) : ℕ := Nat.card (Submodule F2 (Fin r → F2))

/-- The number `|Gr(r, j)|` of `j`-dimensional subspaces of `F₂^r`. -/
noncomputable def numSubspacesOfDim (r j : ℕ) : ℕ :=
  Nat.card {W : Submodule F2 (Fin r → F2) // finrank F2 W = j}

/-- The number of subspaces of an `r`-dimensional `F₂`-space is `N₂(r)`. -/
theorem card_submodule_eq_numSubspaces {E : Type*} [AddCommGroup E] [Module F2 E]
    [FiniteDimensional F2 E] :
    Nat.card (Submodule F2 E) = numSubspaces (finrank F2 E) :=
  Nat.card_congr (Submodule.orderIsoMapComap
    (LinearEquiv.ofFinrankEq E (Fin (finrank F2 E) → F2) (by simp))).toEquiv

/-- An injective linear map does not decrease the number of subspaces. -/
theorem card_submodule_le_of_injective {E E' : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup E'] [Module F2 E'] [Finite E'] {f : E →ₗ[F2] E'}
    (hf : Function.Injective f) : Nat.card (Submodule F2 E) ≤ Nat.card (Submodule F2 E') :=
  Nat.card_le_card_of_injective _ (Submodule.map_injective_of_injective hf)

/-- `N₂` is monotone: `F₂^r` embeds into `F₂^s` for `r ≤ s`. -/
theorem numSubspaces_mono : Monotone numSubspaces := by
  intro r s hrs
  have h := card_submodule_le_of_injective
    (LinearMap.inl_injective (R := F2) (M := Fin r → F2) (M₂ := Fin (s - r) → F2))
  rwa [card_submodule_eq_numSubspaces (E := (Fin r → F2) × (Fin (s - r) → F2)),
    Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
    Nat.add_sub_cancel' hrs] at h

/-- The subspaces of a subspace `W` of dimension at most `r` number at most `N₂(r)`. -/
theorem card_submodules_le_of_finrank_le {E : Type*} [AddCommGroup E] [Module F2 E]
    [FiniteDimensional F2 E] (W : Submodule F2 E) {r : ℕ} (h : finrank F2 W ≤ r) :
    Nat.card {U : Submodule F2 E // U ≤ W} ≤ numSubspaces r := by
  rw [← Nat.card_congr (Submodule.MapSubtype.orderIso W).toEquiv,
    card_submodule_eq_numSubspaces]
  exact numSubspaces_mono h

/-- `|Gr(r, j)| · ∏_{i<j} (2^j - 2^i) = ∏_{i<j} (2^r - 2^i)`. -/
theorem numSubspacesOfDim_mul_prod {r j : ℕ} (hj : j ≤ r) :
    numSubspacesOfDim r j * ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ)) =
      ∏ i : Fin j, (2 ^ r - 2 ^ (i : ℕ)) := by
  have h := card_finrank_eq_mul_prod_fin (K := F2) hj
  rwa [ZMod.card] at h

/-- `N₂(r) = ∑_{j ≤ r} |Gr(r, j)|`. -/
theorem numSubspaces_eq_sum (r : ℕ) :
    numSubspaces r = ∑ j ∈ range (r + 1), numSubspacesOfDim r j := by
  let f : Submodule F2 (Fin r → F2) → Fin (r + 1) := fun W =>
    ⟨finrank F2 W, Nat.lt_succ_of_le ((Submodule.finrank_le W).trans_eq (by simp))⟩
  rw [numSubspaces, ← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => Nat.card_congr (Equiv.subtypeEquivRight fun W => ?_)
  simp [f, Fin.ext_iff]

/-! ## Elementary estimates -/

/-- The recursion `|GL_{j+1}(F₂)| = (2^{j+1} - 1) · 2^j · |GL_j(F₂)|`. -/
theorem prod_two_pow_sub_succ (j : ℕ) :
    ∏ i : Fin (j + 1), (2 ^ (j + 1) - 2 ^ (i : ℕ)) =
      (2 ^ (j + 1) - 1) * 2 ^ j * ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ]
  have h : ∀ i : Fin j, 2 ^ (j + 1) - 2 ^ ((i : ℕ) + 1) = 2 * (2 ^ j - 2 ^ (i : ℕ)) := by
    intro i
    rw [pow_succ, pow_succ]
    omega
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_assoc]

/-- Each factor `2^j - 2^i`, `i < j`, is positive. -/
theorem prod_two_pow_sub_pos (j : ℕ) : 0 < ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ)) :=
  Finset.prod_pos fun i _ => Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) i.2)

/-- `∏_{i<k+1} (1 - 2^{-(i+1)}) ≥ 1/4 + 2^{-(k+2)}`, multiplied out. -/
theorem prod_two_pow_sub_aux (k : ℕ) :
    (2 ^ (k + 2) + 4) * 2 ^ ((k + 1) * (k + 1)) ≤
      4 * 2 ^ (k + 2) * ∏ i : Fin (k + 1), (2 ^ (k + 1) - 2 ^ (i : ℕ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_two_pow_sub_succ (k + 1)]
    set A := ∏ i : Fin (k + 1), (2 ^ (k + 1) - 2 ^ (i : ℕ))
    set x := 2 ^ (k + 1) with hx_def
    have hx : 2 ≤ x := by
      rw [hx_def, pow_succ]
      have := Nat.one_le_two_pow (n := k)
      omega
    have h2 : 2 ^ (k + 1 + 1) = 2 * x := by rw [pow_succ, mul_comm]
    have h3 : 2 ^ (k + 1 + 2) = 4 * x := by rw [hx_def, pow_add]; ring
    have h4 : 2 ^ ((k + 1 + 1) * (k + 1 + 1)) = 2 ^ ((k + 1) * (k + 1)) * x * x * 2 := by
      rw [hx_def, ← pow_add, ← pow_add, ← pow_succ]
      congr 1
      ring
    rw [h2] at ih
    rw [h2, h3, h4]
    set P := 2 ^ ((k + 1) * (k + 1))
    obtain ⟨y, hy⟩ : ∃ y, 2 * x - 1 = y := ⟨_, rfl⟩
    have hy' : y + 1 = 2 * x := by omega
    rw [hy]
    have key : (4 * x + 4) * x ≤ y * (2 * x + 4) := by nlinarith
    calc (4 * x + 4) * (P * x * x * 2) = (4 * x + 4) * x * (2 * x * P) := by ring
      _ ≤ y * (2 * x + 4) * (2 * x * P) := Nat.mul_le_mul_right _ key
      _ = 2 * x * y * ((2 * x + 4) * P) := by ring
      _ ≤ 2 * x * y * (4 * (2 * x) * A) := Nat.mul_le_mul_left _ ih
      _ = 4 * (4 * x) * (y * x * A) := by ring

/-- `|GL_j(F₂)| ≥ 2^{j²}/4`, since `∏_{i ≥ 1} (1 - 2^{-i}) ≥ 1/4`. -/
theorem pow_le_four_mul_prod (j : ℕ) : 2 ^ (j * j) ≤ 4 * ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ)) := by
  cases j with
  | zero => simp
  | succ k =>
    have h := prod_two_pow_sub_aux k
    refine Nat.le_of_mul_le_mul_left (c := 2 ^ (k + 2)) ?_ (by positivity)
    calc 2 ^ (k + 2) * 2 ^ ((k + 1) * (k + 1))
        ≤ (2 ^ (k + 2) + 4) * 2 ^ ((k + 1) * (k + 1)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 4 * 2 ^ (k + 2) * ∏ i : Fin (k + 1), (2 ^ (k + 1) - 2 ^ (i : ℕ)) := h
      _ = 2 ^ (k + 2) * (4 * ∏ i : Fin (k + 1), (2 ^ (k + 1) - 2 ^ (i : ℕ))) := by ring

/-- `∏_{i<j} (2^r - 2^i) ≤ 2^{rj}`. -/
theorem prod_two_pow_sub_le (r j : ℕ) : ∏ i : Fin j, (2 ^ r - 2 ^ (i : ℕ)) ≤ 2 ^ (r * j) := by
  calc ∏ i : Fin j, (2 ^ r - 2 ^ (i : ℕ)) ≤ (2 ^ r) ^ (Finset.univ : Finset (Fin j)).card :=
        Finset.prod_le_pow_card _ _ _ fun i _ => Nat.sub_le _ _
    _ = 2 ^ (r * j) := by rw [Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- A sum dominated by a geometric series: if `a t ≤ C / 2^t` for `t < n`, then
`∑_{t<n} a t ≤ 2 C`. -/
theorem sum_le_two_mul_of_mul_pow_le {n C : ℕ} {a : ℕ → ℕ} (h : ∀ t < n, a t * 2 ^ t ≤ C) :
    ∑ t ∈ range n, a t ≤ 2 * C := by
  have key : ∀ n, (∀ t < n, a t * 2 ^ t ≤ C) →
      2 ^ n * ∑ t ∈ range n, a t + 2 * C ≤ 2 * C * 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro h
      have ih := ih fun t ht => h t (Nat.lt_succ_of_lt ht)
      have hn := h n (Nat.lt_succ_self n)
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  have := key n h
  exact Nat.le_of_mul_le_mul_left (c := 2 ^ n) (by nlinarith) (by positivity)

/-- `⌊r²/4⌋ = ⌊r/2⌋ ⌈r/2⌉`. -/
theorem mul_self_div_four (r : ℕ) : r * r / 4 = r / 2 * (r - r / 2) := by
  rcases Nat.even_or_odd' r with ⟨k, rfl | rfl⟩
  · have h1 : 2 * k / 2 = k := by omega
    have h2 : 2 * k - k = k := by omega
    have h3 : 2 * k * (2 * k) = 4 * (k * k) := by ring
    rw [h1, h2, h3, Nat.mul_div_cancel_left _ (by norm_num)]
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k + 1 - k = k + 1 := by omega
    have h3 : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    have h4 : k * (k + 1) = k * k + k := by ring
    rw [h1, h2, h3, h4]
    omega

/-- Below the middle, `j(r-j)` decays at least linearly: for `j = ⌊r/2⌋ - t`,
`j(r-j) + t ≤ ⌊r²/4⌋`. -/
theorem exponent_le_left {r t : ℕ} (ht : t ≤ r / 2) :
    (r / 2 - t) * (r - (r / 2 - t)) + t ≤ r * r / 4 := by
  rw [mul_self_div_four]
  rcases Nat.even_or_odd' r with ⟨k, rfl | rfl⟩
  · have h1 : 2 * k / 2 = k := by omega
    rw [h1] at ht ⊢
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
    have h2 : t + u - t = u := by omega
    have h3 : 2 * (t + u) - u = u + 2 * t := by omega
    have h4 : 2 * (t + u) - (t + u) = t + u := by omega
    rw [h2, h3, h4]
    nlinarith [Nat.le_mul_self t]
  · have h1 : (2 * k + 1) / 2 = k := by omega
    rw [h1] at ht ⊢
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
    have h2 : t + u - t = u := by omega
    have h3 : 2 * (t + u) + 1 - u = u + 2 * t + 1 := by omega
    have h4 : 2 * (t + u) + 1 - (t + u) = t + u + 1 := by omega
    rw [h2, h3, h4]
    nlinarith

/-- Above the middle, `j(r-j)` decays at least linearly: for `j = ⌊r/2⌋ + 1 + t ≤ r`,
`j(r-j) + t ≤ ⌊r²/4⌋`. -/
theorem exponent_le_right {r t : ℕ} (ht : t < r - r / 2) :
    (r / 2 + 1 + t) * (r - (r / 2 + 1 + t)) + t ≤ r * r / 4 := by
  rw [mul_self_div_four]
  rcases Nat.even_or_odd' r with ⟨k, rfl | rfl⟩
  · have h1 : 2 * k / 2 = k := by omega
    rw [h1] at ht ⊢
    obtain ⟨s, hs⟩ : ∃ s, k = t + 1 + s := ⟨k - t - 1, by omega⟩
    subst hs
    have h2 : 2 * (t + 1 + s) - (t + 1 + s + 1 + t) = s := by omega
    have h3 : 2 * (t + 1 + s) - (t + 1 + s) = t + 1 + s := by omega
    rw [h2, h3]
    nlinarith
  · have h1 : (2 * k + 1) / 2 = k := by omega
    rw [h1] at ht ⊢
    obtain ⟨s, hs⟩ : ∃ s, k = t + s := ⟨k - t, by omega⟩
    subst hs
    have h2 : 2 * (t + s) + 1 - (t + s + 1 + t) = s := by omega
    have h3 : 2 * (t + s) + 1 - (t + s) = t + s + 1 := by omega
    rw [h2, h3]
    nlinarith

/-- Completing the square: `∑_{j ≤ r} 2^{j(r-j)} ≤ 4 · 2^{⌊r²/4⌋}`. -/
theorem sum_two_pow_mul_sub_le (r : ℕ) :
    ∑ j ∈ range (r + 1), 2 ^ (j * (r - j)) ≤ 4 * 2 ^ (r * r / 4) := by
  have hsplit : r + 1 = (r / 2 + 1) + (r - r / 2) := by omega
  have h1 : ∑ j ∈ range (r / 2 + 1), 2 ^ (j * (r - j)) ≤ 2 * 2 ^ (r * r / 4) := by
    rw [← Finset.sum_range_reflect]
    refine sum_le_two_mul_of_mul_pow_le fun t ht => ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    rw [Nat.add_sub_cancel]
    exact exponent_le_left (by omega)
  have h2 : ∑ t ∈ range (r - r / 2), 2 ^ ((r / 2 + 1 + t) * (r - (r / 2 + 1 + t))) ≤
      2 * 2 ^ (r * r / 4) := by
    refine sum_le_two_mul_of_mul_pow_le fun t ht => ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (exponent_le_right ht)
  rw [hsplit, Finset.sum_range_add]
  linarith

/-! ## Bounds on `|Gr(r, j)|` and `N₂(r)` -/

/-- `|Gr(r, j)| ≤ 4 · 2^{j(r-j)}`. -/
theorem numSubspacesOfDim_le {r j : ℕ} (hj : j ≤ r) :
    numSubspacesOfDim r j ≤ 4 * 2 ^ (j * (r - j)) := by
  have h1 := numSubspacesOfDim_mul_prod hj
  have h2 := pow_le_four_mul_prod j
  have h3 := prod_two_pow_sub_le r j
  have h4 : r * j = j * (r - j) + j * j := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hj, Nat.mul_comm]
  refine Nat.le_of_mul_le_mul_right (c := 2 ^ (j * j)) ?_ (by positivity)
  calc numSubspacesOfDim r j * 2 ^ (j * j)
      ≤ numSubspacesOfDim r j * (4 * ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ))) :=
        Nat.mul_le_mul_left _ h2
    _ = 4 * (numSubspacesOfDim r j * ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ))) := by ring
    _ = 4 * ∏ i : Fin j, (2 ^ r - 2 ^ (i : ℕ)) := by rw [h1]
    _ ≤ 4 * 2 ^ (r * j) := Nat.mul_le_mul_left _ h3
    _ = 4 * 2 ^ (j * (r - j)) * 2 ^ (j * j) := by rw [h4, pow_add, mul_assoc]

/-- `|Gr(r, j)| ≥ 2^{j(r-j)}`: each factor `(2^r - 2^i)/(2^j - 2^i)` is at least `2^{r-j}`. -/
theorem pow_le_numSubspacesOfDim {r j : ℕ} (hj : j ≤ r) :
    2 ^ (j * (r - j)) ≤ numSubspacesOfDim r j := by
  have h1 := numSubspacesOfDim_mul_prod hj
  have hfac : ∀ i : Fin j, 2 ^ (r - j) * (2 ^ j - 2 ^ (i : ℕ)) ≤ 2 ^ r - 2 ^ (i : ℕ) := by
    intro i
    rw [Nat.mul_sub, ← pow_add, Nat.sub_add_cancel hj]
    exact Nat.sub_le_sub_left (Nat.le_mul_of_pos_left _ (by positivity)) _
  have h2 : 2 ^ (j * (r - j)) * ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ)) ≤
      ∏ i : Fin j, (2 ^ r - 2 ^ (i : ℕ)) := by
    calc 2 ^ (j * (r - j)) * ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ))
        = ∏ i : Fin j, 2 ^ (r - j) * (2 ^ j - 2 ^ (i : ℕ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← pow_mul, Nat.mul_comm j]
      _ ≤ ∏ i : Fin j, (2 ^ r - 2 ^ (i : ℕ)) := Finset.prod_le_prod fun i _ => hfac i
  rw [← h1] at h2
  exact Nat.le_of_mul_le_mul_right h2 (prod_two_pow_sub_pos j)

/-- **Upper bound** `N₂(r) ≤ 2^{⌊r²/4⌋ + 4}`. -/
theorem numSubspaces_le (r : ℕ) : numSubspaces r ≤ 2 ^ (r * r / 4 + 4) := by
  rw [numSubspaces_eq_sum]
  calc ∑ j ∈ range (r + 1), numSubspacesOfDim r j
      ≤ ∑ j ∈ range (r + 1), 4 * 2 ^ (j * (r - j)) :=
        Finset.sum_le_sum fun j hj => numSubspacesOfDim_le (Nat.lt_succ_iff.1 (mem_range.1 hj))
    _ = 4 * ∑ j ∈ range (r + 1), 2 ^ (j * (r - j)) := by rw [Finset.mul_sum]
    _ ≤ 4 * (4 * 2 ^ (r * r / 4)) := Nat.mul_le_mul_left _ (sum_two_pow_mul_sub_le r)
    _ = 2 ^ (r * r / 4 + 4) := by rw [pow_add]; ring

/-- **Lower bound** `2^{⌊r²/4⌋} ≤ N₂(r)`: the `⌊r/2⌋`-dimensional subspaces already suffice. -/
theorem le_numSubspaces (r : ℕ) : 2 ^ (r * r / 4) ≤ numSubspaces r := by
  rw [mul_self_div_four]
  calc 2 ^ (r / 2 * (r - r / 2)) ≤ numSubspacesOfDim r (r / 2) :=
        pow_le_numSubspacesOfDim (Nat.div_le_self r 2)
    _ ≤ numSubspaces r := Finite.card_subtype_le _

theorem numSubspaces_pos (r : ℕ) : 0 < numSubspaces r :=
  lt_of_lt_of_le (by positivity) (le_numSubspaces r)

/-- The subspaces of a subspace `W` of dimension at most `r` number at most `2^{⌊r²/4⌋ + 4}`. -/
theorem card_submodules_le_two_pow {E : Type*} [AddCommGroup E] [Module F2 E]
    [FiniteDimensional F2 E] (W : Submodule F2 E) {r : ℕ} (h : finrank F2 W ≤ r) :
    Nat.card {U : Submodule F2 E // U ≤ W} ≤ 2 ^ (r * r / 4 + 4) :=
  (card_submodules_le_of_finrank_le W h).trans (numSubspaces_le r)

/-! ## Small values -/

/-- The Gaussian binomial coefficient `|Gr(r, j)| = ∏_{i<j} (2^r - 2^i) / ∏_{i<j} (2^j - 2^i)`. -/
theorem numSubspacesOfDim_eq_div {r j : ℕ} (hj : j ≤ r) :
    numSubspacesOfDim r j =
      (∏ i : Fin j, (2 ^ r - 2 ^ (i : ℕ))) / ∏ i : Fin j, (2 ^ j - 2 ^ (i : ℕ)) :=
  Nat.eq_div_of_mul_eq_left (prod_two_pow_sub_pos j).ne' (numSubspacesOfDim_mul_prod hj)

theorem numSubspaces_zero : numSubspaces 0 = 1 := by
  rw [numSubspaces_eq_sum, Finset.sum_range_one, numSubspacesOfDim_eq_div le_rfl]
  simp

theorem numSubspaces_one : numSubspaces 1 = 2 := by
  rw [numSubspaces_eq_sum, Finset.sum_range_succ, Finset.sum_range_one,
    numSubspacesOfDim_eq_div (by norm_num), numSubspacesOfDim_eq_div le_rfl]
  simp

theorem numSubspaces_two : numSubspaces 2 = 5 := by
  rw [numSubspaces_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    numSubspacesOfDim_eq_div (by norm_num), numSubspacesOfDim_eq_div (by norm_num),
    numSubspacesOfDim_eq_div le_rfl]
  simp [Fin.prod_univ_succ]

end SubspaceConvolution
