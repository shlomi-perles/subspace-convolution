/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Count

/-!
# Three small counting claims of the paper

Write `q = |K|`.

* **Footnote of Section 1.**  Embedding `U ∈ Gr(V, k)` as the indicator vector
  `x_U = (1[L ≤ U])_{L ∈ Gr(V, 1)}` of its lines,
  `‖x_U - x_W‖² = 2 (q^k - q^{dim(U ∩ W)}) / (q - 1)`: `sqDist_lineIndicator` (over `ℤ`, with the
  denominator cleared), `sqDist_lineIndicator_real` (over `ℝ`), `sqDist_lineIndicator_gDist` (in
  terms of the Grassmann distance), and `intersectionKernel_radial` (so intersection kernels are
  radial kernels on these vectors).  The key count is `Misc.card_grass_le`: a subspace `U`
  contains exactly `|Gr(dim U, j)|` subspaces of dimension `j`.
* **Section 5.3, last paragraph.**  The inclusions `L' < L` that raise the dimension by one, with
  `dim L ≤ k`, number `∑_{j=1}^{k} |Gr(n, j)| [j]_q` (`card_inclusions`, `card_inclusions_fin`),
  and for `1 ≤ k ≤ n/2` this is `Θ_q(q^k |Gr(n, k)|)`: `pow_mul_gr_le_sum_inclusions`,
  `sum_inclusions_le`, `card_inclusions_theta`.
* **Introduction.**  The number of cover pairs is `Θ_q(N_q(n) q^{n/2})` (`coverPairs_theta`),
  `q^{n/2} = Θ_q(N^{1/√(log_q N)})` for `N = N_q(n)` (`rpow_inv_sqrt_logb_theta`), hence
  cover pairs `= Θ_q(N^{1 + 1/√(log_q N)})` (`coverPairs_theta_rpow`).

Helper lemmas live in the namespace `SubspaceConvolution.Misc`.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

universe v w

/-! ### Helpers -/

namespace Misc

section Helpers

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local notation "q" => Fintype.card K

theorem two_le_card : 2 ≤ q := Fintype.one_lt_card

/-- The `j`-dimensional subspaces of `V` contained in `U` are the `j`-dimensional subspaces of
`U` (pull back / push forward along `U.subtype`). -/
noncomputable def grassLEEquiv (U : Submodule K V) (j : ℕ) :
    {L : Grass K V j // L.1 ≤ U} ≃ Grass K U j where
  toFun L := ⟨Submodule.comap U.subtype L.1.1, by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_of_le_right L.2]
    exact L.1.2⟩
  invFun M := ⟨⟨Submodule.map U.subtype M.1, by rw [Submodule.finrank_map_subtype_eq]; exact M.2⟩,
    Submodule.map_subtype_le U M.1⟩
  left_inv L := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.map_comap_subtype, inf_of_le_right L.2]
  right_inv M := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective U.injective_subtype M.1

open Classical in
/-- A subspace `U` contains exactly `|Gr(dim U, j)|` subspaces of dimension `j`. -/
theorem card_grass_le (U : Submodule K V) (j : ℕ) :
    Fintype.card {L : Grass K V j // L.1 ≤ U} = gr K (finrank K U) j := by
  rw [Fintype.card_congr (grassLEEquiv U j)]
  exact card_grass rfl j

open Classical in
theorem card_filter_grass_le (U : Submodule K V) (j : ℕ) :
    #(univ.filter fun L : Grass K V j => L.1 ≤ U) = gr K (finrank K U) j := by
  rw [← card_grass_le U j, Fintype.card_subtype]

open Classical in
/-- The same count, phrased over all subspaces. -/
theorem card_filter_submodule_le (U : Submodule K V) (j : ℕ) :
    #(univ.filter fun L : Submodule K V => L ≤ U ∧ finrank K L = j) = gr K (finrank K U) j := by
  rw [← card_grass_le U j, ← Fintype.card_subtype]
  exact Fintype.card_congr
    ((Equiv.subtypeEquivRight fun L => and_comm).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun L : Submodule K V => finrank K L = j)
        (fun L => L ≤ U)).symm)

/-- `[m]_q (q - 1) = q^m - 1` over `ℤ`. -/
theorem gr_one_mul_int (m : ℕ) : (gr K m 1 : ℤ) * ((q : ℤ) - 1) = (q : ℤ) ^ m - 1 := by
  have h := gr_one_mul K m
  have hq : 1 ≤ q := Fintype.card_pos
  have hqm : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  zify [hq, hqm] at h
  exact h

/-- `[m]_q ≤ q^m`. -/
theorem gr_one_le_pow (m : ℕ) : gr K m 1 ≤ q ^ m := by
  have h := gr_one_mul K m
  have hq : 2 ≤ q := two_le_card
  calc gr K m 1 ≤ gr K m 1 * (q - 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ = q ^ m - 1 := h
    _ ≤ q ^ m := Nat.sub_le _ _

open Classical in
/-- Summing a function of the dimension over all subspaces of an `n`-dimensional space. -/
theorem sum_submodule_finrank {n : ℕ} (hV : finrank K V = n) {M : Type*} [AddCommMonoid M]
    (g : ℕ → M) :
    ∑ L : Submodule K V, g (finrank K L) = ∑ j ∈ range (n + 1), gr K n j • g j := by
  rw [← Finset.sum_fiberwise_of_maps_to' (s := univ) (t := range (n + 1))
    (g := fun L : Submodule K V => finrank K L) (fun L _ => by
      rw [mem_range]; have := Submodule.finrank_le L; omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_const, ← card_grass hV j, Fintype.card_subtype]

open Classical in
/-- A subspace `W` of dimension `d ≥ 1` has `|Gr(d, d - 1)| = |Gr(d, 1)| = [d]_q` hyperplanes. -/
theorem card_hyperplanes_le (W : Submodule K V) (hW : 1 ≤ finrank K W) :
    #(univ.filter fun L : Submodule K V => L ≤ W ∧ finrank K W = finrank K L + 1) =
      gr K (finrank K W) 1 := by
  rw [← gr_symm K hW, ← card_filter_submodule_le W]
  congr 1
  ext L
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- `(k - t)(n - (k - t)) ≤ k (n - k)` for `t ≤ k ≤ n / 2`. -/
theorem sub_mul_sub_le {n k t : ℕ} (hkn : 2 * k ≤ n) (ht : t ≤ k) :
    (k - t) * (n - (k - t)) ≤ k * (n - k) := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + t := ⟨k - t, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, n = 2 * a + 2 * t + e := ⟨n - 2 * a - 2 * t, by omega⟩
  have h1 : a + t - t = a := by omega
  have h2 : 2 * a + 2 * t + e - a = a + 2 * t + e := by omega
  have h3 : 2 * a + 2 * t + e - (a + t) = a + t + e := by omega
  rw [h1, h2, h3]
  nlinarith [Nat.zero_le (t * t), Nat.zero_le (t * e)]

/-- `⌊(n+1)²/4⌋ = ⌊n²/4⌋ + ⌈n/2⌉`. -/
theorem succ_mul_succ_div_four (n : ℕ) : (n + 1) * (n + 1) / 4 = n * n / 4 + (n + 1) / 2 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h1 : (2 * m + 1) * (2 * m + 1) = 4 * (m * m + m) + 1 := by ring
    have h2 : 2 * m * (2 * m) = 4 * (m * m) := by ring
    rw [h1, h2]; omega
  · have h1 : (2 * m + 1 + 1) * (2 * m + 1 + 1) = 4 * (m * m + 2 * m + 1) := by ring
    have h2 : (2 * m + 1) * (2 * m + 1) = 4 * (m * m + m) + 1 := by ring
    rw [h1, h2]; omega

/-- `N^{1/√(log_b N)} = b^{√(log_b N)}` for `N > 0`. -/
theorem rpow_one_div_sqrt_logb {b N : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (hN : 0 < N) :
    N ^ (1 / Real.sqrt (Real.logb b N)) = b ^ Real.sqrt (Real.logb b N) := by
  calc N ^ (1 / Real.sqrt (Real.logb b N))
      = (b ^ Real.logb b N) ^ (1 / Real.sqrt (Real.logb b N)) := by
        rw [Real.rpow_logb hb hb1 hN]
    _ = b ^ (Real.logb b N * (1 / Real.sqrt (Real.logb b N))) := by
        rw [Real.rpow_mul hb.le]
    _ = b ^ Real.sqrt (Real.logb b N) := by
        rw [mul_one_div, Real.div_sqrt]

theorem numLE_self_pos (n : ℕ) : 0 < numLE K n n :=
  lt_of_lt_of_le (pow_pos Fintype.card_pos _) (pow_le_numLE_self K n)

end Helpers

end Misc

/-! ### Footnote of Section 1: the indicator embedding of `Gr(V, k)` -/

section Footnote

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local notation "q" => Fintype.card K

open Classical in
/-- **Footnote of Section 1.** Embed `U ∈ Gr(V, k)` as the indicator vector
`x_U = (1[L ≤ U])_{L ∈ Gr(V, 1)}` of the lines it contains.  Then
`‖x_U - x_W‖² = 2 (q^k - q^{dim(U ∩ W)}) / (q - 1)`; here with the denominator cleared. -/
theorem sqDist_lineIndicator {k : ℕ} (U W : Grass K V k) :
    (q - 1 : ℤ) * ∑ L : Grass K V 1,
        ((if L.1 ≤ U.1 then 1 else 0) - (if L.1 ≤ W.1 then 1 else 0) : ℤ) ^ 2 =
      2 * ((q : ℤ) ^ k - (q : ℤ) ^ finrank K (U.1 ⊓ W.1 : Submodule K V)) := by
  have key : ∀ L : Grass K V 1,
      ((if L.1 ≤ U.1 then 1 else 0) - (if L.1 ≤ W.1 then 1 else 0) : ℤ) ^ 2 =
        (if L.1 ≤ U.1 then 1 else 0) + (if L.1 ≤ W.1 then 1 else 0) -
          2 * (if L.1 ≤ U.1 ⊓ W.1 then 1 else 0) := by
    intro L
    by_cases hU : L.1 ≤ U.1 <;> by_cases hW : L.1 ≤ W.1 <;> simp [hU, hW, le_inf_iff]
  rw [Finset.sum_congr rfl (fun L _ => key L), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, Finset.sum_boole,
    Misc.card_filter_grass_le, Misc.card_filter_grass_le, Misc.card_filter_grass_le, U.2, W.2]
  linear_combination (2 : ℤ) * Misc.gr_one_mul_int (K := K) k -
    2 * Misc.gr_one_mul_int (K := K) (finrank K (U.1 ⊓ W.1 : Submodule K V))

open Classical in
/-- The footnote over `ℝ`: `‖x_U - x_W‖² = 2 (q^k - q^{dim(U ∩ W)}) / (q - 1)`. -/
theorem sqDist_lineIndicator_real {k : ℕ} (U W : Grass K V k) :
    ∑ L : Grass K V 1,
        ((if L.1 ≤ U.1 then 1 else 0) - (if L.1 ≤ W.1 then 1 else 0) : ℝ) ^ 2 =
      2 * ((q : ℝ) ^ k - (q : ℝ) ^ finrank K (U.1 ⊓ W.1 : Submodule K V)) / (q - 1) := by
  have hq : (1 : ℝ) < q := by exact_mod_cast Fintype.one_lt_card
  have h := congrArg (fun z : ℤ => (z : ℝ)) (sqDist_lineIndicator U W)
  push_cast at h
  rw [eq_div_iff (by linarith), mul_comm]
  exact h

open Classical in
/-- The footnote in terms of the Grassmann distance `dist(U, W) = k - dim(U ∩ W)`. -/
theorem sqDist_lineIndicator_gDist {k : ℕ} (U W : Grass K V k) :
    (q - 1 : ℤ) * ∑ L : Grass K V 1,
        ((if L.1 ≤ U.1 then 1 else 0) - (if L.1 ≤ W.1 then 1 else 0) : ℤ) ^ 2 =
      2 * ((q : ℤ) ^ k - (q : ℤ) ^ (k - gDist k U W)) := by
  have h : finrank K (U.1 ⊓ W.1 : Submodule K V) ≤ k := by
    have := Submodule.finrank_mono (inf_le_left : U.1 ⊓ W.1 ≤ U.1)
    rw [U.2] at this
    exact this
  have : k - gDist k U W = finrank K (U.1 ⊓ W.1 : Submodule K V) := by unfold gDist; omega
  rw [this]
  exact sqDist_lineIndicator U W

open Classical in
/-- The conclusion of the footnote: an intersection kernel `K(U, W) = a_{dist(U, W)}` is a radial
kernel on the vectors `x_U`, i.e. a function of `‖x_U - x_W‖²`. -/
theorem intersectionKernel_radial {R : Type*} (k : ℕ) (a : ℕ → R) :
    ∃ f : ℤ → R, ∀ U W : Grass K V k, a (gDist k U W) =
      f (∑ L : Grass K V 1,
        ((if L.1 ≤ U.1 then 1 else 0) - (if L.1 ≤ W.1 then 1 else 0) : ℤ) ^ 2) := by
  refine ⟨fun t => if h : ∃ d, d ≤ k ∧ (q - 1 : ℤ) * t = 2 * ((q : ℤ) ^ k - (q : ℤ) ^ (k - d))
    then a h.choose else a 0, fun U W => ?_⟩
  have hex : ∃ d, d ≤ k ∧ (q - 1 : ℤ) * (∑ L : Grass K V 1,
      ((if L.1 ≤ U.1 then 1 else 0) - (if L.1 ≤ W.1 then 1 else 0) : ℤ) ^ 2) =
        2 * ((q : ℤ) ^ k - (q : ℤ) ^ (k - d)) :=
    ⟨gDist k U W, Nat.sub_le _ _, sqDist_lineIndicator_gDist U W⟩
  simp only [dite_eq_left hex]
  congr 1
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h2' := sqDist_lineIndicator_gDist U W
  have h3 : (q : ℤ) ^ (k - gDist k U W) = (q : ℤ) ^ (k - hex.choose) := by linarith
  have h4 : q ^ (k - gDist k U W) = q ^ (k - hex.choose) := by exact_mod_cast h3
  have h5 := Nat.pow_right_injective Misc.two_le_card h4
  have h6 : gDist k U W ≤ k := Nat.sub_le _ _
  simp only at h5
  omega

end Footnote

/-! ### Section 5.3: inclusions processed by the lattice transforms -/

section Inclusions

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local notation "q" => Fintype.card K

open Classical in
/-- **Section 5.3, last paragraph.** The inclusions `L' < L` raising the dimension by one, with
`dim L ≤ k`, number `∑_{j=1}^{k} |Gr(n, j)| [j]_q` (each `j`-space has `[j]_q` hyperplanes). -/
theorem card_inclusions {n : ℕ} (hV : finrank K V = n) (k : ℕ) :
    #(univ.filter fun p : Submodule K V × Submodule K V =>
        p.1 ≤ p.2 ∧ finrank K p.2 = finrank K p.1 + 1 ∧ finrank K p.2 ≤ k) =
      ∑ j ∈ Icc 1 k, gr K n j * gr K j 1 := by
  rw [card_filter, Fintype.sum_prod_type_right]
  have inner : ∀ W : Submodule K V,
      (∑ L : Submodule K V,
          if (L, W).1 ≤ (L, W).2 ∧ finrank K (L, W).2 = finrank K (L, W).1 + 1 ∧
            finrank K (L, W).2 ≤ k then 1 else 0) =
        (fun d => if 1 ≤ d ∧ d ≤ k then gr K d 1 else 0) (finrank K W) := by
    intro W
    simp only
    split_ifs with h
    · rw [← Misc.card_hyperplanes_le W h.1, card_filter]
      refine Finset.sum_congr rfl fun L _ => ?_
      simp only [h.2, and_true]
    · refine Finset.sum_eq_zero fun L _ => ite_eq_right ?_
      rintro ⟨_, h2, h3⟩
      exact h ⟨by omega, h3⟩
  rw [Finset.sum_congr rfl fun W _ => inner W]
  refine (Misc.sum_submodule_finrank hV
    (fun d => if 1 ≤ d ∧ d ≤ k then gr K d 1 else 0)).trans ?_
  simp only [smul_eq_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro j hj
    simp only [mem_filter, mem_range, mem_Icc] at hj ⊢
    omega
  · intro j hj hj'
    simp only [mem_filter, mem_range, mem_Icc, not_and] at hj hj'
    rw [gr_eq_zero_of_lt K (by omega), zero_mul]

open Classical in
/-- `card_inclusions` for `V = K^n`. -/
theorem card_inclusions_fin (n k : ℕ) :
    #(univ.filter fun p : Submodule K (Fin n → K) × Submodule K (Fin n → K) =>
        p.1 ≤ p.2 ∧ finrank K p.2 = finrank K p.1 + 1 ∧ finrank K p.2 ≤ k) =
      ∑ j ∈ Icc 1 k, gr K n j * gr K j 1 :=
  card_inclusions (Module.finrank_fin_fun K) k

/-- **Section 5.3**, lower bound: `q^{k-1} |Gr(n,k)| ≤ ∑_{j=1}^{k} |Gr(n,j)| [j]_q`. -/
theorem pow_mul_gr_le_sum_inclusions {n k : ℕ} (hk : 1 ≤ k) :
    q ^ (k - 1) * gr K n k ≤ ∑ j ∈ Icc 1 k, gr K n j * gr K j 1 := by
  have h1 : q ^ (k - 1) ≤ gr K k 1 := by
    have := pow_le_gr K hk
    rwa [one_mul] at this
  calc q ^ (k - 1) * gr K n k ≤ gr K n k * gr K k 1 := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ h1
    _ ≤ ∑ j ∈ Icc 1 k, gr K n j * gr K j 1 :=
      Finset.single_le_sum (f := fun j => gr K n j * gr K j 1) (fun j _ => Nat.zero_le _)
        (by simp [hk])

/-- **Section 5.3**, upper bound: for `k ≤ n/2`, `∑_{j=1}^{k} |Gr(n,j)| [j]_q ≤ 8 q^k |Gr(n,k)|`
(the terms decay geometrically away from `j = k`). -/
theorem sum_inclusions_le {n k : ℕ} (hkn : 2 * k ≤ n) :
    ∑ j ∈ Icc 1 k, gr K n j * gr K j 1 ≤ 8 * q ^ k * gr K n k := by
  have hq : 2 ≤ q := Misc.two_le_card
  have hre : ∑ j ∈ Icc 1 k, gr K n j * gr K j 1 =
      ∑ t ∈ range k, gr K n (k - t) * gr K (k - t) 1 := by
    refine Finset.sum_nbij' (fun j => k - j) (fun t => k - t) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Icc, mem_range] at hj ⊢; omega
    · intro t ht; simp only [mem_Icc, mem_range] at ht ⊢; omega
    · intro j hj; simp only [mem_Icc] at hj; omega
    · intro t ht; simp only [mem_range] at ht; omega
    · intro j hj
      simp only [mem_Icc] at hj
      have : k - (k - j) = j := by omega
      rw [this]
  have hb : ∀ t < k, gr K n (k - t) * gr K (k - t) 1 * 2 ^ t ≤
      4 * q ^ (k * (n - k)) * q ^ k := by
    intro t ht
    have e1 := gr_le K n (k - t)
    have e2 := Misc.gr_one_le_pow (K := K) (k - t)
    have e3 : 2 ^ t ≤ q ^ t := Nat.pow_le_pow_left hq t
    have e4 : q ^ ((k - t) * (n - (k - t))) * q ^ (k - t) * q ^ t ≤
        q ^ (k * (n - k)) * q ^ k := by
      rw [← pow_add, ← pow_add, ← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      have := Misc.sub_mul_sub_le hkn ht.le
      omega
    calc gr K n (k - t) * gr K (k - t) 1 * 2 ^ t ≤
          (4 * q ^ ((k - t) * (n - (k - t)))) * q ^ (k - t) * q ^ t :=
          Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
      _ = 4 * (q ^ ((k - t) * (n - (k - t))) * q ^ (k - t) * q ^ t) := by ring
      _ ≤ 4 * (q ^ (k * (n - k)) * q ^ k) := Nat.mul_le_mul_left 4 e4
      _ = 4 * q ^ (k * (n - k)) * q ^ k := by ring
  have hg := pow_le_gr K (show k ≤ n by omega)
  rw [hre]
  calc ∑ t ∈ range k, gr K n (k - t) * gr K (k - t) 1 ≤ 2 * (4 * q ^ (k * (n - k)) * q ^ k) :=
        sum_le_two_mul_of_mul_pow_le hb
    _ = 8 * q ^ k * q ^ (k * (n - k)) := by ring
    _ ≤ 8 * q ^ k * gr K n k := Nat.mul_le_mul_left _ hg

open Classical in
/-- **Section 5.3**: for `1 ≤ k ≤ n/2`, the lattice transforms process `Θ_q(q^k N)` inclusions
raising the dimension by one, `N = |Gr(n, k)|`. -/
theorem card_inclusions_theta {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    q ^ (k - 1) * gr K n k ≤
        #(univ.filter fun p : Submodule K (Fin n → K) × Submodule K (Fin n → K) =>
          p.1 ≤ p.2 ∧ finrank K p.2 = finrank K p.1 + 1 ∧ finrank K p.2 ≤ k) ∧
      #(univ.filter fun p : Submodule K (Fin n → K) × Submodule K (Fin n → K) =>
          p.1 ≤ p.2 ∧ finrank K p.2 = finrank K p.1 + 1 ∧ finrank K p.2 ≤ k) ≤
        8 * q ^ k * gr K n k := by
  rw [card_inclusions_fin]
  exact ⟨pow_mul_gr_le_sum_inclusions hk, sum_inclusions_le hkn⟩

end Inclusions

/-! ### Introduction: cover pairs and `N^{1/√(log_q N)}` -/

section Asymptotics

variable (K : Type w) [Field K] [Fintype K]

local notation "q" => Fintype.card K

/-- **Introduction**: the number of cover pairs `U < W`, `dim W = dim U + 1`, is
`Θ_q(N_q(n) q^{n/2})`. -/
theorem coverPairs_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n : ℕ, 1 ≤ n →
      c₁ * (numLE K n n : ℝ) * (q : ℝ) ^ ((n : ℝ) / 2) ≤ (coverPairs K n : ℝ) ∧
      (coverPairs K n : ℝ) ≤ c₂ * (numLE K n n : ℝ) * (q : ℝ) ^ ((n : ℝ) / 2) := by
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (Misc.two_le_card (K := K))
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  refine ⟨1 / (16 * q), 64, by positivity, by norm_num, fun n hn => ⟨?_, ?_⟩⟩
  · have hexp : (n : ℝ) / 2 ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast (by omega : n ≤ (n + 1) / 2 * 2)
    have h1 : (q : ℝ) ^ ((n : ℝ) / 2) ≤ (q : ℝ) ^ ((n + 1) / 2) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hq1 hexp
    have hNr : (numLE K n n : ℝ) ≤ 16 * (q : ℝ) ^ (n * n / 4) := by
      exact_mod_cast numLE_self_le K n
    have hCr : (q : ℝ) ^ ((n + 1) * (n + 1) / 4 - 1) ≤ (coverPairs K n : ℝ) := by
      exact_mod_cast pow_le_coverPairs K hn
    have hE : (q : ℝ) ^ (n * n / 4) * (q : ℝ) ^ ((n + 1) / 2) =
        (q : ℝ) ^ ((n + 1) * (n + 1) / 4 - 1) * q := by
      rw [← pow_add, ← pow_succ, Misc.succ_mul_succ_div_four]
      congr 1
      omega
    calc 1 / (16 * (q : ℝ)) * (numLE K n n : ℝ) * (q : ℝ) ^ ((n : ℝ) / 2)
        ≤ 1 / (16 * (q : ℝ)) * (16 * (q : ℝ) ^ (n * n / 4)) * (q : ℝ) ^ ((n + 1) / 2) := by
          gcongr
      _ = (q : ℝ) ^ ((n + 1) * (n + 1) / 4 - 1) := by
          have hq' : (q : ℝ) ≠ 0 := hq0.ne'
          calc 1 / (16 * (q : ℝ)) * (16 * (q : ℝ) ^ (n * n / 4)) * (q : ℝ) ^ ((n + 1) / 2)
              = ((q : ℝ) ^ (n * n / 4) * (q : ℝ) ^ ((n + 1) / 2)) / q := by field_simp
            _ = _ := by rw [hE, mul_div_assoc, div_self hq', mul_one]
      _ ≤ (coverPairs K n : ℝ) := hCr
  · have hexp : (((n / 2 : ℕ)) : ℝ) ≤ (n : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast (by omega : n / 2 * 2 ≤ n)
    have h1 : (q : ℝ) ^ (n / 2) ≤ (q : ℝ) ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hq1 hexp
    have hNr : (q : ℝ) ^ (n * n / 4) ≤ (numLE K n n : ℝ) := by
      exact_mod_cast pow_le_numLE_self K n
    have hCr : (coverPairs K n : ℝ) ≤ 64 * (q : ℝ) ^ ((n + 1) * (n + 1) / 4 - 1) := by
      exact_mod_cast coverPairs_le K n
    have hE : (q : ℝ) ^ ((n + 1) * (n + 1) / 4 - 1) ≤
        (q : ℝ) ^ (n * n / 4) * (q : ℝ) ^ (n / 2) := by
      rw [← pow_add]
      apply pow_le_pow_right₀ hq1
      rw [Misc.succ_mul_succ_div_four]
      omega
    calc (coverPairs K n : ℝ) ≤ 64 * (q : ℝ) ^ ((n + 1) * (n + 1) / 4 - 1) := hCr
      _ ≤ 64 * ((q : ℝ) ^ (n * n / 4) * (q : ℝ) ^ (n / 2)) := by gcongr
      _ ≤ 64 * ((numLE K n n : ℝ) * (q : ℝ) ^ ((n : ℝ) / 2)) := by gcongr
      _ = 64 * (numLE K n n : ℝ) * (q : ℝ) ^ ((n : ℝ) / 2) := by ring

/-- **Introduction**: `q^{n/2} = Θ_q(N^{1/√(log_q N)})` for `N = N_q(n)`, so that
`Θ_q(N q^{n/2}) = Θ_q(N^{1 + 1/√(log_q N)})`.  (With `L = log_q N ∈ [⌊n²/4⌋, ⌊n²/4⌋ + 4]`,
`N^{1/√L} = q^{√L}` and `n/2 - 1 ≤ √L ≤ n/2 + 2`.) -/
theorem rpow_inv_sqrt_logb_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n : ℕ, 1 ≤ n →
      c₁ * (q : ℝ) ^ ((n : ℝ) / 2) ≤
          (numLE K n n : ℝ) ^ (1 / Real.sqrt (Real.logb q (numLE K n n))) ∧
      (numLE K n n : ℝ) ^ (1 / Real.sqrt (Real.logb q (numLE K n n))) ≤
          c₂ * (q : ℝ) ^ ((n : ℝ) / 2) := by
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (Misc.two_le_card (K := K))
  have hq1 : (1 : ℝ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  refine ⟨1 / q, (q : ℝ) ^ 2, by positivity, by positivity, fun n _ => ?_⟩
  have hNlo : (q : ℝ) ^ (n * n / 4) ≤ (numLE K n n : ℝ) := by
    exact_mod_cast pow_le_numLE_self K n
  have hNhi : (numLE K n n : ℝ) ≤ (q : ℝ) ^ (n * n / 4 + 4) := by
    have h16 : (16 : ℝ) ≤ (q : ℝ) ^ 4 := by
      have : (2 : ℝ) ^ 4 ≤ (q : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hq 4
      norm_num at this
      linarith
    calc (numLE K n n : ℝ) ≤ 16 * (q : ℝ) ^ (n * n / 4) := by exact_mod_cast numLE_self_le K n
      _ ≤ (q : ℝ) ^ 4 * (q : ℝ) ^ (n * n / 4) := by gcongr
      _ = (q : ℝ) ^ (n * n / 4 + 4) := by rw [pow_add, mul_comm]
  have hN0 : (0 : ℝ) < numLE K n n := by exact_mod_cast Misc.numLE_self_pos (K := K) n
  have hLlo : (((n * n / 4 : ℕ)) : ℝ) ≤ Real.logb q (numLE K n n) := by
    rw [Real.le_logb_iff_rpow_le hq1 hN0, Real.rpow_natCast]; exact hNlo
  have hLhi : Real.logb q (numLE K n n) ≤ (((n * n / 4 + 4 : ℕ)) : ℝ) := by
    rw [Real.logb_le_iff_le_rpow hq1 hN0, Real.rpow_natCast]; exact hNhi
  have hm : ((n : ℝ) * n) ≤ 4 * (((n * n / 4 : ℕ)) : ℝ) + 3 := by
    have : n * n ≤ 4 * (n * n / 4) + 3 := by omega
    exact_mod_cast this
  have hm' : 4 * (((n * n / 4 : ℕ)) : ℝ) ≤ (n : ℝ) * n := by
    have : 4 * (n * n / 4) ≤ n * n := by omega
    exact_mod_cast this
  have hL0 : 0 ≤ Real.logb q (numLE K n n) := le_trans (Nat.cast_nonneg _) hLlo
  have hs_lo : (n : ℝ) / 2 - 1 ≤ Real.sqrt (Real.logb q (numLE K n n)) := by
    rcases le_or_gt ((n : ℝ) / 2 - 1) 0 with h | h
    · exact h.trans (Real.sqrt_nonneg _)
    · rw [Real.le_sqrt h.le hL0]
      have hn2 : (2 : ℝ) ≤ n := by linarith
      nlinarith
  have hs_hi : Real.sqrt (Real.logb q (numLE K n n)) ≤ (n : ℝ) / 2 + 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    push_cast at hLhi
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  rw [Misc.rpow_one_div_sqrt_logb hq0 hq1.ne' hN0]
  constructor
  · calc 1 / (q : ℝ) * (q : ℝ) ^ ((n : ℝ) / 2) = (q : ℝ) ^ ((n : ℝ) / 2 - 1) := by
          rw [Real.rpow_sub hq0, Real.rpow_one]; ring
      _ ≤ (q : ℝ) ^ Real.sqrt (Real.logb q (numLE K n n)) :=
          Real.rpow_le_rpow_of_exponent_le hq1.le hs_lo
  · calc (q : ℝ) ^ Real.sqrt (Real.logb q (numLE K n n)) ≤ (q : ℝ) ^ ((n : ℝ) / 2 + 2) :=
          Real.rpow_le_rpow_of_exponent_le hq1.le hs_hi
      _ = (q : ℝ) ^ 2 * (q : ℝ) ^ ((n : ℝ) / 2) := by
          rw [Real.rpow_add hq0, Real.rpow_two]; ring

/-- **Introduction**: the number of cover pairs is
`Θ_q(N_q(n)^{1 + 1/√(log_q N_q(n))})`. -/
theorem coverPairs_theta_rpow :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n : ℕ, 1 ≤ n →
      c₁ * (numLE K n n : ℝ) ^ (1 + 1 / Real.sqrt (Real.logb q (numLE K n n))) ≤
          (coverPairs K n : ℝ) ∧
      (coverPairs K n : ℝ) ≤
          c₂ * (numLE K n n : ℝ) ^ (1 + 1 / Real.sqrt (Real.logb q (numLE K n n))) := by
  obtain ⟨a₁, a₂, ha₁, ha₂, ha⟩ := coverPairs_theta K
  obtain ⟨b₁, b₂, hb₁, hb₂, hb⟩ := rpow_inv_sqrt_logb_theta K
  refine ⟨a₁ / b₂, a₂ / b₁, by positivity, by positivity, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := ha n hn
  obtain ⟨h3, h4⟩ := hb n hn
  have hN0 : (0 : ℝ) < numLE K n n := by exact_mod_cast Misc.numLE_self_pos (K := K) n
  rw [Real.rpow_add hN0, Real.rpow_one]
  set N : ℝ := (numLE K n n : ℝ)
  set P : ℝ := (q : ℝ) ^ ((n : ℝ) / 2)
  set S : ℝ := N ^ (1 / Real.sqrt (Real.logb q N))
  constructor
  · calc a₁ / b₂ * (N * S) ≤ a₁ / b₂ * (N * (b₂ * P)) := by gcongr
      _ = a₁ * N * P := by field_simp
      _ ≤ _ := h1
  · calc (coverPairs K n : ℝ) ≤ a₂ * N * P := h2
      _ = a₂ / b₁ * (N * (b₁ * P)) := by field_simp
      _ ≤ a₂ / b₁ * (N * S) := by gcongr

end Asymptotics

end SubspaceConvolution
