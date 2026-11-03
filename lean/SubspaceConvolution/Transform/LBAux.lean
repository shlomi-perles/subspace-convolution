/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Count

/-!
# Counting subspaces in an interval; the `q`-Vandermonde identity

Helpers for Appendices D and F (`Transform/Mobius.lean`, `Transform/LowerBound.lean`).

* `finrank_map_mkQ_add` — rank–nullity for the image of a superspace of `U` in `V ⧸ U`.
* `card_super` — superspaces `L ≥ U` with `dim L = dim U + j` correspond to `j`-dimensional
  subspaces of `V ⧸ U`: there are `|Gr(n - dim U, j)|` of them.
* `card_interval` — the interval `U ≤ L ≤ W`, `dim L = dim U + j`, has `|Gr(dim W - dim U, j)|`
  elements; `sum_interval` groups a sum over an interval by dimension.
* `card_superGrass` — `#{W' ∈ Gr(V, b) : S ≤ W'} = |Gr(n - dim S, b - dim S)|`.
* `gr_vandermonde` — the `q`-Vandermonde identity
  `|Gr(m+t, r)| = ∑_j |Gr(t, j)| |Gr(m, r-j)| q^{j(m+j-r)}` (from equation (25)).

Everything lives in the namespace `SubspaceConvolution.LBAux`.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

namespace LBAux

section Interval

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Rank–nullity for the image of a superspace of `U` in the quotient by `U`. -/
theorem finrank_map_mkQ_add {U L : Submodule K V} (h : U ≤ L) :
    finrank K (L.map U.mkQ) + finrank K U = finrank K L := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (U.mkQ ∘ₗ L.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, Submodule.ker_mkQ] at h1
  rw [← h1, (Submodule.comapSubtypeEquivOfLe h).finrank_eq]

theorem finrank_comap_mkQ (U : Submodule K V) (M : Submodule K (V ⧸ U)) :
    finrank K (M.comap U.mkQ) = finrank K M + finrank K U := by
  have := finrank_map_mkQ_add (Submodule.le_comap_mkQ U M)
  rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective U)] at this
  omega

/-- Superspaces of `U` of dimension `dim U + j` are the `j`-dimensional subspaces of `V ⧸ U`. -/
noncomputable def superEquiv (U : Submodule K V) (j : ℕ) :
    {L : Submodule K V // U ≤ L ∧ finrank K L = finrank K U + j} ≃ Grass K (V ⧸ U) j where
  toFun L := ⟨L.1.map U.mkQ, by have := finrank_map_mkQ_add L.2.1; have := L.2.2; omega⟩
  invFun M := ⟨M.1.comap U.mkQ, Submodule.le_comap_mkQ U M.1, by
    rw [finrank_comap_mkQ, M.2]; ring⟩
  left_inv L := by
    apply Subtype.ext
    simp only [Submodule.comap_map_mkQ, sup_eq_right.2 L.2.1]
  right_inv M := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective U) M.1

open Classical in
/-- The number of superspaces of `U` of dimension `dim U + j`. -/
theorem card_super (U : Submodule K V) (j : ℕ) :
    #(univ.filter fun L : Submodule K V => U ≤ L ∧ finrank K L = finrank K U + j) =
      gr K (finrank K V - finrank K U) j := by
  rw [← card_grass (V := V ⧸ U) (Submodule.finrank_quotient U) j, ← Fintype.card_subtype]
  exact Fintype.card_congr (superEquiv U j)

/-- Restricting an interval `[U, W]` of subspaces to the subspaces of `W`. -/
noncomputable def restrictEquiv {U W : Submodule K V} (hUW : U ≤ W) (j : ℕ) :
    {L : Submodule K V // U ≤ L ∧ L ≤ W ∧ finrank K L = finrank K U + j} ≃
      {L : Submodule K W // U.comap W.subtype ≤ L ∧
        finrank K L = finrank K (U.comap W.subtype) + j} where
  toFun L := ⟨L.1.comap W.subtype, Submodule.comap_mono L.2.1, by
    rw [(Submodule.comapSubtypeEquivOfLe L.2.2.1).finrank_eq,
      (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq]
    exact L.2.2.2⟩
  invFun L := ⟨L.1.map W.subtype, by
    have h := Submodule.map_mono (f := W.subtype) L.2.1
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hUW] at h,
    Submodule.map_subtype_le W L.1, by
    rw [Submodule.finrank_map_subtype_eq, L.2.2, (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq]⟩
  left_inv L := by
    apply Subtype.ext
    simp only [Submodule.map_comap_subtype, inf_eq_right.2 L.2.2.1]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective (Submodule.injective_subtype W) L.1

open Classical in
/-- The number of subspaces `U ≤ L ≤ W` with `dim L = dim U + j` is `|Gr(dim W - dim U, j)|`. -/
theorem card_interval {U W : Submodule K V} (hUW : U ≤ W) (j : ℕ) :
    #(univ.filter fun L : Submodule K V => U ≤ L ∧ L ≤ W ∧ finrank K L = finrank K U + j) =
      gr K (finrank K W - finrank K U) j := by
  have h := card_super (U.comap W.subtype) j
  rw [← Fintype.card_subtype] at h
  rw [← Fintype.card_subtype, Fintype.card_congr (restrictEquiv hUW j), h,
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq]

open Classical in
/-- A sum over the interval `[U, W]`, grouped by dimension. -/
theorem sum_interval {M : Type*} [AddCommMonoid M] {U W : Submodule K V} (hUW : U ≤ W)
    (f : ℕ → M) :
    ∑ L ∈ univ.filter (fun L : Submodule K V => U ≤ L ∧ L ≤ W), f (finrank K L - finrank K U) =
      ∑ j ∈ range (finrank K W - finrank K U + 1),
        gr K (finrank K W - finrank K U) j • f j := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun L : Submodule K V => finrank K L - finrank K U)
    (t := range (finrank K W - finrank K U + 1))]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f j) (fun L hL => by rw [(mem_filter.1 hL).2]),
      Finset.sum_const, filter_filter, ← card_interval hUW j]
    congr 2
    ext L
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have := Submodule.finrank_mono h1
      exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, by omega⟩
  · intro L hL
    simp only [mem_filter, mem_univ, true_and] at hL
    have := Submodule.finrank_mono hL.2
    simp only [mem_range]
    omega

open Classical in
/-- Sums over the subspaces of `T`, grouped by dimension. -/
theorem sum_le_eq_sum_range {M : Type*} [AddCommMonoid M] (T : Submodule K V) (f : ℕ → M) :
    ∑ L ∈ univ.filter (fun L : Submodule K V => L ≤ T), f (finrank K L) =
      ∑ j ∈ range (finrank K T + 1), gr K (finrank K T) j • f j := by
  have h := sum_interval (bot_le : (⊥ : Submodule K V) ≤ T) f
  simp only [finrank_bot, Nat.sub_zero, bot_le, true_and] at h
  exact h

open Classical in
/-- The number of `b`-dimensional superspaces of `S`. -/
theorem card_superGrass (S : Submodule K V) {b : ℕ} (hb : finrank K S ≤ b) :
    #(univ.filter fun W : Grass K V b => S ≤ W.1) =
      gr K (finrank K V - finrank K S) (b - finrank K S) := by
  rw [← card_super S (b - finrank K S)]
  refine Finset.card_bij (fun W _ => W.1) ?_ ?_ ?_
  · intro W hW
    simp only [mem_filter, mem_univ, true_and] at hW ⊢
    exact ⟨hW, by rw [W.2]; omega⟩
  · intro W₁ _ W₂ _ h
    exact Subtype.ext h
  · intro L hL
    simp only [mem_filter, mem_univ, true_and] at hL
    exact ⟨⟨L, by show finrank K L = b; omega⟩, by simpa using hL.1, rfl⟩

end Interval

/-! ### The `q`-Vandermonde identity -/

section Vandermonde

variable (K : Type*) [Field K] [Fintype K]

local notation "q" => Fintype.card K

/-- The `q`-Vandermonde identity, from equation (25) by induction on `t`. -/
theorem gr_vandermonde (m t r : ℕ) :
    gr K (m + t) r =
      ∑ j ∈ range (r + 1), gr K t j * gr K m (r - j) * q ^ (j * (m + j - r)) := by
  induction t generalizing r with
  | zero =>
    rw [Finset.sum_range_succ']
    simp [gr_zero_right, gr_eq_zero_of_lt K (Nat.succ_pos _)]
  | succ t ih =>
    cases r with
    | zero => simp [gr_zero_right]
    | succ r =>
      have key : ∀ i ∈ range (r + 1),
          q ^ (m + t - r) * (gr K t i * gr K m (r - i) * q ^ (i * (m + i - r))) =
            q ^ (t - i) * gr K t i * gr K m (r - i) * q ^ ((i + 1) * (m + (i + 1) - (r + 1))) := by
        intro i hi
        rcases Nat.lt_or_ge t i with h1 | h1
        · simp [gr_eq_zero_of_lt K h1]
        rcases Nat.lt_or_ge m (r - i) with h2 | h2
        · simp [gr_eq_zero_of_lt K h2]
        have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
        obtain ⟨X, hX⟩ : ∃ X, m + i - r = X := ⟨_, rfl⟩
        have e1 : m + (i + 1) - (r + 1) = X := by omega
        have e2 : m + t - r = (t - i) + X := by omega
        rw [e1, hX, e2]
        ring
      rw [show m + (t + 1) = (m + t) + 1 by ring, gr_succ_succ, ih (r + 1), ih r, mul_sum,
        sum_congr rfl key, Finset.sum_range_succ' _ (r + 1), Finset.sum_range_succ' _ (r + 1)]
      simp only [gr_succ_succ, gr_zero_right, add_mul, sum_add_distrib]
      have e3 : ∀ i, r + 1 - (i + 1) = r - i := fun i => by omega
      simp only [e3]
      ring

end Vandermonde

end LBAux

end SubspaceConvolution
