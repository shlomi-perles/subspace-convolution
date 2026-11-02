/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Grassmann
import SubspaceConvolution.Transform.Count

/-!
# Counting subspaces in intervals (helpers for Appendix E)

* `qnum q m = [m]_q = 1 + q + ⋯ + q^{m-1}` and its identities; `gr_one_eq_qnum`
  (`|Gr(m, 1)| = [m]`), `gr_pred_eq_qnum` (`|Gr(m, m-1)| = [m]`).
* `card_interval` — the number of `s`-dimensional `H` with `A ≤ H ≤ B` is
  `|Gr(dim B - dim A, s - dim A)|` (through the quotient `B / A`); special cases
  `card_grass_le_sub` (subspaces of `X`) and `card_grass_ge` (superspaces of `X`).
* `card_adj` — for `U ∈ Gr(V, k)`, `L ∈ Gr(V, j)`:
  `#{W ~ U : L ≤ W} = [L ≤ U] [k-j] q [n-k] + [dim(U ∩ L) = j - 1] [k-j+1]`.
-/

open Finset Module

set_option linter.unusedSectionVars false

universe u v w

namespace SubspaceConvolution

/-! ### Gaussian integers `[m]_q` -/

/-- `[m]_q = 1 + q + ⋯ + q^{m-1}`. -/
def qnum (q m : ℕ) : ℕ := ∑ i ∈ range m, q ^ i

@[simp] theorem qnum_zero (q : ℕ) : qnum q 0 = 0 := by simp [qnum]

@[simp] theorem qnum_one (q : ℕ) : qnum q 1 = 1 := by simp [qnum]

theorem qnum_add (q a b : ℕ) : qnum q (a + b) = qnum q a + q ^ a * qnum q b := by
  unfold qnum
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp [pow_add]

theorem qnum_succ (q m : ℕ) : qnum q (m + 1) = qnum q m + q ^ m := by
  rw [qnum_add, qnum_one, mul_one]

theorem qnum_succ' (q m : ℕ) : qnum q (m + 1) = 1 + q * qnum q m := by
  rw [add_comm m 1, qnum_add, qnum_one, pow_one]

theorem qnum_mul_add_one {q : ℕ} (hq : 1 ≤ q) (m : ℕ) : qnum q m * (q - 1) + 1 = q ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : q ^ m * (q - 1) + q ^ m = q ^ m * q := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel hq]
    calc qnum q (m + 1) * (q - 1) + 1 = (qnum q m * (q - 1) + 1) + q ^ m * (q - 1) := by
          rw [qnum_succ]; ring
      _ = q ^ (m + 1) := by rw [ih, add_comm, h, pow_succ]

theorem one_le_qnum {q m : ℕ} (hm : 1 ≤ m) : 1 ≤ qnum q m := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [qnum_succ']; omega

section GrValues

variable (K : Type w) [Field K] [Fintype K]

local notation "q" => Fintype.card K

theorem one_lt_card_field : 1 < q := Fintype.one_lt_card

/-- `|Gr(m, 1)| = [m]_q`. -/
theorem gr_one_eq_qnum (m : ℕ) : gr K m 1 = qnum q m := by
  have h1 := gr_one_mul K m
  have h2 := qnum_mul_add_one (one_lt_card_field K).le m
  have hq : 0 < q - 1 := by have := one_lt_card_field K; omega
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h1]; omega

/-- `|Gr(m, m - 1)| = [m]_q` for `m ≥ 1`. -/
theorem gr_pred_eq_qnum {m : ℕ} (hm : 1 ≤ m) : gr K m (m - 1) = qnum q m := by
  rw [gr_symm K hm, gr_one_eq_qnum]

end GrValues

/-! ### Subspaces in an interval -/

section Interval

variable {K : Type w} [Field K] [Fintype K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

open Classical

theorem card_filter_grass (P : Submodule K V → Prop) (k : ℕ) :
    #(univ.filter fun W : Grass K V k => P W.1) =
      #(univ.filter fun H : Submodule K V => P H ∧ finrank K H = k) := by
  refine Finset.card_bij (fun W _ => W.1) ?_ ?_ ?_
  · intro W hW
    simp only [mem_filter, mem_univ, true_and] at hW ⊢
    exact ⟨hW, W.2⟩
  · intro W₁ _ W₂ _ h; exact Subtype.ext h
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    exact ⟨⟨H, hH.2⟩, by simpa using hH.1, rfl⟩

theorem finrank_map_mkQ_add {p p' : Submodule K V} (h : p ≤ p') :
    finrank K ↥(p'.map p.mkQ) + finrank K p = finrank K p' := by
  have := LinearMap.finrank_range_add_finrank_ker (p.mkQ ∘ₗ p'.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
    Submodule.ker_mkQ] at this
  rw [← this, (Submodule.comapSubtypeEquivOfLe h).finrank_eq]

/-- The interval `[A, B]` in dimension `s` is `Gr(B / A, s - dim A)`. -/
noncomputable def intervalEquiv (A B : Submodule K V) (hAB : A ≤ B) (s : ℕ)
    (hs : finrank K A ≤ s) :
    {H : Submodule K V // A ≤ H ∧ H ≤ B ∧ finrank K H = s} ≃
      Grass K (↥B ⧸ A.comap B.subtype) (s - finrank K A) where
  toFun H := ⟨(H.1.comap B.subtype).map (A.comap B.subtype).mkQ, by
    show finrank K _ = s - finrank K A
    have h1 := finrank_map_mkQ_add
      (Submodule.comap_mono H.2.1 : A.comap B.subtype ≤ H.1.comap B.subtype)
    rw [(Submodule.comapSubtypeEquivOfLe H.2.2.1).finrank_eq,
      (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq, H.2.2.2] at h1
    omega⟩
  invFun S := ⟨(S.1.comap (A.comap B.subtype).mkQ).map B.subtype, by
    have hA' : A.comap B.subtype ≤ S.1.comap (A.comap B.subtype).mkQ := fun y hy => by
      rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hy]
      exact zero_mem _
    refine ⟨fun x hx => ?_, Submodule.map_subtype_le _ _, ?_⟩
    · exact Submodule.mem_map.2 ⟨⟨x, hAB hx⟩, hA' (by simpa using hx), rfl⟩
    · rw [Submodule.finrank_map_subtype_eq]
      have h1 := finrank_map_mkQ_add hA'
      rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _),
        (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq] at h1
      have h2 : finrank K S.1 = s - finrank K A := S.2
      omega⟩
  left_inv H := by
    apply Subtype.ext
    dsimp only
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono H.2.1),
      Submodule.map_comap_subtype, inf_eq_right.2 H.2.2.1]
  right_inv S := by
    apply Subtype.ext
    dsimp only
    rw [Submodule.comap_map_eq_of_injective B.injective_subtype,
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _)]

/-- **Counting an interval**: `#{H : A ≤ H ≤ B, dim H = s} = |Gr(dim B - dim A, s - dim A)|`. -/
theorem card_interval {A B : Submodule K V} (hAB : A ≤ B) (s : ℕ) :
    #(univ.filter fun H : Submodule K V => A ≤ H ∧ H ≤ B ∧ finrank K H = s) =
      if finrank K A ≤ s then gr K (finrank K B - finrank K A) (s - finrank K A) else 0 := by
  split_ifs with hs
  · rw [← Fintype.card_subtype, Fintype.card_congr (intervalEquiv A B hAB s hs)]
    apply card_grass
    have := Submodule.finrank_quotient_add_finrank (A.comap B.subtype)
    rw [(Submodule.comapSubtypeEquivOfLe hAB).finrank_eq] at this
    omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro H - ⟨hAH, -, hH⟩
    exact hs (hH ▸ Submodule.finrank_mono hAH)

/-- The `s`-dimensional subspaces of `X`. -/
theorem card_grass_le_sub (X : Submodule K V) (s : ℕ) :
    #(univ.filter fun M : Grass K V s => M.1 ≤ X) = gr K (finrank K X) s := by
  rw [card_filter_grass (fun H => H ≤ X)]
  have := card_interval (bot_le : (⊥ : Submodule K V) ≤ X) s
  rw [finrank_bot, ite_eq_left (Nat.zero_le _), Nat.sub_zero, Nat.sub_zero] at this
  rw [← this]
  congr 1
  exact Finset.filter_congr fun H _ => by simp

/-- The `k`-dimensional superspaces of `X`. -/
theorem card_grass_ge (X : Submodule K V) (k : ℕ) :
    #(univ.filter fun W : Grass K V k => X ≤ W.1) =
      if finrank K X ≤ k then gr K (finrank K V - finrank K X) (k - finrank K X) else 0 := by
  rw [card_filter_grass (fun H => X ≤ H)]
  have := card_interval (le_top : X ≤ ⊤) k
  rw [finrank_top] at this
  rw [← this]
  congr 1
  exact Finset.filter_congr fun H _ => by simp

/-! ### Neighbours containing a fixed subspace -/

/-- The fibre of `W ↦ U ∩ W` over a hyperplane `H` of `U`. -/
theorem adj_fiber {k : ℕ} (hk : 1 ≤ k) (U : Grass K V k) (L : Submodule K V) {H : Submodule K V}
    (hHU : H ≤ U.1) (hH : finrank K H = k - 1) :
    ((univ.filter fun W : Grass K V k => (grassGraph k).Adj U W ∧ L ≤ W.1).filter
        fun W => U.1 ⊓ W.1 = H) = (univ.filter fun W : Grass K V k => H ⊔ L ≤ W.1).erase U := by
  ext W
  simp only [mem_filter, mem_erase, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hadj, hLW⟩, hUW⟩
    exact ⟨hadj.1.symm, sup_le (hUW ▸ inf_le_right) hLW⟩
  · rintro ⟨hWU, hHLW⟩
    have hHW : H ≤ U.1 ⊓ W.1 := le_inf hHU (le_sup_left.trans hHLW)
    have hlt : U.1 ⊓ W.1 < U.1 :=
      lt_of_le_of_ne inf_le_left fun h => hWU (grass_eq_of_le (inf_eq_left.1 h)).symm
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_mono hHW
    rw [finrank_grass] at h1
    have h3 : finrank K H = finrank K ↥(U.1 ⊓ W.1) := by omega
    have hEq := Submodule.eq_of_le_of_finrank_eq hHW h3
    exact ⟨⟨⟨fun h => hWU h.symm, by rw [← hEq]; omega⟩, le_sup_right.trans hHLW⟩, hEq.symm⟩

/-- **Neighbours of `U` containing `L`**:
`#{W ~ U : L ≤ W} = [L ≤ U] [k-j] q [n-k] + [dim(U ∩ L) + 1 = j] [k+1-j]`. -/
theorem card_adj {k j : ℕ} (U : Grass K V k) (L : Grass K V j) (hjk : j ≤ k) :
    #(univ.filter fun W : Grass K V k => (grassGraph k).Adj U W ∧ L.1 ≤ W.1) =
      (if L.1 ≤ U.1 then
        qnum (Fintype.card K) (k - j) * (Fintype.card K * qnum (Fintype.card K) (finrank K V - k))
        else 0) +
      (if finrank K ↥(U.1 ⊓ L.1) + 1 = j then qnum (Fintype.card K) (k + 1 - j) else 0) := by
  have hkn : k ≤ finrank K V := le_finrank_of_grass U
  have hU := finrank_grass U
  have hL := finrank_grass L
  set t := finrank K ↥(U.1 ⊓ L.1) with ht
  have htj : t ≤ j := by rw [← hL]; exact Submodule.finrank_mono inf_le_right
  have htk : t ≤ k := by rw [← hU]; exact Submodule.finrank_mono inf_le_left
  have hLU : L.1 ≤ U.1 ↔ t = j := by
    constructor
    · intro h; rw [ht, inf_eq_right.2 h, hL]
    · intro h
      exact inf_eq_right.1 (Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [← ht, h, hL]))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hj : j = 0 := by omega
    subst hj
    have h0 : (univ.filter fun W : Grass K V 0 => (grassGraph 0).Adj U W ∧ L.1 ≤ W.1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro W - ⟨⟨-, h⟩, -⟩
      omega
    rw [h0, Finset.card_empty]
    simp
  -- the hyperplanes of `U` containing `U ∩ L`
  set T := univ.filter fun H : Submodule K V => U.1 ⊓ L.1 ≤ H ∧ H ≤ U.1 ∧ finrank K H = k - 1
    with hT
  have hTcard : #T = if t ≤ k - 1 then qnum (Fintype.card K) (k - t) else 0 := by
    rw [hT, card_interval (inf_le_left : U.1 ⊓ L.1 ≤ U.1), hU, ← ht]
    by_cases h : t ≤ k - 1
    · rw [ite_eq_left h, ite_eq_left h, show k - 1 - t = (k - t) - 1 by omega]
      exact gr_pred_eq_qnum K (by omega)
    · rw [ite_eq_right h, ite_eq_right h]
  -- the size of each fibre
  set c : ℕ := if t = j then Fintype.card K * qnum (Fintype.card K) (finrank K V - k)
    else if t + 1 = j then 1 else 0 with hc
  have hfib : ∀ H ∈ T,
      #((univ.filter fun W : Grass K V k => (grassGraph k).Adj U W ∧ L.1 ≤ W.1).filter
        fun W => U.1 ⊓ W.1 = H) = c := by
    intro H hHT
    simp only [hT, mem_filter, mem_univ, true_and] at hHT
    obtain ⟨hH1, hH2, hH3⟩ := hHT
    rw [adj_fiber hk U L.1 hH2 hH3]
    have hHL : H ⊓ L.1 = U.1 ⊓ L.1 :=
      le_antisymm (inf_le_inf_right L.1 hH2) (le_inf hH1 inf_le_right)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq H L.1
    rw [hHL, ← ht, hH3, hL] at hdim
    have hcard := card_grass_ge (H ⊔ L.1) k
    by_cases htj' : t = j
    · -- `L ≤ U`: `H ⊔ L = H`
      have hsup : H ⊔ L.1 ≤ U.1 := sup_le hH2 (hLU.2 htj')
      rw [Finset.card_erase_of_mem (by simpa using hsup), hcard,
        ite_eq_left (show finrank K ↥(H ⊔ L.1) ≤ k by omega),
        show finrank K V - finrank K ↥(H ⊔ L.1) = (finrank K V - k) + 1 by omega,
        show k - finrank K ↥(H ⊔ L.1) = 1 by omega, gr_one_eq_qnum, qnum_succ', hc,
        ite_eq_left htj']
      omega
    · have hsup : ¬ H ⊔ L.1 ≤ U.1 := fun h => htj' (hLU.1 (le_sup_right.trans h))
      rw [Finset.erase_eq_of_notMem (by simpa using hsup), hcard, hc, ite_eq_right htj']
      by_cases ht1 : t + 1 = j
      · rw [ite_eq_left (show finrank K ↥(H ⊔ L.1) ≤ k by omega), ite_eq_left ht1,
          show k - finrank K ↥(H ⊔ L.1) = 0 by omega, gr_zero_right]
      · rw [ite_eq_right (show ¬ finrank K ↥(H ⊔ L.1) ≤ k by omega), ite_eq_right ht1]
  have hS := Finset.card_eq_sum_card_fiberwise (f := fun W : Grass K V k => U.1 ⊓ W.1)
    (s := univ.filter fun W : Grass K V k => (grassGraph k).Adj U W ∧ L.1 ≤ W.1) (t := T)
    (by
      intro W hW
      rw [Finset.mem_coe, mem_filter] at hW
      obtain ⟨-, ⟨-, hadj⟩, hLW⟩ := hW
      rw [Finset.mem_coe, hT, mem_filter]
      exact ⟨mem_univ _, inf_le_inf_left U.1 hLW, inf_le_left,
        (by omega : finrank K ↥(U.1 ⊓ W.1) = k - 1)⟩)
  rw [hS, Finset.sum_const_nat hfib, hTcard, hc]
  by_cases htj' : t = j
  · have h1 : ¬ (t + 1 = j) := by omega
    rw [ite_eq_left (hLU.2 htj'), ite_eq_left htj', ite_eq_right h1, add_zero]
    by_cases h : t ≤ k - 1
    · rw [ite_eq_left h, htj']
    · rw [ite_eq_right h, show k - j = 0 by omega, qnum_zero, zero_mul]
  · rw [ite_eq_right (fun h => htj' (hLU.1 h)), ite_eq_right htj', zero_add]
    by_cases ht1 : t + 1 = j
    · rw [ite_eq_left (show t ≤ k - 1 by omega), ite_eq_left ht1, ite_eq_left ht1, mul_one,
        show k + 1 - j = k - t by omega]
    · rw [ite_eq_right ht1, ite_eq_right ht1, mul_zero]

/-- Subspaces of dimension `s` inside both `U` and `L`. -/
theorem card_common_sub {k j s : ℕ} (U : Grass K V k) (L : Grass K V j) :
    #(univ.filter fun M : Grass K V s => M.1 ≤ U.1 ∧ M.1 ≤ L.1) =
      gr K (finrank K ↥(U.1 ⊓ L.1)) s := by
  rw [← card_grass_le_sub]
  congr 1
  exact Finset.filter_congr fun M _ => le_inf_iff.symm

end Interval

end SubspaceConvolution
