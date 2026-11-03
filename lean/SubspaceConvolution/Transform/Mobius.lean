/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.LBAux

/-!
# Möbius coefficients of the subspace lattice (Appendix D)

The inverse containment coefficient for a dimension gap `j` is `μ(j) = (-1)^j q^{j(j-1)/2}`
(`mobiusCoeff`), as equation (25) verifies by interval inversion; cutoffs preserve intervals.

* `sum_gr_mul_mobiusCoeff` — `∑_{j ≤ m} (-1)^j q^{j(j-1)/2} |Gr(m, j)| = [m = 0]` (the
  `q`-binomial theorem at `x = -1`, from the recursion `S(m+1) = (1 - q^m) S(m)`,
  `MobiusAux.sum_succ`).
* `MobiusAux.sum_interval_mobius`, `MobiusAux.sum_interval_mobius'` — interval inversion: for
  `A ≤ B`, `∑_{A ≤ L ≤ B} μ(dim L - dim A) = ∑_{A ≤ L ≤ B} μ(dim B - dim L) = [A = B]`
  (intervals are counted by `LBAux.card_interval`).
* `zetaInv_eq_sum_mobius` — **Möbius values**: `(Z⁻¹ g)(W) = ∑_{U ≤ W} μ(dim W - dim U) g(U)`.
* `zetaTInv_eq_sum_mobius` — `((Zᵀ)⁻¹ g)(U) = ∑_{W ≥ U} μ(dim W - dim U) g(W)`.

Helper lemmas live in the namespace `SubspaceConvolution.MobiusAux`.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

/-! ### The Möbius coefficients and the alternating `q`-binomial sum -/

section Coeff

variable (K : Type*) [Field K] [Fintype K]

local notation "q" => Fintype.card K

/-- The Möbius coefficient `μ(j) = (-1)^j q^{j(j-1)/2}` of an interval of dimension gap `j`. -/
def mobiusCoeff (j : ℕ) : ℤ := (-1) ^ j * (q : ℤ) ^ (j * (j - 1) / 2)

theorem mobiusCoeff_zero : mobiusCoeff K 0 = 1 := by simp [mobiusCoeff]

theorem abs_mobiusCoeff (j : ℕ) : |mobiusCoeff K j| = (q : ℤ) ^ (j * (j - 1) / 2) := by
  simp [mobiusCoeff, abs_mul, abs_pow]

/-- `|μ(j)| ≤ q^{n(n-1)/2}` for `j ≤ n`. -/
theorem abs_mobiusCoeff_le {j n : ℕ} (h : j ≤ n) :
    |mobiusCoeff K j| ≤ (q : ℤ) ^ (n * (n - 1) / 2) := by
  rw [abs_mobiusCoeff]
  have hq : (1 : ℤ) ≤ q := by exact_mod_cast Fintype.card_pos
  exact pow_le_pow_right₀ hq (Nat.div_le_div_right (Nat.mul_le_mul h (by omega)))

/-- The recursion `S(m+1) = (1 - q^m) S(m)` for `S(m) = ∑_j μ(j) |Gr(m, j)|`. -/
theorem MobiusAux.sum_succ (m : ℕ) :
    ∑ j ∈ range (m + 2), (gr K (m + 1) j : ℤ) * mobiusCoeff K j =
      (1 - (q : ℤ) ^ m) * ∑ j ∈ range (m + 1), (gr K m j : ℤ) * mobiusCoeff K j := by
  have hS : ∑ j ∈ range (m + 1), (gr K m j : ℤ) * mobiusCoeff K j =
      ∑ j ∈ range (m + 2), (gr K m j : ℤ) * mobiusCoeff K j := by
    rw [Finset.sum_range_succ _ (m + 1), gr_eq_zero_of_lt K (Nat.lt_succ_self m)]
    simp
  have key : ∀ i ∈ range (m + 1),
      ((q : ℤ) ^ (m - i) * (gr K m i : ℤ)) * mobiusCoeff K (i + 1) =
        -(q : ℤ) ^ m * ((gr K m i : ℤ) * mobiusCoeff K i) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hm : (q : ℤ) ^ m = (q : ℤ) ^ (m - i) * (q : ℤ) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hi']
    rw [mobiusCoeff, mobiusCoeff, Nat.triangle_succ, hm]
    ring
  rw [Finset.sum_range_succ' _ (m + 1)]
  simp only [gr_succ_succ, gr_zero_right, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, add_mul,
    sum_add_distrib]
  rw [sum_congr rfl key, ← Finset.mul_sum, hS, Finset.sum_range_succ' _ (m + 1)]
  simp only [gr_zero_right, Nat.cast_one, one_mul, mobiusCoeff_zero]
  ring

/-- `∑_{j ≤ m} (-1)^j q^{j(j-1)/2} |Gr(m, j)| = [m = 0]`. -/
theorem sum_gr_mul_mobiusCoeff (m : ℕ) :
    ∑ j ∈ range (m + 1), (gr K m j : ℤ) * mobiusCoeff K j = if m = 0 then 1 else 0 := by
  induction m with
  | zero => simp [mobiusCoeff, gr_zero_right]
  | succ m ih =>
    rw [MobiusAux.sum_succ, ih]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]

/-- `sum_gr_mul_mobiusCoeff` in any commutative ring. -/
theorem MobiusAux.sum_cast {R : Type*} [CommRing R] (m : ℕ) :
    ∑ j ∈ range (m + 1), gr K m j • (mobiusCoeff K j : R) = if m = 0 then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → R) (sum_gr_mul_mobiusCoeff K m)
  push_cast at h
  rw [← h]
  refine sum_congr rfl fun j _ => ?_
  rw [nsmul_eq_mul]

/-- The reflected sum `∑_{j ≤ m} |Gr(m, j)| μ(m - j) = [m = 0]`. -/
theorem MobiusAux.sum_cast' {R : Type*} [CommRing R] (m : ℕ) :
    ∑ j ∈ range (m + 1), gr K m j • (mobiusCoeff K (m - j) : R) = if m = 0 then 1 else 0 := by
  rw [← MobiusAux.sum_cast K m, ← Finset.sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show m + 1 - 1 - j = m - j by omega, Nat.sub_sub_self hj', gr_symm K hj']

end Coeff

/-! ### Interval inversion -/

namespace MobiusAux

section Interval

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type*} [CommRing R]

open Classical in
/-- `∑_{A ≤ L ≤ B} μ(dim L - dim A) = [A = B]`. -/
theorem sum_interval_mobius {A B : Submodule K V} (hAB : A ≤ B) :
    ∑ L ∈ univ.filter (fun L : Submodule K V => A ≤ L ∧ L ≤ B),
      (mobiusCoeff K (finrank K L - finrank K A) : R) = if A = B then 1 else 0 := by
  rw [LBAux.sum_interval hAB (fun j => (mobiusCoeff K j : R)), MobiusAux.sum_cast]
  have hle := Submodule.finrank_mono hAB
  by_cases h : A = B
  · subst h; simp
  · have hlt : finrank K A < finrank K B :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hAB h)
    rw [ite_eq_right (by omega), ite_eq_right h]

open Classical in
/-- `∑_{A ≤ L ≤ B} μ(dim B - dim L) = [A = B]`. -/
theorem sum_interval_mobius' {A B : Submodule K V} (hAB : A ≤ B) :
    ∑ L ∈ univ.filter (fun L : Submodule K V => A ≤ L ∧ L ≤ B),
      (mobiusCoeff K (finrank K B - finrank K L) : R) = if A = B then 1 else 0 := by
  have h1 : ∀ L ∈ univ.filter (fun L : Submodule K V => A ≤ L ∧ L ≤ B),
      (mobiusCoeff K (finrank K B - finrank K L) : R) =
        (mobiusCoeff K (finrank K B - finrank K A - (finrank K L - finrank K A)) : R) := by
    intro L hL
    simp only [mem_filter, mem_univ, true_and] at hL
    have h1 := Submodule.finrank_mono hL.1
    have h2 := Submodule.finrank_mono hL.2
    rw [show finrank K B - finrank K A - (finrank K L - finrank K A) =
      finrank K B - finrank K L by omega]
  have h2 := LBAux.sum_interval (M := R) hAB
    (fun j => (mobiusCoeff K (finrank K B - finrank K A - j) : R))
  rw [sum_congr rfl h1, h2, MobiusAux.sum_cast']
  have hle := Submodule.finrank_mono hAB
  by_cases h : A = B
  · subst h; simp
  · have hlt : finrank K A < finrank K B :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hAB h)
    rw [ite_eq_right (by omega), ite_eq_right h]

open Classical in
/-- An interval below a subspace of dimension `≤ k` lies in `SubLE K V k`. -/
theorem sum_subLE_interval {M : Type*} [AddCommMonoid M] {k : ℕ} {A B : Submodule K V}
    (hB : finrank K B ≤ k) (f : Submodule K V → M) :
    ∑ U ∈ univ.filter (fun U : SubLE K V k => A ≤ U.1 ∧ U.1 ≤ B), f U.1 =
      ∑ L ∈ univ.filter (fun L : Submodule K V => A ≤ L ∧ L ≤ B), f L := by
  refine Finset.sum_bij (fun U _ => U.1) ?_ ?_ ?_ ?_
  · intro U hU
    simpa using hU
  · intro U₁ _ U₂ _ h
    exact Subtype.ext h
  · intro L hL
    simp only [mem_filter, mem_univ, true_and] at hL
    exact ⟨⟨L, (Submodule.finrank_mono hL.2).trans hB⟩, by simpa using hL, rfl⟩
  · intro _ _; rfl

end Interval

end MobiusAux

/-! ### The Möbius transforms -/

section Transforms

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type*} [CommRing R]

open Classical in
/-- **Möbius values**: `(Z⁻¹ g)(W) = ∑_{U ≤ W} (-1)^j q^{j(j-1)/2} g(U)`, `j = dim W - dim U`. -/
theorem zetaInv_eq_sum_mobius (k : ℕ) (g : SubLE K V k → R) (W : SubLE K V k) :
    zetaInv k g W = ∑ U ∈ univ.filter (fun U : SubLE K V k => U.1 ≤ W.1),
      (mobiusCoeff K (finrank K W.1 - finrank K U.1) : R) * g U := by
  suffices h : zeta k (fun W : SubLE K V k => ∑ U ∈ univ.filter (fun U : SubLE K V k => U.1 ≤ W.1),
      (mobiusCoeff K (finrank K W.1 - finrank K U.1) : R) * g U) = g by
    conv_lhs => rw [← h]
    rw [zetaInv_zeta]
  funext W
  rw [zeta, Finset.sum_comm' (t' := univ.filter (fun U' : SubLE K V k => U'.1 ≤ W.1))
    (s' := fun U' => univ.filter (fun U : SubLE K V k => U'.1 ≤ U.1 ∧ U.1 ≤ W.1))]
  · have inner : ∀ U' ∈ univ.filter (fun U' : SubLE K V k => U'.1 ≤ W.1),
        ∑ U ∈ univ.filter (fun U : SubLE K V k => U'.1 ≤ U.1 ∧ U.1 ≤ W.1),
          (mobiusCoeff K (finrank K U.1 - finrank K U'.1) : R) * g U' =
            if U' = W then g U' else 0 := by
      intro U' hU'
      rw [← Finset.sum_mul, MobiusAux.sum_subLE_interval W.2
        (fun L => (mobiusCoeff K (finrank K L - finrank K U'.1) : R)),
        MobiusAux.sum_interval_mobius (mem_filter.1 hU').2]
      by_cases h : U' = W
      · subst h; simp
      · rw [ite_eq_right (fun h' => h (Subtype.ext h')), ite_eq_right h, zero_mul]
    rw [sum_congr rfl inner, Finset.sum_ite_eq']
    simp
  · intro U U'
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, h2.trans h1⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h2, h1⟩

open Classical in
/-- **Möbius values** for the transpose: `((Zᵀ)⁻¹ g)(U) = ∑_{W ≥ U} (-1)^j q^{j(j-1)/2} g(W)`,
`j = dim W - dim U`. -/
theorem zetaTInv_eq_sum_mobius (k : ℕ) (g : SubLE K V k → R) (U : SubLE K V k) :
    zetaTInv k g U = ∑ W ∈ univ.filter (fun W : SubLE K V k => U.1 ≤ W.1),
      (mobiusCoeff K (finrank K W.1 - finrank K U.1) : R) * g W := by
  suffices h : zetaT k (fun U : SubLE K V k => ∑ W ∈ univ.filter (fun W : SubLE K V k => U.1 ≤ W.1),
      (mobiusCoeff K (finrank K W.1 - finrank K U.1) : R) * g W) = g by
    conv_lhs => rw [← h]
    rw [zetaTInv_zetaT]
  funext U
  rw [zetaT, Finset.sum_comm' (t' := univ.filter (fun W' : SubLE K V k => U.1 ≤ W'.1))
    (s' := fun W' => univ.filter (fun W : SubLE K V k => U.1 ≤ W.1 ∧ W.1 ≤ W'.1))]
  · have inner : ∀ W' ∈ univ.filter (fun W' : SubLE K V k => U.1 ≤ W'.1),
        ∑ W ∈ univ.filter (fun W : SubLE K V k => U.1 ≤ W.1 ∧ W.1 ≤ W'.1),
          (mobiusCoeff K (finrank K W'.1 - finrank K W.1) : R) * g W' =
            if W' = U then g W' else 0 := by
      intro W' hW'
      rw [← Finset.sum_mul, MobiusAux.sum_subLE_interval W'.2
        (fun L => (mobiusCoeff K (finrank K W'.1 - finrank K L) : R)),
        MobiusAux.sum_interval_mobius' (mem_filter.1 hW').2]
      by_cases h : W' = U
      · subst h; simp
      · rw [ite_eq_right (fun h' => h (Subtype.ext h'.symm)), ite_eq_right h, zero_mul]
    rw [sum_congr rfl inner, Finset.sum_ite_eq']
    simp
  · intro W W'
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1.trans h2⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩

end Transforms

end SubspaceConvolution
