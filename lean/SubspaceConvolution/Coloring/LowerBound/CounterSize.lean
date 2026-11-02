/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Main
import SubspaceConvolution.Coloring.LowerBound.LittleO

/-!
# Theorem C.1: size of the counter reduction on the instances of Lemma C.2

Lemma C.2 (from FGLSZ19) supplies instances with `|C| = O(k² n²)` constraints and
`L = max(1, max_C |R_C|) ≤ max(n, 4)` mini-constraints per constraint.  On such instances the
counter-reduction graph has `N ≤ g(k) (n+1)^6` vertices (`card_Vtx_le_poly`; the paper writes
`N ≤ g(k) n^6`).
-/

open Finset

namespace SubspaceConvolution.Counter

/-- The instance class of Lemma C.2: normalized, at most `c₀ k² n²` constraints, and at most
`max(n, 4)` mini-constraints per constraint. -/
def Restricted (c₀ : ℕ) (I : MinCSP) : Prop :=
  I.Normalized ∧ I.p ≤ c₀ * I.k ^ 2 * I.n ^ 2 ∧ ∀ C, I.numMini C ≤ max I.n 4

theorem numA_le (I : MinCSP) (hI : I.Normalized) : numA I ≤ 4 * I.p := by
  unfold numA
  calc ∑ C, (I.scope C).card ≤ ∑ _C : Fin I.p, 4 := sum_le_sum fun C _ => hI.scope_card C
    _ = 4 * I.p := by simp [mul_comm]

theorem numI_le (I : MinCSP) (hI : I.Normalized) (hL : ∀ C, I.numMini C ≤ max I.n 4) :
    numI I ≤ I.p * ((I.n + 4) * (4 * I.n)) := by
  unfold numI
  calc ∑ C, ∑ R : Fin (I.numMini C), ∑ x ∈ I.scope C, (I.n - I.thr C R x)
      ≤ ∑ _C : Fin I.p, (I.n + 4) * (4 * I.n) := by
        refine sum_le_sum fun C _ => ?_
        calc ∑ R : Fin (I.numMini C), ∑ x ∈ I.scope C, (I.n - I.thr C R x)
            ≤ ∑ _R : Fin (I.numMini C), 4 * I.n := by
              refine sum_le_sum fun R _ => ?_
              calc ∑ x ∈ I.scope C, (I.n - I.thr C R x) ≤ ∑ _x ∈ I.scope C, I.n :=
                    sum_le_sum fun x _ => Nat.sub_le _ _
                _ = (I.scope C).card * I.n := by simp
                _ ≤ 4 * I.n := Nat.mul_le_mul_right _ (hI.scope_card C)
          _ = I.numMini C * (4 * I.n) := by simp
          _ ≤ (I.n + 4) * (4 * I.n) := by
              apply Nat.mul_le_mul_right
              have := hL C
              omega
    _ = I.p * ((I.n + 4) * (4 * I.n)) := by simp

/-- The function of `k` in the size bound. -/
def sizeFactor (c₀ k : ℕ) : ℕ :=
  let d := Nat.find (exists_sq_exponent k)
  let M := 2 ^ (d * d)
  (d + 1) * M + 37 * c₀ * k ^ 2 * (d + M + 1) + 68 * c₀ ^ 2 * k ^ 4

/-- **Size of the reduction (Theorem C.1):** `N ≤ g(k) (n+1)^6` on the instances of Lemma C.2. -/
theorem card_Vtx_le_poly {c₀ : ℕ} {I : MinCSP} (hI : Restricted c₀ I) :
    Fintype.card (Vtx I) ≤ sizeFactor c₀ I.k * (I.n + 1) ^ 6 := by
  obtain ⟨hN, hp, hL⟩ := hI
  have hA := numA_le I hN
  have hIb := numI_le I hN hL
  have hcard := card_Vtx_le I
  set n := I.n
  set p := I.p
  set k := I.k
  set dd := d I with hdd
  set MM := M I with hMM
  have hQ : Q I = MM * n := rfl
  have heta : eta I = MM * n + (p + numI I) := rfl
  have hsf : sizeFactor c₀ k = (dd + 1) * MM + 37 * c₀ * k ^ 2 * (dd + MM + 1) +
      68 * c₀ ^ 2 * k ^ 4 := rfl
  rw [hsf]
  rw [hQ, heta] at hcard
  -- crude bounds in terms of `(n+1)`
  set m := n + 1 with hm
  have hn : n ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hp' : p ≤ c₀ * k ^ 2 * m ^ 2 :=
    hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2))
  have hI' : numI I ≤ p * (4 * m * (4 * m)) :=
    hIb.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega)))
  have hm2 : m ^ 2 ≤ m ^ 6 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hm3 : m ^ 3 ≤ m ^ 6 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hm4 : m ^ 4 ≤ m ^ 6 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hm1' : m ≤ m ^ 6 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 6 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hnI : numI I ≤ 16 * c₀ * k ^ 2 * m ^ 4 := by
    calc numI I ≤ p * (4 * m * (4 * m)) := hI'
      _ ≤ c₀ * k ^ 2 * m ^ 2 * (4 * m * (4 * m)) := Nat.mul_le_mul_right _ hp'
      _ = 16 * c₀ * k ^ 2 * m ^ 4 := by ring
  have hpp : p * p ≤ c₀ ^ 2 * k ^ 4 * m ^ 4 := by
    calc p * p ≤ (c₀ * k ^ 2 * m ^ 2) * (c₀ * k ^ 2 * m ^ 2) := Nat.mul_le_mul hp' hp'
      _ = c₀ ^ 2 * k ^ 4 * m ^ 4 := by ring
  have hpI : p * numI I ≤ 16 * c₀ ^ 2 * k ^ 4 * m ^ 6 := by
    calc p * numI I ≤ (c₀ * k ^ 2 * m ^ 2) * (16 * c₀ * k ^ 2 * m ^ 4) := Nat.mul_le_mul hp' hnI
      _ = 16 * c₀ ^ 2 * k ^ 4 * m ^ 6 := by ring
  have hpdM : p * (dd * n + MM * n) ≤ c₀ * k ^ 2 * (dd + MM) * m ^ 3 := by
    calc p * (dd * n + MM * n) ≤ (c₀ * k ^ 2 * m ^ 2) * ((dd + MM) * m) := by
          apply Nat.mul_le_mul hp'
          nlinarith
      _ = c₀ * k ^ 2 * (dd + MM) * m ^ 3 := by ring
  calc Fintype.card (Vtx I)
      ≤ (dd + 1) * (MM * n) + p + 2 * numI I + numA I * (dd * n + (MM * n + (p + numI I))) :=
        hcard
    _ ≤ (dd + 1) * (MM * n) + p + 2 * numI I + 4 * p * (dd * n + (MM * n + (p + numI I))) := by
        gcongr
    _ = (dd + 1) * MM * n + p + 2 * numI I + 4 * (p * (dd * n + MM * n)) + 4 * (p * p) +
          4 * (p * numI I) := by ring
    _ ≤ (dd + 1) * MM * m ^ 6 + c₀ * k ^ 2 * m ^ 6 + 2 * (16 * c₀ * k ^ 2 * m ^ 6) +
          4 * (c₀ * k ^ 2 * (dd + MM) * m ^ 6) + 4 * (c₀ ^ 2 * k ^ 4 * m ^ 6) +
          4 * (16 * c₀ ^ 2 * k ^ 4 * m ^ 6) := by
        have e1 : (dd + 1) * MM * n ≤ (dd + 1) * MM * m ^ 6 :=
          Nat.mul_le_mul_left _ (hn.trans hm1')
        have e2 : p ≤ c₀ * k ^ 2 * m ^ 6 := hp'.trans (Nat.mul_le_mul_left _ hm2)
        have e3 : numI I ≤ 16 * c₀ * k ^ 2 * m ^ 6 := hnI.trans (Nat.mul_le_mul_left _ hm4)
        have e4 : p * (dd * n + MM * n) ≤ c₀ * k ^ 2 * (dd + MM) * m ^ 6 :=
          hpdM.trans (Nat.mul_le_mul_left _ hm3)
        have e5 : p * p ≤ c₀ ^ 2 * k ^ 4 * m ^ 6 := hpp.trans (Nat.mul_le_mul_left _ hm4)
        have e6 := hpI
        have := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add e1 e2) (Nat.mul_le_mul_left 2 e3)) (Nat.mul_le_mul_left 4 e4))
          (Nat.mul_le_mul_left 4 e5)) (Nat.mul_le_mul_left 4 e6)
        exact this
    _ ≤ ((dd + 1) * MM + 37 * c₀ * k ^ 2 * (dd + MM + 1) + 68 * c₀ ^ 2 * k ^ 4) * m ^ 6 := by
        ring_nf
        nlinarith [Nat.zero_le (c₀ * k ^ 2 * m ^ 6), Nat.zero_le (c₀ * k ^ 2 * dd * m ^ 6),
          Nat.zero_le (c₀ * k ^ 2 * MM * m ^ 6)]

end SubspaceConvolution.Counter
