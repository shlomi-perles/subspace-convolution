/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Defs

/-!
# Auxiliary arithmetic for `Transform/Count.lean`

Elementary estimates about `q`-analogues for a natural number `q ≥ 2` (in `Count.lean`,
`q = |K|`).  Nothing here mentions subspaces.

* `qprod q n j = ∏_{i<j} (q^n - q^i)`, the number of linearly independent `j`-tuples in `F_q^n`,
  with the recursions `qprod_succ`, `qprod_succ_succ`, and the bounds `qprod_pos`, `qprod_le`,
  `pow_mul_qprod_le` (each factor `(q^n - q^i)/(q^j - q^i)` is at least `q^{n-j}`) and
  `pow_le_four_mul_qprod` (`|GL_j(F_q)| ≥ q^{j²}/4`, since `∏_{i ≥ 1} (1 - q^{-i}) ≥ 1/4`).
* `qfac q m = ∏_{i<m} (q^{i+1} - 1)`.
* `sum_pow_mul_sub_le`: completing the square, `∑_{j ≤ r} q^{j(r-j)} ≤ 4 q^{⌊r²/4⌋}`.
* `slack_core`, `slack_core_eq`, `slack_arith_*`, `budget_arith`: the arithmetic of Appendix B.
-/

open Finset

namespace SubspaceConvolution

namespace CountAux

/-! ### `∏_{i<j} (q^n - q^i)` -/

/-- `∏_{i<j} (q^n - q^i)`: the number of linearly independent `j`-tuples in `F_q^n`. -/
def qprod (q n j : ℕ) : ℕ := ∏ i ∈ range j, (q ^ n - q ^ i)

@[simp] theorem qprod_zero (q n : ℕ) : qprod q n 0 = 1 := by simp [qprod]

theorem qprod_succ (q n j : ℕ) : qprod q n (j + 1) = qprod q n j * (q ^ n - q ^ j) := by
  rw [qprod, prod_range_succ, ← qprod]

theorem pow_sub_pow_eq (q : ℕ) {n j : ℕ} (h : j ≤ n) :
    q ^ n - q ^ j = q ^ j * (q ^ (n - j) - 1) := by
  rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' h]

/-- `∏_{i ≤ j} (q^{n+1} - q^i) = (q^{n+1} - 1) q^j ∏_{i<j} (q^n - q^i)`. -/
theorem qprod_succ_succ (q n j : ℕ) :
    qprod q (n + 1) (j + 1) = (q ^ (n + 1) - 1) * q ^ j * qprod q n j := by
  rw [qprod, prod_range_succ']
  have h : ∀ i ∈ range j, q ^ (n + 1) - q ^ (i + 1) = q * (q ^ n - q ^ i) := by
    intro i _
    rw [Nat.mul_sub, ← pow_succ', ← pow_succ']
  rw [prod_congr rfl h, prod_mul_distrib, prod_const, card_range, pow_zero, ← qprod]
  ring

theorem qprod_pos {q n j : ℕ} (hq : 1 < q) (h : j ≤ n) : 0 < qprod q n j :=
  prod_pos fun _ hi => Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq ((mem_range.1 hi).trans_le h))

theorem qprod_le (q n j : ℕ) : qprod q n j ≤ q ^ (n * j) :=
  calc qprod q n j ≤ (q ^ n) ^ #(range j) := prod_le_pow_card _ _ _ fun i _ => Nat.sub_le _ _
    _ = q ^ (n * j) := by rw [card_range, ← pow_mul]

/-- Each factor `(q^n - q^i)/(q^j - q^i)` is at least `q^{n-j}`. -/
theorem pow_mul_qprod_le {q n j : ℕ} (hq : 0 < q) (h : j ≤ n) :
    q ^ (j * (n - j)) * qprod q j j ≤ qprod q n j := by
  have hfac : ∀ i ∈ range j, q ^ (n - j) * (q ^ j - q ^ i) ≤ q ^ n - q ^ i := by
    intro i _
    rw [Nat.mul_sub, ← pow_add, Nat.sub_add_cancel h]
    exact Nat.sub_le_sub_left (Nat.le_mul_of_pos_left _ (Nat.pow_pos hq)) _
  calc q ^ (j * (n - j)) * qprod q j j = ∏ i ∈ range j, q ^ (n - j) * (q ^ j - q ^ i) := by
        rw [qprod, prod_mul_distrib, prod_const, card_range, ← pow_mul, Nat.mul_comm j]
    _ ≤ qprod q n j := prod_le_prod hfac

theorem qprod_self_succ (q j : ℕ) :
    qprod q (j + 1) (j + 1) = (q ^ (j + 1) - 1) * q ^ j * qprod q j j :=
  qprod_succ_succ q j j

/-- `∏_{i ≤ k} (1 - q^{-(i+1)}) ≥ 1/4 + q^{-(k+1)}/2`, multiplied out. -/
theorem qprod_aux {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    (q ^ (k + 1) + 2) * q ^ ((k + 1) * (k + 1)) ≤ 4 * q ^ (k + 1) * qprod q (k + 1) (k + 1) := by
  induction k with
  | zero =>
    simp only [zero_add, pow_one, mul_one, qprod, prod_range_one, pow_zero]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
    rw [show r + 2 - 1 = r + 1 by omega]
    nlinarith
  | succ k ih =>
    rw [qprod_self_succ q (k + 1)]
    set D := qprod q (k + 1) (k + 1)
    set x := q ^ (k + 1) with hx_def
    have hx : 2 ≤ x := le_trans hq (by rw [hx_def]; exact Nat.le_self_pow (by omega) q)
    have h2 : q ^ (k + 1 + 1) = q * x := by rw [hx_def, pow_succ']
    have h4 : q ^ ((k + 1 + 1) * (k + 1 + 1)) = q ^ ((k + 1) * (k + 1)) * x * x * q := by
      rw [hx_def, ← pow_add, ← pow_add, ← pow_succ]
      congr 1
      ring
    rw [h2, h4]
    set P := q ^ ((k + 1) * (k + 1))
    obtain ⟨y, hy⟩ : ∃ y, q * x - 1 = y := ⟨_, rfl⟩
    have hqx : 2 * x ≤ q * x := Nat.mul_le_mul_right x hq
    have hy' : y + 1 = q * x := by omega
    rw [hy]
    have key : (q * x + 2) * x ≤ y * (x + 2) := by
      have e : q * x * x = y * x + x := by rw [← hy']; ring
      nlinarith
    calc (q * x + 2) * (P * x * x * q) = (q * x + 2) * x * (x * q * P) := by ring
      _ ≤ y * (x + 2) * (x * q * P) := Nat.mul_le_mul_right _ key
      _ = x * q * y * ((x + 2) * P) := by ring
      _ ≤ x * q * y * (4 * x * D) := Nat.mul_le_mul_left _ ih
      _ = 4 * (q * x) * (y * x * D) := by ring

/-- `|GL_j(F_q)| ≥ q^{j²}/4`. -/
theorem pow_le_four_mul_qprod {q : ℕ} (hq : 2 ≤ q) (j : ℕ) : q ^ (j * j) ≤ 4 * qprod q j j := by
  cases j with
  | zero => simp
  | succ k =>
    have h := qprod_aux hq k
    refine Nat.le_of_mul_le_mul_left (c := q ^ (k + 1)) ?_ (Nat.pow_pos (by omega))
    calc q ^ (k + 1) * q ^ ((k + 1) * (k + 1))
        ≤ (q ^ (k + 1) + 2) * q ^ ((k + 1) * (k + 1)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 4 * q ^ (k + 1) * qprod q (k + 1) (k + 1) := h
      _ = q ^ (k + 1) * (4 * qprod q (k + 1) (k + 1)) := by ring

/-! ### `∏_{i<m} (q^{i+1} - 1)` -/

/-- `∏_{i<m} (q^{i+1} - 1)` (`= (q-1)^m [m]_q!`). -/
def qfac (q m : ℕ) : ℕ := ∏ i ∈ range m, (q ^ (i + 1) - 1)

@[simp] theorem qfac_zero (q : ℕ) : qfac q 0 = 1 := by simp [qfac]

theorem qfac_succ (q m : ℕ) : qfac q (m + 1) = qfac q m * (q ^ (m + 1) - 1) := by
  rw [qfac, prod_range_succ, ← qfac]

theorem qfac_pos {q : ℕ} (hq : 1 < q) (m : ℕ) : 0 < qfac q m :=
  prod_pos fun i _ => Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero i) hq)

/-! ### Completing the square -/

/-- `∑_{j ≤ r} q^{j(r-j)} ≤ 4 q^{⌊r²/4⌋}`. -/
theorem sum_pow_mul_sub_le {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    ∑ j ∈ range (r + 1), q ^ (j * (r - j)) ≤ 4 * q ^ (r * r / 4) := by
  have hsplit : r + 1 = (r / 2 + 1) + (r - r / 2) := by omega
  have h2q : ∀ t, 2 ^ t ≤ q ^ t := fun t => Nat.pow_le_pow_left hq t
  have h1 : ∑ j ∈ range (r / 2 + 1), q ^ (j * (r - j)) ≤ 2 * q ^ (r * r / 4) := by
    rw [← Finset.sum_range_reflect]
    refine sum_le_two_mul_of_mul_pow_le fun t ht => ?_
    refine (Nat.mul_le_mul_left _ (h2q t)).trans ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by omega) ?_
    rw [Nat.add_sub_cancel]
    exact exponent_le_left (by omega)
  have h2 : ∑ t ∈ range (r - r / 2), q ^ ((r / 2 + 1 + t) * (r - (r / 2 + 1 + t))) ≤
      2 * q ^ (r * r / 4) := by
    refine sum_le_two_mul_of_mul_pow_le fun t ht => ?_
    refine (Nat.mul_le_mul_left _ (h2q t)).trans ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) (exponent_le_right ht)
  rw [hsplit, Finset.sum_range_add]
  linarith

/-! ### Small inequalities -/

theorem two_mul_le_two_pow (m : ℕ) : 2 * m ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

theorem succ_le_pow {q : ℕ} (hq : 2 ≤ q) (m : ℕ) : m + 1 ≤ q ^ m :=
  (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hq m)

theorem two_mul_le_pow {q : ℕ} (hq : 2 ≤ q) (m : ℕ) : 2 * m ≤ q ^ m :=
  (two_mul_le_two_pow m).trans (Nat.pow_le_pow_left hq m)

/-- `n² ≤ 5 ⌊n²/4⌋` for `n ≥ 2`. -/
theorem mul_self_le_five_mul_div_four {n : ℕ} (hn : 2 ≤ n) : n * n ≤ 5 * (n * n / 4) := by
  rcases Nat.even_or_odd' n with ⟨p, rfl | rfl⟩
  · have h : 2 * p * (2 * p) / 4 = p * p := by
      rw [show 2 * p * (2 * p) = 4 * (p * p) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h]
    nlinarith
  · have h : (2 * p + 1) * (2 * p + 1) / 4 = p * p + p := by
      rw [show (2 * p + 1) * (2 * p + 1) = 4 * (p * p + p) + 1 by ring]
      omega
    rw [h]
    have : 1 ≤ p := by omega
    nlinarith

/-! ### Appendix B arithmetic -/

/-- The case `a < c` of eq. (slack): `I + aJ ≤ 3S/4`, from `|Gr(n-1, j)| ≤ q^{-j} |Gr(n, j)|`
and `A ≤ B`.  Here `x, y, z` stand for `|Gr(n-1,a)|, |Gr(n-1,b)|, |Gr(n-1,b-1)|`. -/
theorem slack_core {q m x y z A B e₁ e₂ : ℕ} (hq : 2 ≤ q) (hx : q ^ m * x ≤ A)
    (hy : q ^ e₁ * y ≤ B) (hz : q ^ e₂ * z ≤ B) (he₁ : m + 1 ≤ e₁) (he₂ : m + 1 ≤ e₂)
    (hAB : A ≤ B) : 4 * ((m + 1) * x + y + m * z) ≤ 3 * (A + B) := by
  have h1 : m + 1 ≤ q ^ m := succ_le_pow hq m
  have h2 : 2 * (m + 1) ≤ q ^ (m + 1) := two_mul_le_pow hq (m + 1)
  have hy' : q ^ (m + 1) * y ≤ B :=
    le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) he₁)) hy
  have hz' : q ^ (m + 1) * z ≤ B :=
    le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) he₂)) hz
  have hxA : (m + 1) * x ≤ A := le_trans (Nat.mul_le_mul_right _ h1) hx
  have hyz : 2 * (y + m * z) ≤ B := by
    have h3 : (m + 1) * (2 * (y + m * z)) ≤ (m + 1) * B := by
      calc (m + 1) * (2 * (y + m * z)) = 2 * (m + 1) * (y + m * z) := by ring
        _ ≤ q ^ (m + 1) * (y + m * z) := Nat.mul_le_mul_right _ h2
        _ = q ^ (m + 1) * y + m * (q ^ (m + 1) * z) := by ring
        _ ≤ B + m * B := Nat.add_le_add hy' (Nat.mul_le_mul_left _ hz')
        _ = (m + 1) * B := by ring
    exact Nat.le_of_mul_le_mul_left h3 (by omega)
  linarith

/-- The case `a = c` of eq. (slack): `aJ ≤ 3S/4` from `J ≤ q^{-a} S`. -/
theorem slack_core_eq {q m J S : ℕ} (hq : 2 ≤ q) (h : q ^ m * J ≤ S) : 4 * m * J ≤ 3 * S := by
  have h1 : 2 * m ≤ q ^ m := two_mul_le_pow hq m
  calc 4 * m * J ≤ 3 * (q ^ m * J) := by nlinarith
    _ ≤ 3 * S := Nat.mul_le_mul_left _ h

/-- Eq. (slack), case `a < c`: the bookkeeping. `x, y, z, w` are `|Gr(n-1, ·)|` at
`a, b, b-1, a-1`, `u, v` are `|Gr(n-2, ·)|` at `a-1, b-1`, `A, B` are `|Gr(n, a)|, |Gr(n, b)|`,
`E = q^{n-1} - 1`, and `m₁, …, m₄` are the minima of the recursive calls. -/
theorem slack_arith_lt {m d m₁ m₂ m₃ m₄ x y z w u v E A B : ℕ} (hm : m = d + 1)
    (h₁ : m₁ = m) (h₂ : m₂ = m) (h₃ : m₃ = d) (h₄ : m₄ = d)
    (hA : A = x + w + E * u) (hB : B = y + z + E * v)
    (core : 4 * ((m + 1) * x + y + m * z) ≤ 3 * (A + B)) :
    4 * (m₁ * (x + y) + m₂ * (x + z) + m₃ * (w + z) + E * (m₄ * (u + v))) + (A + B) ≤
      4 * (m₂ * (A + B)) := by
  subst h₁ h₂ h₃ h₄ hm hA hB
  nlinarith [core]

/-- Eq. (slack), case `a = c`. -/
theorem slack_arith_eq {m d m₁ m₂ m₃ m₄ x y z w u v E A B : ℕ} (hm : m = d + 1)
    (h₁ : m₁ = d) (h₂ : m₂ = m) (h₃ : m₃ = d) (h₄ : m₄ = d)
    (hA : A = x + w + E * u) (hB : B = y + z + E * v)
    (core : 4 * m * (x + z) ≤ 3 * (A + B)) :
    4 * (m₁ * (x + y) + m₂ * (x + z) + m₃ * (w + z) + E * (m₄ * (u + v))) + (A + B) ≤
      4 * (m₂ * (A + B)) := by
  subst h₁ h₂ h₃ h₄ hm hA hB
  nlinarith [core]

/-- Eq. (slack), case `a > c` (the dual of the case `a < c`). -/
theorem slack_arith_gt {c e m₁ m₂ m₃ m₄ x y z w u v E A B : ℕ} (hc : c = e + 1)
    (h₁ : m₁ = e) (h₂ : m₂ = c) (h₃ : m₃ = c) (h₄ : m₄ = e)
    (hA : A = x + w + E * u) (hB : B = y + z + E * v)
    (core : 4 * ((c + 1) * z + w + c * x) ≤ 3 * (B + A)) :
    4 * (m₁ * (x + y) + m₂ * (x + z) + m₃ * (w + z) + E * (m₄ * (u + v))) + (A + B) ≤
      4 * (m₂ * (A + B)) := by
  subst h₁ h₂ h₃ h₄ hc hA hB
  nlinarith [core]

/-- The induction step of Appendix B, given eq. (slack): `I, J, F, G` are the sizes of the
recursive calls (`F` the frequency call with `λ = 0`, `G` the other `E = q^{n-1} - 1` ones). -/
theorem budget_arith {C₁ n n₁ n₂ m₁ m₂ m₃ m₄ I J F G E S : ℕ} (hn : 1 ≤ n) (hn₁ : n₁ ≤ n)
    (hn₂ : n₂ ≤ n) (hS : S = I + F + E * G) (hJ : J ≤ S)
    (hslack : 4 * (m₁ * I + m₂ * J + m₃ * F + E * (m₄ * G)) + S ≤ 4 * (m₂ * S)) :
    (4 * C₁ + 4) * n₁ * m₁ * I + I + ((4 * C₁ + 4) * n₁ * m₂ * J + J) +
        ((4 * C₁ + 4) * n₁ * m₃ * F + F) + E * ((4 * C₁ + 4) * n₂ * m₄ * G + G) +
        C₁ * n * S ≤
      (4 * C₁ + 4) * n * m₂ * S + S := by
  have h1 : (4 * C₁ + 4) * n₁ * m₁ * I ≤ (4 * C₁ + 4) * n * m₁ * I := by gcongr
  have h2 : (4 * C₁ + 4) * n₁ * m₂ * J ≤ (4 * C₁ + 4) * n * m₂ * J := by gcongr
  have h3 : (4 * C₁ + 4) * n₁ * m₃ * F ≤ (4 * C₁ + 4) * n * m₃ * F := by gcongr
  have h4 : E * ((4 * C₁ + 4) * n₂ * m₄ * G) ≤ E * ((4 * C₁ + 4) * n * m₄ * G) := by gcongr
  have h5 : (C₁ + 1) * n * (4 * (m₁ * I + m₂ * J + m₃ * F + E * (m₄ * G)) + S) ≤
      (C₁ + 1) * n * (4 * (m₂ * S)) := Nat.mul_le_mul_left _ hslack
  have h6 : S ≤ n * S := Nat.le_mul_of_pos_left S hn
  subst hS
  nlinarith [h1, h2, h3, h4, h5, h6, hJ]

end CountAux

end SubspaceConvolution
