/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Mobius
import SubspaceConvolution.Transform.Algorithm
import SubspaceConvolution.Transform.Incidence

/-!
# Exact integer evaluation (Appendix D, Corollary 2)

For integer inputs of magnitude below `2^H`, every transform of Theorems 1 and 2 is evaluated
exactly by running the algorithm over `ℤ/Lℤ` for a modulus `L ∈ {2B+1, 2B+2}` coprime to
`p = char K`, where `B = 2^H S q^{n(n-1)/2}` bounds the outputs, and taking centered residues
(`ZMod.valMinAbs`).

* Ring-hom compatibility: `IntegerAux.zeta_map`, `zetaT_map`, `zetaInv_map`, `zetaTInv_map`,
  `incid_map`, `incidT_map` (the transforms commute with `φ : R →+* R'`).
* Output bounds: all coefficients are `0/1` or Möbius values `(-1)^j q^{j(j-1)/2}`
  (`zetaInv_eq_sum_mobius`, `zetaTInv_eq_sum_mobius`), of magnitude at most `q^{n(n-1)/2}`
  (`IntegerAux.abs_zeta_le`, `IntegerAux.abs_zetaInv_le`, …).
* `exists_coprime_modulus`, `IntegerAux.valMinAbs_cast_of_abs_le` — the modulus and centered
  residues.
* `IntegerAux.exact_integer_generic` — the argument of Corollary 2 for an abstract transform.
* `exact_integer_zeta`, `exact_integer_zetaInv`, `exact_integer_zetaT`, `exact_integer_zetaTInv`,
  `exact_integer_incid`, `exact_integer_incidT` — **Corollary 2** for the six transforms.

**Bit-cost model.** The algorithm performs `s` gates `z = a x + b y` over `ℤ/Lℤ` (counted by
`LinCost`, from Theorems 1 and 2).  We charge `(log₂ L + 1)²` bit operations per gate, the
schoolbook cost of one multiplication modulo `L`; the bound `s (log₂ L + 1)² = O_q(S (H + n² + 1)²
log S)` is stated in this per-operation bit-cost model (it is not derived from a machine model).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

namespace IntegerAux

/-! ### Ring-hom compatibility -/

section RingHom

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')

theorem zeta_map (k : ℕ) (f : SubLE K V k → R) (W : SubLE K V k) :
    zeta k (fun U => φ (f U)) W = φ (zeta k f W) := by
  simp only [zeta, map_sum]

theorem zetaT_map (k : ℕ) (f : SubLE K V k → R) (U : SubLE K V k) :
    zetaT k (fun W => φ (f W)) U = φ (zetaT k f U) := by
  simp only [zetaT, map_sum]

theorem incid_map (a b : ℕ) (f : Grass K V a → R) (W : Grass K V b) :
    incid a b (fun U => φ (f U)) W = φ (incid a b f W) := by
  simp only [incid, map_sum]

theorem incidT_map (a b : ℕ) (f : Grass K V b → R) (U : Grass K V a) :
    incidT a b (fun W => φ (f W)) U = φ (incidT a b f U) := by
  simp only [incidT, map_sum]

theorem zetaInv_map (k : ℕ) (g : SubLE K V k → R) (W : SubLE K V k) :
    zetaInv k (fun U => φ (g U)) W = φ (zetaInv k g W) := by
  have h : zeta k (fun U => φ (zetaInv k g U)) = fun U => φ (g U) := by
    funext U
    rw [zeta_map, zeta_zetaInv]
  rw [← h, zetaInv_zeta]

theorem zetaTInv_map (k : ℕ) (g : SubLE K V k → R) (U : SubLE K V k) :
    zetaTInv k (fun W => φ (g W)) U = φ (zetaTInv k g U) := by
  have h : zetaT k (fun W => φ (zetaTInv k g W)) = fun W => φ (g W) := by
    funext W
    rw [zetaT_map, zetaT_zetaTInv]
  rw [← h, zetaTInv_zetaT]

end RingHom

/-! ### Output bounds -/

section Bounds

/-- `|∑_{i ∈ s} c_i f_i| ≤ |ι| C F` when `|c_i| ≤ C` and `|f_i| ≤ F`. -/
theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (s : Finset ι) (c f : ι → ℤ) {C F : ℤ}
    (hc : ∀ i, |c i| ≤ C) (hf : ∀ i, |f i| ≤ F) (hC : 0 ≤ C) (hF : 0 ≤ F) :
    |∑ i ∈ s, c i * f i| ≤ Fintype.card ι * (C * F) := by
  calc |∑ i ∈ s, c i * f i| ≤ ∑ i ∈ s, |c i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, C * F := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul (hc i) (hf i) (abs_nonneg _) hC
    _ ≤ ∑ i : ι, C * F :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => mul_nonneg hC hF
    _ = Fintype.card ι * (C * F) := by simp [Finset.card_univ]

/-- `|∑_{i ∈ s} f_i| ≤ |ι| F` when `|f_i| ≤ F`. -/
theorem abs_sum_le_card {ι : Type*} [Fintype ι] (s : Finset ι) (f : ι → ℤ) {F : ℤ}
    (hf : ∀ i, |f i| ≤ F) (hF : 0 ≤ F) :
    |∑ i ∈ s, f i| ≤ Fintype.card ι * F := by
  have h := abs_sum_mul_le s (fun _ => 1) f (C := 1) (fun _ => by simp) hf zero_le_one hF
  simpa using h

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local notation "q" => Fintype.card K

theorem one_le_qpow (m : ℕ) : (1 : ℤ) ≤ (q : ℤ) ^ m :=
  one_le_pow₀ (by exact_mod_cast Fintype.card_pos)

theorem abs_zeta_le (k : ℕ) (f : SubLE K V k → ℤ) {F : ℤ} (hf : ∀ U, |f U| ≤ F) (hF : 0 ≤ F)
    (W : SubLE K V k) :
    |zeta k f W| ≤ Fintype.card (SubLE K V k) *
      ((q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) * F) := by
  refine (abs_sum_le_card _ f hf hF).trans ?_
  have := one_le_qpow (K := K) (finrank K V * (finrank K V - 1) / 2)
  gcongr
  nlinarith

theorem abs_zetaT_le (k : ℕ) (f : SubLE K V k → ℤ) {F : ℤ} (hf : ∀ U, |f U| ≤ F) (hF : 0 ≤ F)
    (U : SubLE K V k) :
    |zetaT k f U| ≤ Fintype.card (SubLE K V k) *
      ((q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) * F) := by
  refine (abs_sum_le_card _ f hf hF).trans ?_
  have := one_le_qpow (K := K) (finrank K V * (finrank K V - 1) / 2)
  gcongr
  nlinarith

theorem abs_incid_le (a b : ℕ) (f : Grass K V a → ℤ) {F : ℤ} (hf : ∀ U, |f U| ≤ F) (hF : 0 ≤ F)
    (W : Grass K V b) :
    |incid a b f W| ≤ Fintype.card (Grass K V a) *
      ((q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) * F) := by
  refine (abs_sum_le_card _ f hf hF).trans ?_
  have := one_le_qpow (K := K) (finrank K V * (finrank K V - 1) / 2)
  gcongr
  nlinarith

theorem abs_incidT_le (a b : ℕ) (f : Grass K V b → ℤ) {F : ℤ} (hf : ∀ U, |f U| ≤ F) (hF : 0 ≤ F)
    (U : Grass K V a) :
    |incidT a b f U| ≤ Fintype.card (Grass K V b) *
      ((q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) * F) := by
  refine (abs_sum_le_card _ f hf hF).trans ?_
  have := one_le_qpow (K := K) (finrank K V * (finrank K V - 1) / 2)
  gcongr
  nlinarith

theorem abs_zetaInv_le (k : ℕ) (g : SubLE K V k → ℤ) {F : ℤ} (hg : ∀ U, |g U| ≤ F) (hF : 0 ≤ F)
    (W : SubLE K V k) :
    |zetaInv k g W| ≤ Fintype.card (SubLE K V k) *
      ((q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) * F) := by
  rw [zetaInv_eq_sum_mobius]
  have hc : ∀ U : SubLE K V k, |mobiusCoeff K (finrank K W.1 - finrank K U.1)| ≤
      (q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) := by
    intro U
    exact abs_mobiusCoeff_le K (by have := Submodule.finrank_le W.1; omega)
  simp only [Int.cast_id]
  exact abs_sum_mul_le _ _ g hc hg (by positivity) hF

theorem abs_zetaTInv_le (k : ℕ) (g : SubLE K V k → ℤ) {F : ℤ} (hg : ∀ U, |g U| ≤ F) (hF : 0 ≤ F)
    (U : SubLE K V k) :
    |zetaTInv k g U| ≤ Fintype.card (SubLE K V k) *
      ((q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) * F) := by
  rw [zetaTInv_eq_sum_mobius]
  have hc : ∀ W : SubLE K V k, |mobiusCoeff K (finrank K W.1 - finrank K U.1)| ≤
      (q : ℤ) ^ (finrank K V * (finrank K V - 1) / 2) := by
    intro W
    exact abs_mobiusCoeff_le K (by have := Submodule.finrank_le W.1; omega)
  simp only [Int.cast_id]
  exact abs_sum_mul_le _ _ g hc hg (by positivity) hF

/-- The number of subspaces is at most `16 q^{n²}` (from `N_q(n) = O(q^{⌊n²/4⌋})`). -/
theorem card_submodule_le : Fintype.card (Submodule K V) ≤ 16 * q ^ (finrank K V ^ 2) := by
  have h1 : Fintype.card (Submodule K V) = Fintype.card (SubLE K V (finrank K V)) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun U => Submodule.finrank_le U)).symm
  rw [h1, card_subLE rfl]
  refine (numLE_self_le K _).trans ?_
  exact Nat.mul_le_mul_left 16 (Nat.pow_le_pow_right Fintype.card_pos
    (by rw [sq]; exact Nat.div_le_self _ _))

theorem card_subP_le (P : ℕ → Prop) : Fintype.card (SubP K V P) ≤ Fintype.card (Submodule K V) := by
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem card_subLE_le (k : ℕ) : Fintype.card (SubLE K V k) ≤ 32 * q ^ (finrank K V ^ 2) := by
  have h1 : Fintype.card (SubLE K V k) ≤ Fintype.card (Submodule K V) := card_subP_le _
  have := card_submodule_le (K := K) (V := V)
  omega

theorem card_grass_add_le (a b : ℕ) :
    Fintype.card (Grass K V a) + Fintype.card (Grass K V b) ≤ 32 * q ^ (finrank K V ^ 2) := by
  have h1 : Fintype.card (Grass K V a) ≤ Fintype.card (Submodule K V) := card_subP_le _
  have h2 : Fintype.card (Grass K V b) ≤ Fintype.card (Submodule K V) := card_subP_le _
  have := card_submodule_le (K := K) (V := V)
  omega

end Bounds

end IntegerAux

/-! ### The modulus -/

section Modulus

/-- One of `2B+1`, `2B+2` is coprime to the prime `p`.  (For a composite `p` this can fail, e.g.
`B = 1`, `p = 6`; we use it for `p = char K`, which is prime.) -/
theorem exists_coprime_modulus (B p : ℕ) (hp : p.Prime) :
    ∃ L, (L = 2 * B + 1 ∨ L = 2 * B + 2) ∧ Nat.Coprime L p := by
  by_cases h : p ∣ 2 * B + 1
  · refine ⟨2 * B + 2, Or.inr rfl, ?_⟩
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h'
    rw [show 2 * B + 2 = (2 * B + 1) + 1 by ring] at h'
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h'))
  · exact ⟨2 * B + 1, Or.inl rfl, by rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]; exact h⟩

end Modulus

namespace IntegerAux

/-- Centered residues recover integers of magnitude at most `B` modulo `L > 2B`. -/
theorem valMinAbs_cast_of_abs_le {L B : ℕ} (hL : 2 * B < L) {x : ℤ} (hx : |x| ≤ B) :
    ((x : ZMod L)).valMinAbs = x := by
  have : NeZero L := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  have hL' : (2 * B : ℤ) < L := by exact_mod_cast hL
  rw [Set.mem_Ioc]
  constructor <;> linarith

/-- Arithmetic of the bit-length bound: with `L ≤ 2B + 2`, `B = 2^H S q^{n(n-1)/2}` and
`S ≤ 32 q^{n²}`, `log₂ L = O_q(H + n² + 1)`. -/
theorem cost_arith (q n H S C₁ L : ℕ) (hq : 2 ≤ q) (hS : S ≤ 32 * q ^ (n ^ 2))
    (hL : L ≤ 2 * (2 ^ H * S * q ^ (n * (n - 1) / 2)) + 2) :
    C₁ * S * Nat.log 2 S * (Nat.log 2 L + 1) ^ 2 ≤
      C₁ * (2 * Nat.log 2 q + 10) ^ 2 * S * (H + n ^ 2 + 1) ^ 2 * (Nat.log 2 S + 1) := by
  set c := Nat.log 2 q + 1 with hc
  have hqc : q ≤ 2 ^ c := (Nat.lt_pow_succ_log_self (by norm_num) q).le
  have h1 : q ^ (n ^ 2) ≤ 2 ^ (c * n ^ 2) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hqc _
  have h2 : q ^ (n * (n - 1) / 2) ≤ q ^ (n ^ 2) := by
    refine Nat.pow_le_pow_right (by omega) ?_
    calc n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
      _ ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = n ^ 2 := (sq n).symm
  have hL' : L ≤ 2 ^ (H + 7 + 2 * (c * n ^ 2)) := by
    have e : 2 ^ (H + 7 + 2 * (c * n ^ 2)) =
        2 * (2 ^ H * (32 * 2 ^ (c * n ^ 2)) * 2 ^ (c * n ^ 2)) +
          2 * (2 ^ H * (32 * 2 ^ (c * n ^ 2)) * 2 ^ (c * n ^ 2)) := by
      rw [show H + 7 + 2 * (c * n ^ 2) = H + (c * n ^ 2) + (c * n ^ 2) + 7 by ring]
      simp only [pow_add]
      ring
    have hX1 : 1 ≤ 2 ^ (c * n ^ 2) := Nat.one_le_two_pow
    have hH1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
    have hS' : S ≤ 32 * 2 ^ (c * n ^ 2) := hS.trans (Nat.mul_le_mul_left _ h1)
    have hq' : q ^ (n * (n - 1) / 2) ≤ 2 ^ (c * n ^ 2) := h2.trans h1
    have h4 : 2 ^ H * S * q ^ (n * (n - 1) / 2) ≤
        2 ^ H * (32 * 2 ^ (c * n ^ 2)) * 2 ^ (c * n ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hS') hq'
    have h5 : 1 ≤ 2 ^ H * (32 * 2 ^ (c * n ^ 2)) * 2 ^ (c * n ^ 2) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [e]
    calc L ≤ 2 * (2 ^ H * S * q ^ (n * (n - 1) / 2)) + 2 := hL
      _ ≤ 2 * (2 ^ H * (32 * 2 ^ (c * n ^ 2)) * 2 ^ (c * n ^ 2)) +
          2 * (2 ^ H * (32 * 2 ^ (c * n ^ 2)) * 2 ^ (c * n ^ 2)) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 h4) (by omega)
  have hlogL : Nat.log 2 L ≤ H + 7 + 2 * (c * n ^ 2) :=
    (Nat.log_mono_right hL').trans (Nat.log_pow (by norm_num) _).le
  have h4 : Nat.log 2 L + 1 ≤ (2 * c + 8) * (H + n ^ 2 + 1) := by nlinarith
  have h5 : 2 * c + 8 = 2 * Nat.log 2 q + 10 := by omega
  calc C₁ * S * Nat.log 2 S * (Nat.log 2 L + 1) ^ 2
      ≤ C₁ * S * (Nat.log 2 S + 1) * ((2 * c + 8) * (H + n ^ 2 + 1)) ^ 2 := by
        gcongr
        exact Nat.le_succ _
    _ = C₁ * (2 * Nat.log 2 q + 10) ^ 2 * S * (H + n ^ 2 + 1) ^ 2 * (Nat.log 2 S + 1) := by
        rw [h5]; ring

/-- **Corollary 2**, the generic argument: a transform `out` with integer coefficients, bounded
by `B = 2^H S q^{n(n-1)/2}`, computed by a linear program over every `ℤ/Lℤ` with `L` coprime to
`p`, is recovered exactly from centered residues modulo some `L ∈ {2B+1, 2B+2}`. -/
theorem exact_integer_generic {I O : Type*} (q p : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (C₁ n H S : ℕ) (hS : S ≤ 32 * q ^ (n ^ 2))
    (M : ∀ L : ℕ, (I → ZMod L) → O → ZMod L)
    (hM : ∀ L : ℕ, Nat.Coprime L p →
      LinCost (Set.univ : Set (ZMod L)) (M L) (C₁ * S * Nat.log 2 S))
    (out : O → ℤ) (outMod : ∀ L : ℕ, O → ZMod L) (hout : ∀ L o, outMod L o = (out o : ZMod L))
    (hB : ∀ o, |out o| ≤ ((2 ^ H * S * q ^ (n * (n - 1) / 2) : ℕ) : ℤ)) :
    ∃ L s : ℕ, Nat.Coprime L p ∧ LinCost (Set.univ : Set (ZMod L)) (M L) s ∧
      (∀ o, out o = (outMod L o).valMinAbs) ∧
      s * (Nat.log 2 L + 1) ^ 2 ≤
        C₁ * (2 * Nat.log 2 q + 10) ^ 2 * S * (H + n ^ 2 + 1) ^ 2 * (Nat.log 2 S + 1) := by
  obtain ⟨L, hL, hcop⟩ := exists_coprime_modulus (2 ^ H * S * q ^ (n * (n - 1) / 2)) p hp
  refine ⟨L, C₁ * S * Nat.log 2 S, hcop, hM L hcop, fun o => ?_, ?_⟩
  · rw [hout, valMinAbs_cast_of_abs_le (B := 2 ^ H * S * q ^ (n * (n - 1) / 2)) (by omega) (hB o)]
  · exact cost_arith q n H S C₁ L hq hS (by omega)

/-! ### Corollary 2 -/

theorem isUnit_ringChar_zmod (K : Type*) [Field K] [Fintype K] {L : ℕ}
    (h : Nat.Coprime L (ringChar K)) : IsUnit ((ringChar K : ℕ) : ZMod L) :=
  (ZMod.isUnit_iff_coprime (ringChar K) L).mpr h.symm

theorem natCast_bound_le {K : Type w} [Field K] [Fintype K] (H S S' e : ℕ) (hS : S' ≤ S) :
    (S' : ℤ) * ((Fintype.card K : ℤ) ^ e * 2 ^ H) ≤ ((2 ^ H * S * Fintype.card K ^ e : ℕ) : ℤ) := by
  push_cast
  have : (S' : ℤ) ≤ S := by exact_mod_cast hS
  have h0 : (0 : ℤ) ≤ (Fintype.card K : ℤ) ^ e * 2 ^ H := by positivity
  nlinarith

end IntegerAux

/-! ### Corollary 2 -/

section Corollary

variable (K : Type w) [Field K] [Fintype K]

/-- **Corollary 2** for `Z_{n,k}`: exact evaluation on integer inputs `|f U| < 2^H` from the
centered residues of a program with `s` gates over `ℤ/Lℤ`, `L ≤ 2B + 2` coprime to `p`, with
`s (log₂ L + 1)² = O_q(S (H + n² + 1)² log S)`, `S = M_q(n,k)`.  The factor `(log₂ L + 1)²` per gate
is the schoolbook bit cost of one operation modulo `L`: this per-operation cost is the bit-cost
model (it is not derived from a machine model). -/
theorem exact_integer_zeta :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
      k ≤ finrank K V → ∀ (H : ℕ) (f : SubLE K V k → ℤ), (∀ U, |f U| < 2 ^ H) →
        ∃ (L s : ℕ), Nat.Coprime L (ringChar K) ∧
          LinCost (Set.univ : Set (ZMod L)) (zeta (K := K) (V := V) k) s ∧
          (∀ W, zeta k f W = ((zeta k (fun U => (f U : ZMod L))) W).valMinAbs) ∧
          s * (Nat.log 2 L + 1) ^ 2 ≤ C * Fintype.card (SubLE K V k) *
            (H + finrank K V ^ 2 + 1) ^ 2 * (Nat.log 2 (Fintype.card (SubLE K V k)) + 1) := by
  obtain ⟨C₁, hC₁⟩ := fast_subspace_summation_log.{0, v, w} K
  refine ⟨C₁ * (2 * Nat.log 2 (Fintype.card K) + 10) ^ 2, fun V _ _ _ k hk H f hf => ?_⟩
  exact IntegerAux.exact_integer_generic (Fintype.card K) (ringChar K) Fintype.one_lt_card
    (CharP.prime_ringChar K) C₁ (finrank K V) H _ (IntegerAux.card_subLE_le k)
    (fun L => zeta (K := K) (V := V) (R := ZMod L) k)
    (fun L hL => (hC₁ (ZMod L) (IntegerAux.isUnit_ringChar_zmod K hL) V k hk).1)
    (zeta k f) (fun L => zeta k (fun U => (f U : ZMod L)))
    (fun L W => by simpa using IntegerAux.zeta_map (Int.castRingHom (ZMod L)) k f W)
    (fun W => (IntegerAux.abs_zeta_le k f (fun U => (hf U).le) (by positivity) W).trans
      (IntegerAux.natCast_bound_le H _ _ _ le_rfl))

/-- **Corollary 2** for `Z_{n,k}⁻¹` (coefficients `(-1)^j q^{j(j-1)/2}`,
`zetaInv_eq_sum_mobius`); same bit-cost model. -/
theorem exact_integer_zetaInv :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
      k ≤ finrank K V → ∀ (H : ℕ) (g : SubLE K V k → ℤ), (∀ U, |g U| < 2 ^ H) →
        ∃ (L s : ℕ), Nat.Coprime L (ringChar K) ∧
          LinCost (Set.univ : Set (ZMod L)) (zetaInv (K := K) (V := V) k) s ∧
          (∀ W, zetaInv k g W = ((zetaInv k (fun U => (g U : ZMod L))) W).valMinAbs) ∧
          s * (Nat.log 2 L + 1) ^ 2 ≤ C * Fintype.card (SubLE K V k) *
            (H + finrank K V ^ 2 + 1) ^ 2 * (Nat.log 2 (Fintype.card (SubLE K V k)) + 1) := by
  obtain ⟨C₁, hC₁⟩ := fast_subspace_summation_log.{0, v, w} K
  refine ⟨C₁ * (2 * Nat.log 2 (Fintype.card K) + 10) ^ 2, fun V _ _ _ k hk H g hg => ?_⟩
  exact IntegerAux.exact_integer_generic (Fintype.card K) (ringChar K) Fintype.one_lt_card
    (CharP.prime_ringChar K) C₁ (finrank K V) H _ (IntegerAux.card_subLE_le k)
    (fun L => zetaInv (K := K) (V := V) (R := ZMod L) k)
    (fun L hL => (hC₁ (ZMod L) (IntegerAux.isUnit_ringChar_zmod K hL) V k hk).2.1)
    (zetaInv k g) (fun L => zetaInv k (fun U => (g U : ZMod L)))
    (fun L W => by simpa using IntegerAux.zetaInv_map (Int.castRingHom (ZMod L)) k g W)
    (fun W => (IntegerAux.abs_zetaInv_le k g (fun U => (hg U).le) (by positivity) W).trans
      (IntegerAux.natCast_bound_le H _ _ _ le_rfl))

/-- **Corollary 2** for `Z_{n,k}ᵀ`; same bit-cost model. -/
theorem exact_integer_zetaT :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
      k ≤ finrank K V → ∀ (H : ℕ) (f : SubLE K V k → ℤ), (∀ U, |f U| < 2 ^ H) →
        ∃ (L s : ℕ), Nat.Coprime L (ringChar K) ∧
          LinCost (Set.univ : Set (ZMod L)) (zetaT (K := K) (V := V) k) s ∧
          (∀ U, zetaT k f U = ((zetaT k (fun W => (f W : ZMod L))) U).valMinAbs) ∧
          s * (Nat.log 2 L + 1) ^ 2 ≤ C * Fintype.card (SubLE K V k) *
            (H + finrank K V ^ 2 + 1) ^ 2 * (Nat.log 2 (Fintype.card (SubLE K V k)) + 1) := by
  obtain ⟨C₁, hC₁⟩ := fast_subspace_summation_log.{0, v, w} K
  refine ⟨C₁ * (2 * Nat.log 2 (Fintype.card K) + 10) ^ 2, fun V _ _ _ k hk H f hf => ?_⟩
  exact IntegerAux.exact_integer_generic (Fintype.card K) (ringChar K) Fintype.one_lt_card
    (CharP.prime_ringChar K) C₁ (finrank K V) H _ (IntegerAux.card_subLE_le k)
    (fun L => zetaT (K := K) (V := V) (R := ZMod L) k)
    (fun L hL => (hC₁ (ZMod L) (IntegerAux.isUnit_ringChar_zmod K hL) V k hk).2.2.1)
    (zetaT k f) (fun L => zetaT k (fun W => (f W : ZMod L)))
    (fun L U => by simpa using IntegerAux.zetaT_map (Int.castRingHom (ZMod L)) k f U)
    (fun U => (IntegerAux.abs_zetaT_le k f (fun W => (hf W).le) (by positivity) U).trans
      (IntegerAux.natCast_bound_le H _ _ _ le_rfl))

/-- **Corollary 2** for `(Z_{n,k}ᵀ)⁻¹` (coefficients `(-1)^j q^{j(j-1)/2}`,
`zetaTInv_eq_sum_mobius`); same bit-cost model. -/
theorem exact_integer_zetaTInv :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
      k ≤ finrank K V → ∀ (H : ℕ) (g : SubLE K V k → ℤ), (∀ U, |g U| < 2 ^ H) →
        ∃ (L s : ℕ), Nat.Coprime L (ringChar K) ∧
          LinCost (Set.univ : Set (ZMod L)) (zetaTInv (K := K) (V := V) k) s ∧
          (∀ U, zetaTInv k g U = ((zetaTInv k (fun W => (g W : ZMod L))) U).valMinAbs) ∧
          s * (Nat.log 2 L + 1) ^ 2 ≤ C * Fintype.card (SubLE K V k) *
            (H + finrank K V ^ 2 + 1) ^ 2 * (Nat.log 2 (Fintype.card (SubLE K V k)) + 1) := by
  obtain ⟨C₁, hC₁⟩ := fast_subspace_summation_log.{0, v, w} K
  refine ⟨C₁ * (2 * Nat.log 2 (Fintype.card K) + 10) ^ 2, fun V _ _ _ k hk H g hg => ?_⟩
  exact IntegerAux.exact_integer_generic (Fintype.card K) (ringChar K) Fintype.one_lt_card
    (CharP.prime_ringChar K) C₁ (finrank K V) H _ (IntegerAux.card_subLE_le k)
    (fun L => zetaTInv (K := K) (V := V) (R := ZMod L) k)
    (fun L hL => (hC₁ (ZMod L) (IntegerAux.isUnit_ringChar_zmod K hL) V k hk).2.2.2)
    (zetaTInv k g) (fun L => zetaTInv k (fun W => (g W : ZMod L)))
    (fun L U => by simpa using IntegerAux.zetaTInv_map (Int.castRingHom (ZMod L)) k g U)
    (fun U => (IntegerAux.abs_zetaTInv_le k g (fun W => (hg W).le) (by positivity) U).trans
      (IntegerAux.natCast_bound_le H _ _ _ le_rfl))

/-- **Corollary 2** for `I^{a,b}_n`, with `S = |Gr(n,a)| + |Gr(n,b)|`; same bit-cost model. -/
theorem exact_integer_incid :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (a b : ℕ),
      a ≤ b → b ≤ finrank K V → ∀ (H : ℕ) (f : Grass K V a → ℤ), (∀ U, |f U| < 2 ^ H) →
        ∃ (L s : ℕ), Nat.Coprime L (ringChar K) ∧
          LinCost (Set.univ : Set (ZMod L)) (incid (K := K) (V := V) a b) s ∧
          (∀ W, incid a b f W = ((incid a b (fun U => (f U : ZMod L))) W).valMinAbs) ∧
          s * (Nat.log 2 L + 1) ^ 2 ≤
            C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
            (H + finrank K V ^ 2 + 1) ^ 2 *
              (Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) + 1) := by
  obtain ⟨C₁, hC₁⟩ := fast_incidence.{0, v, w} K
  refine ⟨C₁ * (2 * Nat.log 2 (Fintype.card K) + 10) ^ 2, fun V _ _ _ a b hab hb H f hf => ?_⟩
  exact IntegerAux.exact_integer_generic (Fintype.card K) (ringChar K) Fintype.one_lt_card
    (CharP.prime_ringChar K) C₁ (finrank K V) H _ (IntegerAux.card_grass_add_le a b)
    (fun L => incid (K := K) (V := V) (R := ZMod L) a b)
    (fun L hL => (hC₁ (ZMod L) (IntegerAux.isUnit_ringChar_zmod K hL) V a b hab hb).1)
    (incid a b f) (fun L => incid a b (fun U => (f U : ZMod L)))
    (fun L W => by simpa using IntegerAux.incid_map (Int.castRingHom (ZMod L)) a b f W)
    (fun W => (IntegerAux.abs_incid_le a b f (fun U => (hf U).le) (by positivity) W).trans
      (IntegerAux.natCast_bound_le H _ _ _ (Nat.le_add_right _ _)))

/-- **Corollary 2** for the transpose `I^{a,b}ᵀ`, with `S = |Gr(n,a)| + |Gr(n,b)|`; same
bit-cost model. -/
theorem exact_integer_incidT :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (a b : ℕ),
      a ≤ b → b ≤ finrank K V → ∀ (H : ℕ) (g : Grass K V b → ℤ), (∀ W, |g W| < 2 ^ H) →
        ∃ (L s : ℕ), Nat.Coprime L (ringChar K) ∧
          LinCost (Set.univ : Set (ZMod L)) (incidT (K := K) (V := V) a b) s ∧
          (∀ U, incidT a b g U = ((incidT a b (fun W => (g W : ZMod L))) U).valMinAbs) ∧
          s * (Nat.log 2 L + 1) ^ 2 ≤
            C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
            (H + finrank K V ^ 2 + 1) ^ 2 *
              (Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) + 1) := by
  obtain ⟨C₁, hC₁⟩ := fast_incidence.{0, v, w} K
  refine ⟨C₁ * (2 * Nat.log 2 (Fintype.card K) + 10) ^ 2, fun V _ _ _ a b hab hb H g hg => ?_⟩
  exact IntegerAux.exact_integer_generic (Fintype.card K) (ringChar K) Fintype.one_lt_card
    (CharP.prime_ringChar K) C₁ (finrank K V) H _ (IntegerAux.card_grass_add_le a b)
    (fun L => incidT (K := K) (V := V) (R := ZMod L) a b)
    (fun L hL => (hC₁ (ZMod L) (IntegerAux.isUnit_ringChar_zmod K hL) V a b hab hb).2)
    (incidT a b g) (fun L => incidT a b (fun W => (g W : ZMod L)))
    (fun L U => by simpa using IntegerAux.incidT_map (Int.castRingHom (ZMod L)) a b g U)
    (fun U => (IntegerAux.abs_incidT_le a b g (fun W => (hg W).le) (by positivity) U).trans
      (IntegerAux.natCast_bound_le H _ _ _ (Nat.le_add_left _ _)))

end Corollary

end SubspaceConvolution
