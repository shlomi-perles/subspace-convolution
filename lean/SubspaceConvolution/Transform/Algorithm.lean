/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Step
import SubspaceConvolution.Transform.Count
import SubspaceConvolution.Transform.AlgAux

/-!
# The fast zeta transform: Theorem 1

* `zeta_linCost`, `zetaInv_linCost` — the recursion of Section 3 over a ring with a Fourier
  character: `O(nk M_q(n,k))` gates, constants among `0, ±1, ψ(x), q⁻¹ψ(x)`.
* `fast_subspace_summation` — **Theorem 1** over any commutative ring in which `p` is
  invertible (through `R[t]/(1 + t + ⋯ + t^{p-1})` and base change), for `Z`, `Z⁻¹`, `Zᵀ`,
  `(Zᵀ)⁻¹` (through the transposition principle); `fast_subspace_summation_log` — the
  `O(M log M)` form.

Theorem 2 is in `Transform/Incidence.lean`.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

section FourierRing

variable {K : Type w} [Field K] [Fintype K] {S : Type*} [CommRing S]

/-- The recursion of Section 3 for `Z`, by strong induction on the dimension. -/
theorem zeta_linCost_aux (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
      finrank K V = n →
      LinCost C (zeta (K := K) (V := V) (R := S) k)
        ((4 * Fintype.card K + 2) * finrank K V * k * Fintype.card (SubLE K V k)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ k hn
  by_cases hbase : k = 0 ∨ finrank K V = 0
  · have := AlgAux.subsingleton_subLE hbase
    exact (LinCost.id.congr AlgAux.zeta_eq_id_of_subsingleton.symm).mono (Nat.zero_le _)
  rw [not_or] at hbase
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨D⟩ := HypData.nonempty (K := K) (V := V) (by omega)
  have hH := D.finrank_H
  have h_in0 := ih (finrank K D.H) (by omega) D.H (k + 1) rfl
  have h_in : LinCost C (fun f₀ : SubLE K D.H (k + 1) → S =>
      Sum.elim (containT (· ≤ k + 1) (· ≤ k + 1) f₀) (containT (· ≤ k + 1) (· ≤ k) f₀)) _ :=
    (h_in0.reindex id (Sum.elim id (StepAux.embLE k))).congr (by funext f₀ o; cases o <;> rfl)
  have h_blk : ∀ ξ : Module.Dual K D.H,
      LinCost C (containT (K := K) (V := LinearMap.ker ξ) (R := S) (· ≤ k) (· ≤ k))
        ((4 * Fintype.card K + 2) * finrank K (LinearMap.ker ξ) * k *
          Fintype.card (SubLE K (LinearMap.ker ξ) k)) := fun ξ =>
    ih (finrank K (LinearMap.ker ξ)) (by have := Submodule.finrank_le (LinearMap.ker ξ); omega)
      (LinearMap.ker ξ) k rfl
  have hstep := containT_step F hC D (P := (· ≤ k + 1)) (P' := (· ≤ k)) (Q := (· ≤ k + 1))
    (Q' := (· ≤ k)) (StepAux.hPk k) (StepAux.hPk k) h_in _ h_blk
  exact hstep.mono (AlgAux.budget_step D k)

/-- **Section 3** over a Fourier ring: `Z_{n,k}` costs at most `(4q+2) n k M_q(n,k)` gates. -/
theorem zeta_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ) :
    LinCost C (zeta (K := K) (V := V) (R := S) k)
      ((4 * Fintype.card K + 2) * finrank K V * k * Fintype.card (SubLE K V k)) :=
  zeta_linCost_aux F hC _ V k rfl

/-- The recursion of equation (5) for `Z⁻¹`, by strong induction on the dimension. -/
theorem zetaInv_linCost_aux (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
      finrank K V = n →
      LinCost C (zetaInv (K := K) (V := V) (R := S) k)
        ((4 * Fintype.card K + 2) * finrank K V * k * Fintype.card (SubLE K V k)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ k hn
  by_cases hbase : k = 0 ∨ finrank K V = 0
  · have := AlgAux.subsingleton_subLE hbase
    exact (LinCost.id.congr AlgAux.zetaInv_eq_id_of_subsingleton.symm).mono (Nat.zero_le _)
  rw [not_or] at hbase
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨D⟩ := HypData.nonempty (K := K) (V := V) (by omega)
  have hH := D.finrank_H
  have h₀ := ih (finrank K D.H) (by omega) D.H (k + 1) rfl
  have h_blk : ∀ ξ : Module.Dual K D.H,
      LinCost C (zetaInv (K := K) (V := LinearMap.ker ξ) (R := S) k)
        ((4 * Fintype.card K + 2) * finrank K (LinearMap.ker ξ) * k *
          Fintype.card (SubLE K (LinearMap.ker ξ) k)) := fun ξ =>
    ih (finrank K (LinearMap.ker ξ)) (by have := Submodule.finrank_le (LinearMap.ker ξ); omega)
      (LinearMap.ker ξ) k rfl
  have hstep := zetaInv_step F hC D k h₀ _ h_blk
  exact hstep.mono (AlgAux.budget_step D k)

/-- **Section 3** (equation (5)): the same bound for `Z_{n,k}⁻¹`. -/
theorem zetaInv_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ) :
    LinCost C (zetaInv (K := K) (V := V) (R := S) k)
      ((4 * Fintype.card K + 2) * finrank K V * k * Fintype.card (SubLE K V k)) :=
  zetaInv_linCost_aux F hC _ V k rfl

end FourierRing

section Ring

variable (K : Type w) [Field K] [Fintype K]

/-- The constant of Theorem 1: base change costs a factor `2(p-1)²` and `(p-1)` gates per
input; transposition doubles the gates and adds one per output. -/
noncomputable def fastConst : ℕ :=
  2 * (2 * (ringChar K - 1) ^ 2 * (4 * Fintype.card K + 2) + (ringChar K - 1)) + 1

/-- `Z` over any ring in which `p` is invertible, through `R[t]/(1 + t + ⋯ + t^{p-1})`. -/
theorem zeta_linCost_ring (R : Type u) [CommRing R] (hR : IsUnit (ringChar K : R))
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ) :
    LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k)
      (2 * (ringChar K - 1) ^ 2 *
          ((4 * Fintype.card K + 2) * finrank K V * k * Fintype.card (SubLE K V k)) +
        (ringChar K - 1) * Fintype.card (SubLE K V k)) := by
  have hp2 : 2 ≤ ringChar K := (CharP.prime_ringChar K).two_le
  have h := zeta_linCost (FourierData.ext K R hR) (C := Set.univ) (Set.subset_univ _) V k
  have hb := LinCost.baseChange (ExtRing.basis R (ringChar K) (by omega)) h ⟨0, by omega⟩
  refine (hb.congr ?_).mono (le_of_eq ?_)
  · funext f o
    rw [AlgAux.zeta_map (algebraMap R (ExtRing R (ringChar K)))]
    exact ExtRing.basis_repr_algebraMap R (ringChar K) hp2 _
  · simp only [Fintype.card_fin]

/-- `Z⁻¹` over any ring in which `p` is invertible. -/
theorem zetaInv_linCost_ring (R : Type u) [CommRing R] (hR : IsUnit (ringChar K : R))
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ) :
    LinCost (Set.univ : Set R) (zetaInv (K := K) (V := V) k)
      (2 * (ringChar K - 1) ^ 2 *
          ((4 * Fintype.card K + 2) * finrank K V * k * Fintype.card (SubLE K V k)) +
        (ringChar K - 1) * Fintype.card (SubLE K V k)) := by
  have hp2 : 2 ≤ ringChar K := (CharP.prime_ringChar K).two_le
  have h := zetaInv_linCost (FourierData.ext K R hR) (C := Set.univ) (Set.subset_univ _) V k
  have hb := LinCost.baseChange (ExtRing.basis R (ringChar K) (by omega)) h ⟨0, by omega⟩
  refine (hb.congr ?_).mono (le_of_eq ?_)
  · funext g o
    rw [AlgAux.zetaInv_map (algebraMap R (ExtRing R (ringChar K)))]
    exact ExtRing.basis_repr_algebraMap R (ringChar K) hp2 _
  · simp only [Fintype.card_fin]

/-- **Theorem 1** with the explicit constant `fastConst K`. -/
theorem fast_subspace_summation_aux (R : Type u) [CommRing R] (hR : IsUnit (ringChar K : R))
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ)
    (hk : k ≤ finrank K V) :
    LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k)
        (fastConst K * finrank K V * k * Fintype.card (SubLE K V k)) ∧
      LinCost (Set.univ : Set R) (zetaInv (K := K) (V := V) k)
        (fastConst K * finrank K V * k * Fintype.card (SubLE K V k)) ∧
      LinCost (Set.univ : Set R) (zetaT (K := K) (V := V) k)
        (fastConst K * finrank K V * k * Fintype.card (SubLE K V k)) ∧
      LinCost (Set.univ : Set R) (zetaTInv (K := K) (V := V) k)
        (fastConst K * finrank K V * k * Fintype.card (SubLE K V k)) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have := AlgAux.subsingleton_subLE (K := K) (V := V) (k := 0) (Or.inl rfl)
    exact ⟨(LinCost.id.congr AlgAux.zeta_eq_id_of_subsingleton.symm).mono (Nat.zero_le _),
      (LinCost.id.congr AlgAux.zetaInv_eq_id_of_subsingleton.symm).mono (Nat.zero_le _),
      (LinCost.id.congr AlgAux.zetaT_eq_id_of_subsingleton.symm).mono (Nat.zero_le _),
      (LinCost.id.congr AlgAux.zetaTInv_eq_id_of_subsingleton.symm).mono (Nat.zero_le _)⟩
  have hnk : 1 ≤ finrank K V * k := Nat.mul_pos (by omega) hk1
  have hz := (zeta_linCost_ring K R hR V k).mono (AlgAux.cost_le _ _ _ _ _ hnk)
  have hzi := (zetaInv_linCost_ring K R hR V k).mono (AlgAux.cost_le _ _ _ _ _ hnk)
  have hzT := ((hz.transpose (Set.mem_univ _) (Set.mem_univ _)).congr
    (AlgAux.transposeMap_zeta k)).mono (AlgAux.cost_le_T _ _ _ _ _ hnk le_rfl)
  have hziT := ((hzi.transpose (Set.mem_univ _) (Set.mem_univ _)).congr
    (AlgAux.transposeMap_zetaInv k)).mono (AlgAux.cost_le_T _ _ _ _ _ hnk le_rfl)
  have hle : (2 * (ringChar K - 1) ^ 2 * (4 * Fintype.card K + 2) + (ringChar K - 1)) *
      finrank K V * k * Fintype.card (SubLE K V k) ≤
      fastConst K * finrank K V * k * Fintype.card (SubLE K V k) := by
    have hA : 2 * (ringChar K - 1) ^ 2 * (4 * Fintype.card K + 2) + (ringChar K - 1) ≤
        fastConst K := by
      unfold fastConst
      omega
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA))
  exact ⟨hz.mono hle, hzi.mono hle, hzT, hziT⟩

end Ring

/-- **Theorem 1 (Fast Subspace Summation).** Over any commutative ring in which
`p = char F_q` is invertible, each of `Z_{n,k}`, `Z_{n,k}⁻¹`, `Z_{n,k}ᵀ`, `(Z_{n,k}ᵀ)⁻¹` can be
applied with `O_q(n k M_q(n, k))` arithmetic operations (gates `z = a x + b y`), `k ≤ n`. -/
theorem fast_subspace_summation (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
        k ≤ finrank K V →
        LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k)
            (C * finrank K V * k * Fintype.card (SubLE K V k)) ∧
          LinCost (Set.univ : Set R) (zetaInv (K := K) (V := V) k)
            (C * finrank K V * k * Fintype.card (SubLE K V k)) ∧
          LinCost (Set.univ : Set R) (zetaT (K := K) (V := V) k)
            (C * finrank K V * k * Fintype.card (SubLE K V k)) ∧
          LinCost (Set.univ : Set R) (zetaTInv (K := K) (V := V) k)
            (C * finrank K V * k * Fintype.card (SubLE K V k)) :=
  ⟨fastConst K, fun R _ hR V _ _ _ k hk => fast_subspace_summation_aux K R hR V k hk⟩

/-- **Theorem 1**, "in particular": `O_q(M log M)` with `M = M_q(n, k)`. -/
theorem fast_subspace_summation_log (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
        k ≤ finrank K V →
        LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k)
            (C * Fintype.card (SubLE K V k) * Nat.log 2 (Fintype.card (SubLE K V k))) ∧
          LinCost (Set.univ : Set R) (zetaInv (K := K) (V := V) k)
            (C * Fintype.card (SubLE K V k) * Nat.log 2 (Fintype.card (SubLE K V k))) ∧
          LinCost (Set.univ : Set R) (zetaT (K := K) (V := V) k)
            (C * Fintype.card (SubLE K V k) * Nat.log 2 (Fintype.card (SubLE K V k))) ∧
          LinCost (Set.univ : Set R) (zetaTInv (K := K) (V := V) k)
            (C * Fintype.card (SubLE K V k) * Nat.log 2 (Fintype.card (SubLE K V k))) := by
  refine ⟨5 * fastConst K, fun R _ hR V _ _ _ k hk => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := fast_subspace_summation_aux K R hR V k hk
  have key : fastConst K * finrank K V * k * Fintype.card (SubLE K V k) ≤
      5 * fastConst K * Fintype.card (SubLE K V k) *
        Nat.log 2 (Fintype.card (SubLE K V k)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [Nat.mul_zero, Nat.zero_mul]
      exact Nat.zero_le _
    · have hlog := mul_le_log_numLE K hk1 hk
      rw [← card_subLE (K := K) (V := V) rfl k] at hlog
      calc fastConst K * finrank K V * k * Fintype.card (SubLE K V k)
          = fastConst K * (finrank K V * k) * Fintype.card (SubLE K V k) := by ring
        _ ≤ fastConst K * (5 * Nat.log 2 (Fintype.card (SubLE K V k))) *
              Fintype.card (SubLE K V k) := by gcongr
        _ = 5 * fastConst K * Fintype.card (SubLE K V k) *
              Nat.log 2 (Fintype.card (SubLE K V k)) := by ring
  exact ⟨h1.mono key, h2.mono key, h3.mono key, h4.mono key⟩

end SubspaceConvolution
