/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Kernel

/-!
# Applications: convolutions, exact spans, distance sums (Sections 1, 5 and Appendix E)

* **Span convolution** (Section 1, "Corollary: Fast Subspace Convolution"): `zetaAll_spanConv`
  (`Z_n (f ⋆ g) = (Z_n f)(Z_n g)`), the inverse `zetaAllInv`, the costs `fast_zetaAll` and
  **`fast_spanConv`** (`O_q(N log N)` operations, `N = N_q(n)`).
* Section 5.1: intersection convolution `interConv` through the upper transform `zetaAllT`
  (`zetaAllT_interConv`, `fast_interConv`); direct sums `directConv` through ranked span
  convolutions (`directConv_eq_coeff`; `directConv_eq_rankConv`, `zetaAll_rankConv` and the
  cost `fast_directConv`, `O_q(n³ N)`).
* **Theorem 5.1** (exact spans): `spanTable`, `zetaAll_spanTable`, equation (exact-span)
  `two_pow_card_eq_sum_spanCount`, `spanCount_eq_zetaAllInv`, `fast_span_count`.
* Appendix E: distance sums `distSum` (`distSum_eq_kernelApply`), equation (profile)
  (`moment_profile`, `interSum_backsubst`), **`fast_distance_sums`** (all `d + 1` of them:
  `distSum_eq_zero_of_lt`); distances to a code
  (`isLeast_distSum_pos`, `sInf_distSum_pos`, `isLeast_minDist`); rectangular kernels,
  equation (rect-moments) (`rect_moments`).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

section Full

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-! ### Transforms on all subspaces -/

/-- Every subspace has dimension at most `n`. -/
def subLETopEquiv : SubLE K V (finrank K V) ≃ Submodule K V :=
  Equiv.subtypeUnivEquiv fun U => Submodule.finrank_le U

/-- `M_q(n, n) = N_q(n)`. -/
theorem card_subLE_top :
    Fintype.card (SubLE K V (finrank K V)) = Fintype.card (Submodule K V) :=
  Fintype.card_congr subLETopEquiv

open Classical in
/-- `Z_n` is `Z_{n,n}` transported along `subLETopEquiv`. -/
theorem zetaAll_eq_zeta (f : Submodule K V → R) (W : Submodule K V) :
    zetaAll f W = zeta (finrank K V) (fun U => f U.1) (subLETopEquiv.symm W) := by
  rw [zetaAll, zeta, sum_filter, sum_filter]
  exact Fintype.sum_equiv subLETopEquiv.symm _ _ fun _ => rfl

/-- The inverse of the full zeta transform `Z_n` (Möbius inversion on all subspaces). -/
noncomputable def zetaAllInv (g : Submodule K V → R) (W : Submodule K V) : R :=
  zetaInv (finrank K V) (fun U => g U.1) (subLETopEquiv.symm W)

/-- `Z_n (Z_n⁻¹ g) = g`. -/
theorem zetaAll_zetaAllInv (g : Submodule K V → R) : zetaAll (zetaAllInv g) = g := by
  funext W
  rw [zetaAll_eq_zeta]
  have : (fun U : SubLE K V (finrank K V) => zetaAllInv g U.1) =
      zetaInv (finrank K V) (fun U => g U.1) := funext fun _ => rfl
  rw [this, zeta_zetaInv]
  rfl

/-- `Z_n⁻¹ (Z_n f) = f`. -/
theorem zetaAllInv_zetaAll (f : Submodule K V → R) : zetaAllInv (zetaAll f) = f := by
  funext W
  unfold zetaAllInv
  have : (fun U : SubLE K V (finrank K V) => zetaAll f U.1) =
      zeta (finrank K V) (fun U => f U.1) := funext fun U => zetaAll_eq_zeta f U.1
  rw [this, zetaInv_zeta]
  rfl

open Classical in
/-- The full upper transform `(Z_nᵀ f)(S) = ∑_{U ⊇ S} f(U)`. -/
noncomputable def zetaAllT (f : Submodule K V → R) (S : Submodule K V) : R :=
  ∑ U ∈ univ.filter (fun U : Submodule K V => S ≤ U), f U

open Classical in
/-- `Z_nᵀ` is `Z_{n,n}ᵀ` transported along `subLETopEquiv`. -/
theorem zetaAllT_eq_zetaT (f : Submodule K V → R) (S : Submodule K V) :
    zetaAllT f S = zetaT (finrank K V) (fun U => f U.1) (subLETopEquiv.symm S) := by
  rw [zetaAllT, zetaT, sum_filter, sum_filter]
  exact Fintype.sum_equiv subLETopEquiv.symm _ _ fun _ => rfl

/-- The inverse of the full upper transform. -/
noncomputable def zetaAllTInv (g : Submodule K V → R) (S : Submodule K V) : R :=
  zetaTInv (finrank K V) (fun U => g U.1) (subLETopEquiv.symm S)

/-- `Z_nᵀ ((Z_nᵀ)⁻¹ g) = g`. -/
theorem zetaAllT_zetaAllTInv (g : Submodule K V → R) : zetaAllT (zetaAllTInv g) = g := by
  funext W
  rw [zetaAllT_eq_zetaT]
  have : (fun U : SubLE K V (finrank K V) => zetaAllTInv g U.1) =
      zetaTInv (finrank K V) (fun U => g U.1) := funext fun _ => rfl
  rw [this, zetaT_zetaTInv]
  rfl

/-- `(Z_nᵀ)⁻¹ (Z_nᵀ f) = f`. -/
theorem zetaAllTInv_zetaAllT (f : Submodule K V → R) : zetaAllTInv (zetaAllT f) = f := by
  funext W
  unfold zetaAllTInv
  have : (fun U : SubLE K V (finrank K V) => zetaAllT f U.1) =
      zetaT (finrank K V) (fun U => f U.1) := funext fun U => zetaAllT_eq_zetaT f U.1
  rw [this, zetaTInv_zetaT]
  rfl

/-! ### Convolutions -/

open Classical in
/-- `Z_n (f ⋆ g) = (Z_n f)(Z_n g)`: `U + U' ≤ W` exactly when `U, U' ≤ W`. -/
theorem zetaAll_spanConv (f g : Submodule K V → R) (W : Submodule K V) :
    zetaAll (spanConv f g) W = zetaAll f W * zetaAll g W := by
  unfold zetaAll spanConv
  calc ∑ S ∈ univ.filter (fun S : Submodule K V => S ≤ W), ∑ U, ∑ U',
        (if U ⊔ U' = S then f U * g U' else 0)
      = ∑ U, ∑ U', ∑ S ∈ univ.filter (fun S : Submodule K V => S ≤ W),
          (if U ⊔ U' = S then f U * g U' else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun U _ => sum_comm
    _ = ∑ U, ∑ U', (if U ≤ W ∧ U' ≤ W then f U * g U' else 0) := by
        refine sum_congr rfl fun U _ => sum_congr rfl fun U' _ => ?_
        simp only [sum_ite_eq, mem_filter, mem_univ, true_and, sup_le_iff]
    _ = (∑ U ∈ univ.filter (fun U : Submodule K V => U ≤ W), f U) *
          ∑ U' ∈ univ.filter (fun U' : Submodule K V => U' ≤ W), g U' := by
        rw [sum_mul_sum, sum_filter]
        refine sum_congr rfl fun U _ => ?_
        by_cases hU : U ≤ W
        · simp [hU, sum_filter]
        · simp [hU]

open Classical in
/-- Intersection convolution `(f ⋆_∩ g)(S) = ∑_{U ∩ W = S} f(U) g(W)` (Section 5.1). -/
noncomputable def interConv (f g : Submodule K V → R) (S : Submodule K V) : R :=
  ∑ U, ∑ W, if U ⊓ W = S then f U * g W else 0

open Classical in
/-- `Z_nᵀ (f ⋆_∩ g) = (Z_nᵀ f)(Z_nᵀ g)`: `S ≤ U ∩ U'` exactly when `S ≤ U, U'`. -/
theorem zetaAllT_interConv (f g : Submodule K V → R) (S : Submodule K V) :
    zetaAllT (interConv f g) S = zetaAllT f S * zetaAllT g S := by
  unfold zetaAllT interConv
  calc ∑ T ∈ univ.filter (fun T : Submodule K V => S ≤ T), ∑ U, ∑ U',
        (if U ⊓ U' = T then f U * g U' else 0)
      = ∑ U, ∑ U', ∑ T ∈ univ.filter (fun T : Submodule K V => S ≤ T),
          (if U ⊓ U' = T then f U * g U' else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun U _ => sum_comm
    _ = ∑ U, ∑ U', (if S ≤ U ∧ S ≤ U' then f U * g U' else 0) := by
        refine sum_congr rfl fun U _ => sum_congr rfl fun U' _ => ?_
        simp only [sum_ite_eq, mem_filter, mem_univ, true_and, le_inf_iff]
    _ = (∑ U ∈ univ.filter (fun U : Submodule K V => S ≤ U), f U) *
          ∑ U' ∈ univ.filter (fun U' : Submodule K V => S ≤ U'), g U' := by
        rw [sum_mul_sum, sum_filter]
        refine sum_congr rfl fun U _ => ?_
        by_cases hU : S ≤ U
        · simp [hU, sum_filter]
        · simp [hU]

open Classical in
/-- Direct-sum convolution `∑_{U ⊕ W = S} f(U) g(W)` (Section 5.1). -/
noncomputable def directConv (f g : Submodule K V → R) (S : Submodule K V) : R :=
  ∑ U, ∑ W, if U ⊔ W = S ∧ U ⊓ W = ⊥ then f U * g W else 0

open Polynomial in
/-- Section 5.1, ranked transforms: weight `f(U)` by `z^{dim U}`; the direct sums are the
coefficient of `z^{dim S}` of the span convolution, since
`dim U + dim W = dim(U + W) + dim(U ∩ W)`. -/
theorem directConv_eq_coeff (f g : Submodule K V → R) (S : Submodule K V) :
    directConv f g S =
      (spanConv (fun U => C (f U) * X ^ finrank K U) (fun W => C (g W) * X ^ finrank K W)
        S).coeff (finrank K S) := by
  classical
  unfold directConv spanConv
  rw [finsetSum_coeff]
  refine sum_congr rfl fun U _ => ?_
  rw [finsetSum_coeff]
  refine sum_congr rfl fun W _ => ?_
  by_cases h : U ⊔ W = S
  · have hdim := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [h] at hdim
    have hmul : C (f U) * X ^ finrank K U * (C (g W) * X ^ finrank K W) =
        C (f U * g W) * X ^ (finrank K U + finrank K W) := by
      rw [C_mul, pow_add]; ring
    rw [ite_eq_left h, hmul, coeff_C_mul_X_pow]
    by_cases h' : U ⊓ W = ⊥
    · have h0 : finrank K (U ⊓ W : Submodule K V) = 0 := Submodule.finrank_eq_zero.2 h'
      rw [ite_eq_left ⟨h, h'⟩, ite_eq_left (by omega)]
    · have h0 : finrank K (U ⊓ W : Submodule K V) ≠ 0 := fun h0 =>
        h' (Submodule.finrank_eq_zero.1 h0)
      rw [ite_eq_right (fun h'' => h' h''.2), ite_eq_right (by omega)]
  · rw [ite_eq_right (fun h'' => h h''.1), ite_eq_right h, coeff_zero]

end Full

/-! ### Costs of the full transforms and convolutions -/

/-- **Theorem 1.1 for `k = n`**: the full transforms `Z_n`, `Z_n⁻¹`, `Z_nᵀ`, `(Z_nᵀ)⁻¹` on all
subspaces cost `O_q(N log N)`, `N = N_q(n)`. -/
theorem fast_zetaAll (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
        LinCost (Set.univ : Set R) (zetaAll (K := K) (V := V))
            (C * Fintype.card (Submodule K V) * (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) ∧
          LinCost (Set.univ : Set R) (zetaAllInv (K := K) (V := V))
            (C * Fintype.card (Submodule K V) * (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) ∧
          LinCost (Set.univ : Set R) (zetaAllT (K := K) (V := V))
            (C * Fintype.card (Submodule K V) * (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) ∧
          LinCost (Set.univ : Set R) (zetaAllTInv (K := K) (V := V))
            (C * Fintype.card (Submodule K V) *
              (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) := by
  obtain ⟨C, hC⟩ := fast_subspace_summation_log.{u, v, w} K
  refine ⟨C, fun R _ hR V _ _ _ => ?_⟩
  have h := hC R hR V (finrank K V) le_rfl
  rw [card_subLE_top] at h
  have hb : C * Fintype.card (Submodule K V) * Nat.log 2 (Fintype.card (Submodule K V)) ≤
      C * Fintype.card (Submodule K V) * (Nat.log 2 (Fintype.card (Submodule K V)) + 1) := by
    gcongr; omega
  refine ⟨((h.1.reindex Subtype.val subLETopEquiv.symm).congr ?_).mono hb,
    ((h.2.1.reindex Subtype.val subLETopEquiv.symm).congr ?_).mono hb,
    ((h.2.2.1.reindex Subtype.val subLETopEquiv.symm).congr ?_).mono hb,
    ((h.2.2.2.reindex Subtype.val subLETopEquiv.symm).congr ?_).mono hb⟩
  · funext f W
    exact (zetaAll_eq_zeta f W).symm
  · rfl
  · funext f W
    exact (zetaAllT_eq_zetaT f W).symm
  · rfl

/-- Three transforms and one product per entry. -/
theorem conv_bound {C N L : ℕ} : C * N * (L + 1) + C * N * (L + 1) + N + C * N * (L + 1) ≤
    (3 * C + 1) * N * (L + 1) := by
  have : N ≤ N * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  nlinarith

/-- **Fast subspace convolution** (Section 1): two transforms, one pointwise product, one
inverse transform: `O_q(N log N)` operations, `N = N_q(n)`. -/
theorem fast_spanConv (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
        ArithCost (fun (x : Submodule K V ⊕ Submodule K V → R) =>
            spanConv (fun U => x (.inl U)) (fun U => x (.inr U)))
          (C * Fintype.card (Submodule K V) *
            (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) := by
  obtain ⟨C, hC⟩ := fast_zetaAll.{u, v, w} K
  refine ⟨3 * C + 1, fun R _ hR V _ _ _ => ?_⟩
  obtain ⟨h1, h2, -, -⟩ := hC R hR V
  have hA := (h1.reindex (I' := Submodule K V ⊕ Submodule K V) Sum.inl id).sumElim
    (h1.reindex (I' := Submodule K V ⊕ Submodule K V) Sum.inr id)
  have hB := (ArithCost.of_linCost hA).comp (ArithCost.mulPointwise (R := R) (J := Submodule K V))
  have hD := hB.comp (ArithCost.of_linCost h2)
  refine (hD.congr ?_).mono conv_bound
  funext x
  rw [← zetaAllInv_zetaAll (spanConv _ _)]
  congr 1
  funext W
  rw [zetaAll_spanConv]
  rfl

/-- **Fast intersection convolution** (Section 5.1), with upper transforms. -/
theorem fast_interConv (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
        ArithCost (fun (x : Submodule K V ⊕ Submodule K V → R) =>
            interConv (fun U => x (.inl U)) (fun U => x (.inr U)))
          (C * Fintype.card (Submodule K V) *
            (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) := by
  obtain ⟨C, hC⟩ := fast_zetaAll.{u, v, w} K
  refine ⟨3 * C + 1, fun R _ hR V _ _ _ => ?_⟩
  obtain ⟨-, -, h1, h2⟩ := hC R hR V
  have hA := (h1.reindex (I' := Submodule K V ⊕ Submodule K V) Sum.inl id).sumElim
    (h1.reindex (I' := Submodule K V ⊕ Submodule K V) Sum.inr id)
  have hB := (ArithCost.of_linCost hA).comp (ArithCost.mulPointwise (R := R) (J := Submodule K V))
  have hD := hB.comp (ArithCost.of_linCost h2)
  refine (hD.congr ?_).mono conv_bound
  funext x
  rw [← zetaAllTInv_zetaAllT (interConv _ _)]
  congr 1
  funext W
  rw [zetaAllT_interConv]
  rfl

/-! ### Section 5.1: direct sums by ranked transforms -/

section Ranked

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

open Classical in
/-- The rank-`r` part of a table. -/
noncomputable def rankPart (r : ℕ) (f : Submodule K V → R) (U : Submodule K V) : R :=
  if finrank K U = r then f U else 0

open Classical in
/-- The rank-graded span convolution `D_m(S) = ∑_{U + W = S, dim U + dim W = m} f(U) g(W)`. -/
noncomputable def rankConv (m : ℕ) (f g : Submodule K V → R) (S : Submodule K V) : R :=
  ∑ U, ∑ W, if U ⊔ W = S ∧ finrank K U + finrank K W = m then f U * g W else 0

/-- Direct sums are the rank-graded convolution at degree `dim S`, since
`dim U + dim W = dim(U + W) + dim(U ∩ W)`. -/
theorem directConv_eq_rankConv (f g : Submodule K V → R) (S : Submodule K V) :
    directConv f g S = rankConv (finrank K S) f g S := by
  classical
  unfold directConv rankConv
  refine sum_congr rfl fun U _ => sum_congr rfl fun W _ => ?_
  by_cases h : U ⊔ W = S
  · have hdim := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [h] at hdim
    have hiff : U ⊓ W = ⊥ ↔ finrank K U + finrank K W = finrank K S := by
      rw [← Submodule.finrank_eq_zero]
      omega
    by_cases h' : U ⊓ W = ⊥
    · rw [ite_eq_left ⟨h, h'⟩, ite_eq_left ⟨h, hiff.1 h'⟩]
    · rw [ite_eq_right (fun h'' => h' h''.2), ite_eq_right (fun h'' => h' (hiff.2 h''.2))]
  · rw [ite_eq_right (fun h'' => h h''.1), ite_eq_right (fun h'' => h h''.1)]

open Classical in
/-- `(Z_n D_m)(W) = ∑_{U, U' ≤ W, dim U + dim U' = m} f(U) g(U')`. -/
theorem zetaAll_rankConv_aux (m : ℕ) (f g : Submodule K V → R) (W : Submodule K V) :
    zetaAll (rankConv m f g) W = ∑ U, ∑ U',
      if U ≤ W ∧ U' ≤ W ∧ finrank K U + finrank K U' = m then f U * g U' else 0 := by
  unfold zetaAll rankConv
  rw [sum_comm]
  refine sum_congr rfl fun U _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun U' _ => ?_
  simp only [ite_and, sum_ite_eq, mem_filter, mem_univ, true_and, sup_le_iff]

open Classical in
/-- The transform of a rank part. -/
theorem zetaAll_rankPart (r : ℕ) (f : Submodule K V → R) (W : Submodule K V) :
    zetaAll (rankPart r f) W = ∑ U, if U ≤ W ∧ finrank K U = r then f U else 0 := by
  unfold zetaAll rankPart
  rw [sum_filter]
  refine sum_congr rfl fun U _ => ?_
  by_cases hU : U ≤ W <;> simp [hU]

open Classical in
/-- `Z_n D_m = ∑_{r + s = m} (Z_n f_r)(Z_n g_s)`: the coefficientwise transforms multiply as
polynomials in the rank. -/
theorem zetaAll_rankConv (m : ℕ) (f g : Submodule K V → R) (W : Submodule K V) :
    zetaAll (rankConv m f g) W =
      ∑ p : Fin (finrank K V + 1) × Fin (finrank K V + 1),
        if (p.1 : ℕ) + p.2 = m then zetaAll (rankPart p.1 f) W * zetaAll (rankPart p.2 g) W
        else 0 := by
  have h1 : ∀ p : Fin (finrank K V + 1) × Fin (finrank K V + 1),
      (if (p.1 : ℕ) + p.2 = m then zetaAll (rankPart p.1 f) W * zetaAll (rankPart p.2 g) W
        else 0) = ∑ U, ∑ U', if ((p.1 : ℕ) + p.2 = m ∧ (U ≤ W ∧ finrank K U = p.1) ∧
          (U' ≤ W ∧ finrank K U' = p.2)) then f U * g U' else 0 := by
    intro p
    rw [zetaAll_rankPart, zetaAll_rankPart, sum_mul_sum]
    simp only [ite_zero_mul_ite_zero]
    by_cases hp : (p.1 : ℕ) + p.2 = m
    · simp only [hp, true_and, ite_eq_left]
    · simp [hp]
  rw [zetaAll_rankConv_aux, sum_congr rfl fun p _ => h1 p]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun U _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun U' _ => ?_
  have hU := Nat.lt_succ_of_le (Submodule.finrank_le U)
  have hU' := Nat.lt_succ_of_le (Submodule.finrank_le U')
  rw [Fintype.sum_eq_single (⟨⟨finrank K U, hU⟩, ⟨finrank K U', hU'⟩⟩ :
    Fin (finrank K V + 1) × Fin (finrank K V + 1))]
  · by_cases hW : U ≤ W ∧ U' ≤ W ∧ finrank K U + finrank K U' = m
    · rw [ite_eq_left hW, ite_eq_left ⟨hW.2.2, ⟨hW.1, rfl⟩, ⟨hW.2.1, rfl⟩⟩]
    · rw [ite_eq_right hW, ite_eq_right]
      rintro ⟨h1, ⟨h2, -⟩, ⟨h3, -⟩⟩
      exact hW ⟨h2, h3, h1⟩
  · intro p hp
    rw [ite_eq_right]
    rintro ⟨-, ⟨-, h2⟩, ⟨-, h3⟩⟩
    exact hp (Prod.ext (Fin.ext h2.symm) (Fin.ext h3.symm))

/-- Taking the rank-`r` part is free. -/
theorem rankPart_linCost (r : ℕ) :
    LinCost (Set.univ : Set R) (rankPart (K := K) (V := V) (R := R) r) 0 := by
  classical
  have h := (LinCost.sumElim (LinCost.id (C := (Set.univ : Set R)) (I := Submodule K V))
    (LinCost.zero (C := (Set.univ : Set R)) (I := Submodule K V) (O := Unit))).reindex id
    (fun U : Submodule K V => if finrank K U = r then Sum.inl U else Sum.inr ())
  refine (h.congr ?_).mono (by norm_num)
  funext f U
  simp only [rankPart]
  split_ifs <;> rfl

/-- The circuit of Section 5.1 for direct sums: `2(n+1)` transforms of the rank parts,
`(n+1)²` products per subspace, schoolbook polynomial multiplication, `2n+1` inverse
transforms. -/
theorem directConv_arithCost_of {s₁ s₂ : ℕ}
    (h₁ : LinCost (Set.univ : Set R) (zetaAll (K := K) (V := V)) s₁)
    (h₂ : LinCost (Set.univ : Set R) (zetaAllInv (K := K) (V := V)) s₂) :
    ArithCost (fun (x : Submodule K V ⊕ Submodule K V → R) =>
        directConv (fun U => x (.inl U)) (fun U => x (.inr U)))
      ((finrank K V + 1) * s₁ + (finrank K V + 1) * s₁ +
        (finrank K V + 1) * (finrank K V + 1) * Fintype.card (Submodule K V) +
        Fintype.card (Submodule K V) *
          ((2 * finrank K V + 1) * ((finrank K V + 1) * (finrank K V + 1))) +
        (2 * finrank K V + 1) * s₂) := by
  classical
  set n := finrank K V with hn
  -- Stage A: the rank parts and their transforms
  have hA1 : ∀ r : Fin (n + 1),
      LinCost (Set.univ : Set R) (fun f : Submodule K V → R => zetaAll (rankPart r f)) s₁ :=
    fun r => ((rankPart_linCost (K := K) (V := V) (R := R) r).comp h₁).mono (by omega)
  have hA2 := (LinCost.sigma (C := (Set.univ : Set R)) (ι := Fin (n + 1))
    (I' := fun _ => Submodule K V) (O' := fun _ => Submodule K V)
    (fun r f => zetaAll (rankPart r f)) (fun _ => s₁) hA1).reindex
    (I' := Submodule K V) (O' := Fin (n + 1) × Submodule K V) Sigma.snd (fun p => ⟨p.1, p.2⟩)
  have hA := (hA2.reindex (I' := Submodule K V ⊕ Submodule K V) Sum.inl id).sumElim
    (hA2.reindex (I' := Submodule K V ⊕ Submodule K V) Sum.inr id)
  -- Stage B: products
  have hB := (ArithCost.mulPointwise (R := R)
    (J := Fin (n + 1) × Fin (n + 1) × Submodule K V)).reindex
    (I' := (Fin (n + 1) × Submodule K V) ⊕ (Fin (n + 1) × Submodule K V))
    (Sum.elim (fun q => Sum.inl (q.1, q.2.2)) (fun q => Sum.inr (q.2.1, q.2.2))) id
  -- Stage C: schoolbook polynomial multiplication
  have hC1 : ∀ _W : Submodule K V, LinCost (Set.univ : Set R)
      (fun (z : Fin (n + 1) × Fin (n + 1) → R) (m : Fin (2 * n + 1)) =>
        ∑ p, (if (p.1 : ℕ) + p.2 = m then (1 : R) else 0) * z p)
      ((2 * n + 1) * ((n + 1) * (n + 1))) := fun _ => by
    have := LinCost.dense (C := (Set.univ : Set R))
      (fun (m : Fin (2 * n + 1)) (p : Fin (n + 1) × Fin (n + 1)) =>
        if (p.1 : ℕ) + p.2 = m then (1 : R) else 0) (fun _ _ => trivial) trivial trivial
    refine this.mono (le_of_eq ?_)
    simp [Fintype.card_prod, Fintype.card_fin]
  have hC := (LinCost.sigma (C := (Set.univ : Set R)) (ι := Submodule K V)
    (I' := fun _ => Fin (n + 1) × Fin (n + 1)) (O' := fun _ => Fin (2 * n + 1))
    (fun _ z m => ∑ p, (if (p.1 : ℕ) + p.2 = m then (1 : R) else 0) * z p)
    (fun _ => (2 * n + 1) * ((n + 1) * (n + 1))) hC1).reindex
    (I' := Fin (n + 1) × Fin (n + 1) × Submodule K V) (O' := Fin (2 * n + 1) × Submodule K V)
    (fun q => (q.2.1, q.2.2, q.1)) (fun p => ⟨p.2, p.1⟩)
  -- Stage D: inverse transforms, one per degree
  have hD := (LinCost.sigma (C := (Set.univ : Set R)) (ι := Fin (2 * n + 1))
    (I' := fun _ => Submodule K V) (O' := fun _ => Submodule K V)
    (fun _ => zetaAllInv) (fun _ => s₂) (fun _ => h₂)).reindex
    (I' := Fin (2 * n + 1) × Submodule K V) (O' := Submodule K V)
    (fun q => (q.1, q.2))
    (fun S => ⟨⟨finrank K S, by have := Submodule.finrank_le S; omega⟩, S⟩)
  have h := (((ArithCost.of_linCost hA).comp hB).comp (ArithCost.of_linCost hC)).comp
    (ArithCost.of_linCost hD)
  refine (h.congr ?_).mono (le_of_eq ?_)
  · funext x S
    rw [directConv_eq_rankConv, ← zetaAllInv_zetaAll (rankConv _ _ _)]
    refine congrArg (fun F => zetaAllInv F S) (funext fun W => ?_)
    rw [zetaAll_rankConv]
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  · simp [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    ring

end Ranked

/-- Theorem 1.1 for `k = n` in the form `O(n² N)`. -/
theorem fast_zetaAll_sq (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
        LinCost (Set.univ : Set R) (zetaAll (K := K) (V := V))
            (C * finrank K V * finrank K V * Fintype.card (Submodule K V)) ∧
          LinCost (Set.univ : Set R) (zetaAllInv (K := K) (V := V))
            (C * finrank K V * finrank K V * Fintype.card (Submodule K V)) := by
  obtain ⟨C, hC⟩ := fast_subspace_summation.{u, v, w} K
  refine ⟨C, fun R _ hR V _ _ _ => ?_⟩
  have h := hC R hR V (finrank K V) le_rfl
  rw [card_subLE_top] at h
  exact ⟨(h.1.reindex Subtype.val subLETopEquiv.symm).congr
      (funext fun f => funext fun W => (zetaAll_eq_zeta f W).symm),
    (h.2.1.reindex Subtype.val subLETopEquiv.symm).congr rfl⟩

/-- The operation count of `directConv_arithCost_of` is `O((n+1)³ N)`. -/
theorem directConv_bound (C n N : ℕ) :
    (n + 1) * (C * n * n * N) + (n + 1) * (C * n * n * N) + (n + 1) * (n + 1) * N +
        N * ((2 * n + 1) * ((n + 1) * (n + 1))) + (2 * n + 1) * (C * n * n * N) ≤
      (4 * C + 3) * (n + 1) ^ 3 * N := by
  have : (4 * C + 3) * (n + 1) ^ 3 * N =
      ((n + 1) * (C * n * n * N) + (n + 1) * (C * n * n * N) + (n + 1) * (n + 1) * N +
        N * ((2 * n + 1) * ((n + 1) * (n + 1))) + (2 * n + 1) * (C * n * n * N)) +
      N * (C * (9 * n * n + 12 * n + 4) + (n + 1) ^ 3) := by ring
  rw [this]
  exact Nat.le_add_right _ _

/-- **Direct-sum convolution** (Section 5.1): coefficientwise transforms and schoolbook
polynomial multiplication give `O_q(n³ N)` operations, `N = N_q(n)` (written `(n+1)³` to cover
`n = 0`). -/
theorem fast_directConv (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
        ArithCost (fun (x : Submodule K V ⊕ Submodule K V → R) =>
            directConv (fun U => x (.inl U)) (fun U => x (.inr U)))
          (C * (finrank K V + 1) ^ 3 * Fintype.card (Submodule K V)) := by
  obtain ⟨C, hC⟩ := fast_zetaAll_sq.{u, v, w} K
  refine ⟨4 * C + 3, fun R _ hR V _ _ _ => ?_⟩
  obtain ⟨h1, h2⟩ := hC R hR V
  exact (directConv_arithCost_of h1 h2).mono (directConv_bound C _ _)

/-! ### Theorem 5.1: counting subsets by their exact span -/

section ExactSpan

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

open Classical in
/-- `t(B) = #{i : ⟨v_i⟩ = B}`. -/
noncomputable def spanTable {ℓ : ℕ} (v : Fin ℓ → V) (B : Submodule K V) : ℕ :=
  #(univ.filter fun i => K ∙ v i = B)

/-- `t` is supported on the zero subspace and the lines. -/
theorem finrank_le_one_of_spanTable_ne_zero {ℓ : ℕ} (v : Fin ℓ → V) (B : Submodule K V)
    (h : spanTable v B ≠ 0) : finrank K B ≤ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, K ∙ v i = B := by
    by_contra hcon
    push Not at hcon
    apply h
    rw [spanTable, card_eq_zero, filter_eq_empty_iff]
    exact fun i _ => hcon i
  rw [← hi]
  by_cases hv : v i = 0
  · rw [hv, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]
    exact zero_le_one
  · rw [finrank_span_singleton hv]

/-- `∑_B t(B) = ℓ`. -/
theorem sum_spanTable {ℓ : ℕ} (v : Fin ℓ → V) : ∑ B : Submodule K V, spanTable v B = ℓ := by
  classical
  unfold spanTable
  rw [← card_eq_sum_card_fiberwise (f := fun i => K ∙ v i) (s := univ) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _)), card_univ, Fintype.card_fin]

open Classical in
/-- `a(U) = (Z_n t)(U) = #{i : v_i ∈ U}`. -/
theorem zetaAll_spanTable {ℓ : ℕ} (v : Fin ℓ → V) (U : Submodule K V) :
    zetaAll (fun B => (spanTable v B : R)) U = (#(univ.filter fun i => v i ∈ U) : R) := by
  unfold zetaAll spanTable
  rw [← Nat.cast_sum]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := fun i => K ∙ v i)
    (t := univ.filter fun B : Submodule K V => B ≤ U)]
  · refine sum_congr rfl fun B hB => ?_
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, h⟩
      rw [← Submodule.span_singleton_le_iff_mem, h]
      exact (mem_filter.1 hB).2
    · exact fun h => h.2
  · intro i hi
    have hi' : v i ∈ U := (mem_filter.1 hi).2
    exact mem_filter.2 ⟨mem_univ _, (Submodule.span_singleton_le_iff_mem _ _).2 hi'⟩

open Classical in
/-- Equation (exact-span): `2^{a(U)} = ∑_{W ≤ U} C(W)`. -/
theorem two_pow_card_eq_sum_spanCount {ℓ : ℕ} (v : Fin ℓ → V) (U : Submodule K V) :
    2 ^ #(univ.filter fun i => v i ∈ U) =
      ∑ W ∈ univ.filter (fun W : Submodule K V => W ≤ U), spanCount v W := by
  unfold spanCount
  have h1 : (univ.filter fun i => v i ∈ U).powerset =
      univ.filter fun A : Finset (Fin ℓ) => Submodule.span K (v '' (A : Set (Fin ℓ))) ≤ U := by
    ext A
    simp only [mem_powerset, mem_filter, mem_univ, true_and, Submodule.span_le,
      Set.image_subset_iff]
    constructor
    · intro h i hi
      exact (mem_filter.1 (h hi)).2
    · intro h i hi
      exact mem_filter.2 ⟨mem_univ _, h hi⟩
  rw [← card_powerset, h1, card_eq_sum_card_fiberwise
    (f := fun A : Finset (Fin ℓ) => Submodule.span K (v '' (A : Set (Fin ℓ))))
    (t := univ.filter fun W : Submodule K V => W ≤ U)]
  · refine sum_congr rfl fun W hW => ?_
    congr 1
    ext A
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact (mem_filter.1 hW).2
  · intro A hA
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hA).2⟩

open Classical in
/-- `C = Z_n⁻¹ (U ↦ 2^{a(U)})`. -/
theorem spanCount_eq_zetaAllInv {ℓ : ℕ} (v : Fin ℓ → V) :
    (fun U : Submodule K V => (spanCount v U : R)) =
      zetaAllInv (fun U : Submodule K V => (2 : R) ^ #(univ.filter fun i => v i ∈ U)) := by
  rw [← zetaAllInv_zetaAll (fun U : Submodule K V => (spanCount v U : R))]
  congr 1
  funext U
  rw [zetaAll, ← Nat.cast_sum, ← two_pow_card_eq_sum_spanCount]
  push_cast
  rfl

end ExactSpan

open Classical in
/-- **Theorem 5.1 (Counting exact spans).** Over `ℚ`, for vectors `v_1, …, v_ℓ` of `V = F_q^n`:
`a = Z_n t` counts the vectors in each subspace (`t(B) = #{i : ⟨v_i⟩ = B}`), and the exact-span
counts are `C = Z_n⁻¹ (U ↦ 2^{a(U)})`; each of the two transforms costs `O_q(N log N)`
operations, `N = N_q(n)`.  Building `t` takes `ℓ` additions (once the vectors are indexed by their
spans) and the powers `2^0, …, 2^ℓ` take `ℓ` doublings; the table lookups `U ↦ 2^{a(U)}` by the
integer `a(U)` are not arithmetic operations.  Hence `O_q(ℓ + N log N)` operations in total. -/
theorem fast_span_count (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      LinCost (Set.univ : Set ℚ) (zetaAll (K := K) (V := V))
          (C * Fintype.card (Submodule K V) * (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) ∧
        LinCost (Set.univ : Set ℚ) (zetaAllInv (K := K) (V := V))
          (C * Fintype.card (Submodule K V) * (Nat.log 2 (Fintype.card (Submodule K V)) + 1)) ∧
        ∀ {ℓ : ℕ} (v : Fin ℓ → V),
          (∀ U : Submodule K V, zetaAll (fun B : Submodule K V => (spanTable v B : ℚ)) U =
            (#(univ.filter fun i => v i ∈ U) : ℚ)) ∧
          (fun U : Submodule K V => (spanCount v U : ℚ)) =
            zetaAllInv (fun U : Submodule K V => (2 : ℚ) ^ #(univ.filter fun i => v i ∈ U)) := by
  obtain ⟨C, hC⟩ := fast_zetaAll.{0, v, w} K
  refine ⟨C, fun V _ _ _ => ?_⟩
  have hp : IsUnit (ringChar K : ℚ) :=
    isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (CharP.ringChar_ne_zero_of_finite K))
  obtain ⟨h1, h2, -, -⟩ := hC ℚ hp V
  exact ⟨h1, h2, fun v => ⟨zetaAll_spanTable v, spanCount_eq_zetaAllInv v⟩⟩

/-! ### Appendix E: distance sums -/

section DistanceSums

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

open Classical in
/-- The distance sums `(D_i f)(U) = ∑_{dist(U,W) = i} f(W)`. -/
noncomputable def distSum (k i : ℕ) (f : Grass K V k → R) (U : Grass K V k) : R :=
  ∑ W ∈ univ.filter (fun W => gDist k U W = i), f W

/-- `D_i` is the intersection kernel with `a_j = [j = i]`. -/
theorem distSum_eq_kernelApply (k i : ℕ) :
    distSum (K := K) (V := V) (R := R) k i = kernelApply k (fun j => if j = i then 1 else 0) := by
  classical
  funext f U
  unfold distSum kernelApply
  rw [sum_filter]
  refine sum_congr rfl fun W _ => ?_
  by_cases h : gDist k U W = i <;> simp [h]

open Classical in
/-- `h_t(U) = ∑_{dim(U ∩ W) = t} f(W)`. -/
noncomputable def interSum (k t : ℕ) (f : Grass K V k → R) (U : Grass K V k) : R :=
  ∑ W ∈ univ.filter (fun W : Grass K V k => finrank K (U.1 ⊓ W.1 : Submodule K V) = t), f W

/-- `m_j(U) = ∑_W |Gr(dim(U ∩ W), j)| f(W)`, computed by equation (moments). -/
noncomputable def momentSum (k j : ℕ) (f : Grass K V k → R) (U : Grass K V k) : R :=
  ∑ W : Grass K V k, (gr K (finrank K (U.1 ⊓ W.1 : Submodule K V)) j : R) * f W

open Classical in
/-- Equation (moments): `m_j` from the upper transform. -/
theorem momentSum_eq (k j : ℕ) (hj : j ≤ k) (f : Grass K V k → R) (U : Grass K V k) :
    momentSum k j f U = ∑ L ∈ univ.filter (fun L : Grass K V j => L.1 ≤ U.1),
      zetaT k (extGr k f) ⟨L.1, L.2.le.trans hj⟩ :=
  (moments k j hj f U).symm

/-- Equation (profile): `m_j(U) = ∑_{t=j}^{k} |Gr(t,j)| h_t(U)`. -/
theorem moment_profile (k j : ℕ) (f : Grass K V k → R) (U : Grass K V k) :
    momentSum k j f U = ∑ t ∈ Icc j k, (gr K t j : R) * interSum k t f U := by
  classical
  unfold momentSum interSum
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (k + 1))
    (g := fun W : Grass K V k => finrank K (U.1 ⊓ W.1 : Submodule K V))
    (fun W _ => mem_range.2 (Nat.lt_succ_of_le (finrank_inf_le_of_grass k U W)))]
  have h1 : ∀ t ∈ range (k + 1),
      ∑ W ∈ univ.filter (fun W : Grass K V k => finrank K (U.1 ⊓ W.1 : Submodule K V) = t),
        (gr K (finrank K (U.1 ⊓ W.1 : Submodule K V)) j : R) * f W =
      (gr K t j : R) * ∑ W ∈ univ.filter
        (fun W : Grass K V k => finrank K (U.1 ⊓ W.1 : Submodule K V) = t), f W := by
    intro t _
    rw [mul_sum]
    refine sum_congr rfl fun W hW => ?_
    rw [(mem_filter.1 hW).2]
  rw [sum_congr rfl h1]
  symm
  refine sum_subset (fun t ht => ?_) fun t ht1 ht2 => ?_
  · rw [mem_Icc] at ht
    exact mem_range.2 (by omega)
  · have : t < j := by
      rw [mem_range] at ht1
      rw [mem_Icc] at ht2
      omega
    rw [gr_eq_zero_of_lt K this, Nat.cast_zero, zero_mul]

/-- No intersection has dimension above `k`. -/
theorem interSum_eq_zero_of_lt (k t : ℕ) (ht : k < t) (f : Grass K V k → R) (U : Grass K V k) :
    interSum k t f U = 0 := by
  classical
  unfold interSum
  refine sum_eq_zero fun W hW => ?_
  have := finrank_inf_le_of_grass k U W
  rw [(mem_filter.1 hW).2] at this
  omega

/-- Equation (profile), back-substitution: `h_t = m_t - ∑_{r=t+1}^{k} |Gr(r,t)| h_r`. -/
theorem interSum_backsubst (k t : ℕ) (f : Grass K V k → R) (U : Grass K V k) :
    interSum k t f U = momentSum k t f U - ∑ r ∈ Ioc t k, (gr K r t : R) * interSum k r f U := by
  rw [moment_profile]
  by_cases ht : t ≤ k
  · rw [Icc_eq_cons_Ioc ht, sum_cons, gr_self, Nat.cast_one, one_mul]
    ring
  · rw [Icc_eq_empty (by omega), Ioc_eq_empty (by omega)]
    simp only [sum_empty, sub_zero]
    exact interSum_eq_zero_of_lt k t (by omega) f U

/-- The distance sums are the sums by intersection dimension: `D_i f = h_{k-i}`. -/
theorem distSum_eq_interSum (k i : ℕ) (hi : i ≤ k) (f : Grass K V k → R) (U : Grass K V k) :
    distSum k i f U = interSum k (k - i) f U := by
  classical
  unfold distSum interSum
  congr 1
  ext W
  rw [mem_filter, mem_filter]
  have := finrank_inf_le_of_grass k U W
  unfold gDist
  simp only [mem_univ, true_and]
  omega

/-- Distances on `Gr(V, k)` are at most `d = min(k, n - k)`. -/
theorem gDist_le_min_sub (k : ℕ) (U W : Grass K V k) :
    gDist k U W ≤ min k (finrank K V - k) := by
  unfold gDist
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U.1 W.1
  have h2 := Submodule.finrank_le (U.1 ⊔ W.1)
  rw [U.2, W.2] at h1
  omega

open Classical in
/-- `D_i f = 0` for `i > d = min(k, n - k)`: the `d + 1` tables of `fast_distance_sums` are all
the distance sums. -/
theorem distSum_eq_zero_of_lt (k i : ℕ) (hi : min k (finrank K V - k) < i)
    (f : Grass K V k → R) (U : Grass K V k) : distSum k i f U = 0 := by
  unfold distSum
  refine sum_eq_zero fun W hW => ?_
  have := gDist_le_min_sub k U W
  rw [(mem_filter.1 hW).2] at this
  omega

end DistanceSums

/-- **All distance sums** (Appendix E): the `d + 1` tables `D_0 f, …, D_d f`, `d = min(k, n-k)`,
cost `O_q((d+1) N log N)`, `N = |Gr(n,k)|`: the input is fanned out (free) to `d + 1` fast
kernels (Theorem 1.4). -/
theorem fast_distance_sums (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
        LinCost (Set.univ : Set R)
          (fun (f : Grass K V k → R) (p : Fin (min k (finrank K V - k) + 1) × Grass K V k) =>
            distSum k p.1 f p.2)
          (C * (min k (finrank K V - k) + 1) * Fintype.card (Grass K V k) *
            (Nat.log 2 (Fintype.card (Grass K V k)) + 1)) := by
  obtain ⟨C, hC⟩ := fast_kernel.{u, v, w} K
  refine ⟨C, fun R _ hR V _ _ _ k => ?_⟩
  set d := min k (finrank K V - k)
  have h := LinCost.sigma (C := (Set.univ : Set R)) (ι := Fin (d + 1))
    (I' := fun _ => Grass K V k) (O' := fun _ => Grass K V k)
    (fun i => distSum (K := K) (V := V) (R := R) k i)
    (fun _ => C * Fintype.card (Grass K V k) * (Nat.log 2 (Fintype.card (Grass K V k)) + 1))
    (fun i => by rw [distSum_eq_kernelApply]; exact hC R hR V k _)
  have h' := h.reindex (I' := Grass K V k) (O' := Fin (d + 1) × Grass K V k) Sigma.snd
    (fun p => ⟨p.1, p.2⟩)
  refine (h'.congr rfl).mono (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-! ### Appendix E: distances to a code, rectangular kernels -/

section Codes

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Classical in
/-- Over `ℚ`, `D_i 1_𝒞` counts the codewords at distance `i`. -/
theorem distSum_indicator (k i : ℕ) (𝒞 : Finset (Grass K V k)) (U : Grass K V k) :
    distSum k i (fun W => if W ∈ 𝒞 then (1 : ℚ) else 0) U =
      (#(𝒞.filter fun W => gDist k U W = i) : ℚ) := by
  unfold distSum
  rw [sum_boole]
  congr 2
  ext W
  simp only [mem_filter, mem_univ, true_and]
  tauto

open Classical in
/-- `(D_i 1_𝒞)(U) > 0` iff some codeword is at distance `i` from `U`. -/
theorem distSum_indicator_pos_iff (k i : ℕ) (𝒞 : Finset (Grass K V k)) (U : Grass K V k) :
    0 < distSum k i (fun W => if W ∈ 𝒞 then (1 : ℚ) else 0) U ↔ ∃ W ∈ 𝒞, gDist k U W = i := by
  rw [distSum_indicator, Nat.cast_pos, card_pos, filter_nonempty_iff]

open Classical in
/-- **Distance to a code** (Appendix E): for a nonempty family `𝒞`, the least `i` with
`(D_i 1_𝒞)(U) > 0` is the distance from `U` to the nearest member of `𝒞`. -/
theorem isLeast_distSum_pos (k : ℕ) (𝒞 : Finset (Grass K V k)) (h𝒞 : 𝒞.Nonempty)
    (U : Grass K V k) :
    IsLeast {i | 0 < distSum k i (fun W => if W ∈ 𝒞 then (1 : ℚ) else 0) U}
      (𝒞.inf' h𝒞 (gDist k U)) := by
  constructor
  · show (0 : ℚ) < _
    rw [distSum_indicator_pos_iff]
    obtain ⟨W, hW, hmin⟩ := exists_mem_eq_inf' h𝒞 (gDist k U)
    exact ⟨W, hW, hmin.symm⟩
  · intro i hi
    have hi' : (0 : ℚ) < distSum k i (fun W => if W ∈ 𝒞 then (1 : ℚ) else 0) U := hi
    rw [distSum_indicator_pos_iff] at hi'
    obtain ⟨W, hW, rfl⟩ := hi'
    exact inf'_le _ hW

open Classical in
/-- The same as an equation: `min {i : (D_i 1_𝒞)(U) > 0} = min_{W ∈ 𝒞} dist(U, W)`. -/
theorem sInf_distSum_pos (k : ℕ) (𝒞 : Finset (Grass K V k)) (h𝒞 : 𝒞.Nonempty)
    (U : Grass K V k) :
    sInf {i | 0 < distSum k i (fun W => if W ∈ 𝒞 then (1 : ℚ) else 0) U} =
      𝒞.inf' h𝒞 (gDist k U) :=
  (isLeast_distSum_pos k 𝒞 h𝒞 U).csInf_eq

/-- On `Gr(V, k)`, `dist(U, W) = 0` exactly when `U = W`. -/
theorem gDist_eq_zero_iff_eq (k : ℕ) (U W : Grass K V k) : gDist k U W = 0 ↔ U = W := by
  constructor
  · intro h
    have h1 : finrank K (U.1 ⊓ W.1 : Submodule K V) = k := by
      have := finrank_inf_le_of_grass k U W
      unfold gDist at h
      omega
    have hU : U.1 ⊓ W.1 = U.1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (h1.trans U.2.symm)
    have hW : U.1 ⊓ W.1 = W.1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (h1.trans W.2.symm)
    exact Subtype.ext (hU.symm.trans hW)
  · rintro rfl
    unfold gDist
    rw [inf_idem, U.2, Nat.sub_self]

open Classical in
/-- **Minimum distance of a code** (Appendix E): for `|𝒞| ≥ 2`, the least `i > 0` with
`(D_i 1_𝒞)(U) > 0` for some `U ∈ 𝒞` is the minimum graph distance between distinct codewords
(the subspace distance is twice the graph distance). -/
theorem isLeast_minDist (k : ℕ) (𝒞 : Finset (Grass K V k)) (h𝒞 : 𝒞.offDiag.Nonempty) :
    IsLeast {i | 0 < i ∧ ∃ U ∈ 𝒞, 0 < distSum k i (fun W => if W ∈ 𝒞 then (1 : ℚ) else 0) U}
      (𝒞.offDiag.inf' h𝒞 fun p => gDist k p.1 p.2) := by
  constructor
  · obtain ⟨p, hp, hmin⟩ := exists_mem_eq_inf' h𝒞 fun p => gDist k p.1 p.2
    rw [mem_offDiag] at hp
    refine ⟨?_, p.1, hp.1, ?_⟩
    · rw [hmin]
      exact Nat.pos_of_ne_zero fun h0 => hp.2.2 ((gDist_eq_zero_iff_eq k _ _).1 h0)
    · rw [distSum_indicator_pos_iff]
      exact ⟨p.2, hp.2.1, hmin.symm⟩
  · rintro i ⟨hi, U, hU, hpos⟩
    rw [distSum_indicator_pos_iff] at hpos
    obtain ⟨W, hW, rfl⟩ := hpos
    have hUW : U ≠ W := fun h => by
      rw [h, (gDist_eq_zero_iff_eq k W W).2 rfl] at hi
      exact lt_irrefl 0 hi
    have hmem : (U, W) ∈ 𝒞.offDiag := mem_offDiag.2 ⟨hU, hW, hUW⟩
    exact inf'_le (fun p : Grass K V k × Grass K V k => gDist k p.1 p.2) hmem

variable {R : Type u} [CommRing R]

/-- Equation (rect-moments): `(I^{t,b} (I^{t,a})ᵀ f)(W) = ∑_U |Gr(dim(U ∩ W), t)| f(U)`.
(It holds for all `t`; the paper uses `t ≤ min(a, b)`.) -/
theorem rect_moments (t a b : ℕ) (f : Grass K V a → R) (W : Grass K V b) :
    incid t b (incidT t a f) W =
      ∑ U : Grass K V a, (gr K (finrank K (U.1 ⊓ W.1 : Submodule K V)) t : R) * f U := by
  unfold incid incidT
  rw [sum_grass_le_sum_ge W.1 f]
  refine sum_congr rfl fun U _ => ?_
  rw [inf_comm]

end Codes

end SubspaceConvolution
