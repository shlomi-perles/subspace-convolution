/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Spectral

/-!
# Costs of the Grassmannian applications (Appendix E)

`N = |Gr(n, k)|`, `d = min(k, n - k)`.

* `linCost_powers` — `f, A f, …, A^m f` with `m` applications of a linear map `A`.
* `specProj_apply_eq` — `P_j f = ∑_{i ≤ d} c_{j,i} D₁^i f`, `c_{j,i}` the coefficients of the
  Lagrange basis polynomial.
* `specComponents_linCost` — **spectral projections**: over `ℚ`, all components
  `f_j = P_j(D₁) f`, `0 ≤ j ≤ d`, in `O_q((d+1) N log N)` operations: `d` fast kernel
  multiplications (`fast_kernel`) give `D₁^i f`, then `(d+1)² N` gates combine them, and
  `(d+1)² N ≤ (d+1) N (log₂ N + 1)` since `2^d ≤ N`.
* `smallSystem_linCost` — **invariant linear systems**: the small matrix `B` of
  equation (small-system) is read off from `d + 1` kernel multiplications (of the indicators
  `b_j`); `kernelInverse_linCost` — once `B c = e₀` is solved (a `(d+1) × (d+1)` system), the
  inverse `K⁻¹ = C`, `C(U,W) = c_{dist(U,W)}`, is applied with `O_q(N log N)` operations over every
  field in which `p` is invertible.
-/

open Finset Module Polynomial Matrix

set_option linter.unusedSectionVars false

universe u v w

namespace SubspaceConvolution

open Circuit

/-! ### Powers of a linear map -/

section Powers

variable {R : Type u} [CommRing R] {I : Type*}

/-- `f, A f, …, A^m f` cost `m` applications of `A`. -/
theorem linCost_powers {C : Set R} {A : Module.End R (I → R)} {c : ℕ}
    (hA : LinCost C (fun f => A f) c) (m : ℕ) :
    LinCost C (fun (f : I → R) (p : Fin (m + 1) × I) => (A ^ (p.1 : ℕ)) f p.2) (m * c) := by
  induction m with
  | zero =>
    refine ((LinCost.id (C := C) (I := I)).reindex (fun i => i) (fun p : Fin 1 × I => p.2)).congr
      ?_ |>.mono (by simp)
    funext f p
    rw [Fin.val_eq_zero p.1, pow_zero, one_apply_eq_self]
  | succ m ih =>
    have h₂ : LinCost C (fun (g : Fin (m + 1) × I → R) (x : I) => A (fun y => g (Fin.last m, y)) x)
        c := hA.reindex (fun y => (Fin.last m, y)) (fun x => x)
    have hS := ((LinCost.id (C := C) (I := Fin (m + 1) × I)).sumElim h₂).reindex (fun p => p)
      (fun p : Fin (m + 2) × I =>
        if h : (p.1 : ℕ) < m + 1 then Sum.inl (⟨p.1, h⟩, p.2) else Sum.inr p.2)
    refine ((ih.comp hS).congr ?_).mono (by rw [zero_add, Nat.succ_mul])
    funext f p
    by_cases h : (p.1 : ℕ) < m + 1
    · simp only [dite_eq_left h, Sum.elim_inl]
    · have hp : (p.1 : ℕ) = m + 1 := by omega
      simp only [dite_eq_right h, Sum.elim_inr, Fin.val_last]
      rw [hp, pow_succ', mul_apply_eq_comp]

end Powers

/-! ### Spectral projections -/

section Spectral

variable {K : Type w} [Field K] [Fintype K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : Type u} [Field F] [CharZero F]

/-- `P_j f = ∑_{i ≤ d} c_{j,i} D₁^i f`. -/
theorem specProj_apply_eq (k j : ℕ) (hj : j ≤ gdiam K V k) (f : Grass K V k → F)
    (U : Grass K V k) :
    specProj K V F k j f U = ∑ i : Fin (gdiam K V k + 1),
      (Lagrange.basis (range (gdiam K V k + 1)) (eigval K V F k) j).coeff i *
        ((adjEnd K V F k ^ (i : ℕ)) f) U := by
  have hdeg : (Lagrange.basis (range (gdiam K V k + 1)) (eigval K V F k) j).natDegree <
      gdiam K V k + 1 := by
    rw [Lagrange.natDegree_basis (eigval_injOn k) (by simpa using Nat.lt_succ_of_le hj),
      card_range]
    omega
  unfold specProj
  rw [aeval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range, LinearMap.sum_apply,
    Finset.sum_apply]
  rfl

/-- `2^d ≤ N`, hence `d ≤ log₂ N`. -/
theorem gdiam_le_log (k : ℕ) (hk : k ≤ finrank K V) :
    gdiam K V k ≤ Nat.log 2 (Fintype.card (Grass K V k)) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  rw [card_grass rfl]
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have h1 := pow_le_gr K hk
  have h2 : gdiam K V k ≤ k * (finrank K V - k) := by
    unfold gdiam
    rcases Nat.eq_zero_or_pos (finrank K V - k) with h | h
    · rw [h]; simp
    · exact (min_le_left _ _).trans (Nat.le_mul_of_pos_right k h)
  calc 2 ^ gdiam K V k ≤ 2 ^ (k * (finrank K V - k)) := Nat.pow_le_pow_right (by norm_num) h2
    _ ≤ Fintype.card K ^ (k * (finrank K V - k)) := Nat.pow_le_pow_left hq _
    _ ≤ gr K (finrank K V) k := h1

theorem isUnit_ringChar_rat (K : Type w) [Field K] [Fintype K] : IsUnit (ringChar K : ℚ) :=
  isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (CharP.ringChar_ne_zero_of_finite K))

/-- **Spectral projections** (Appendix E): over `ℚ`, all components `f_j = P_j(D₁) f`,
`0 ≤ j ≤ d`, take `O_q((d+1) N log N)` operations. -/
theorem specComponents_linCost (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
      LinCost (Set.univ : Set ℚ)
        (fun (f : Grass K V k → ℚ) (p : Fin (gdiam K V k + 1) × Grass K V k) =>
          specProj K V ℚ k p.1 f p.2)
        (C * (gdiam K V k + 1) * Fintype.card (Grass K V k) *
          (Nat.log 2 (Fintype.card (Grass K V k)) + 1)) := by
  obtain ⟨C₀, hC₀⟩ := fast_kernel.{0, v, w} K
  refine ⟨C₀ + 1, fun V _ _ _ k => ?_⟩
  by_cases hkn : k ≤ finrank K V
  · set N := Fintype.card (Grass K V k) with hN
    set d := gdiam K V k with hd
    set L := Nat.log 2 N with hL
    have hdL : d ≤ L := gdiam_le_log k hkn
    -- `D₁^i f`, `i ≤ d`
    have hA : LinCost (Set.univ : Set ℚ) (fun f => adjEnd K V ℚ k f) (C₀ * N * (L + 1)) :=
      hC₀ ℚ (isUnit_ringChar_rat K) V k adjCoeff
    have hP := linCost_powers hA d
    -- combine with the coefficients of the Lagrange basis polynomials
    set coef : Fin (d + 1) → Fin (d + 1) → ℚ := fun j i =>
      (Lagrange.basis (range (d + 1)) (eigval K V ℚ k) j).coeff i with hcoef
    have hblock : ∀ _U : Grass K V k, LinCost (Set.univ : Set ℚ)
        (fun (g : Fin (d + 1) → ℚ) (j : Fin (d + 1)) => ∑ i, coef j i * g i) ((d + 1) * (d + 1)) := by
      intro _
      have := LinCost.dense (C := (Set.univ : Set ℚ)) coef (fun _ _ => trivial) trivial trivial
      simpa only [Fintype.card_fin] using this
    have hS := LinCost.sigma (C := (Set.univ : Set ℚ)) (ι := Grass K V k)
      (I' := fun _ => Fin (d + 1)) (O' := fun _ => Fin (d + 1))
      (fun _ g j => ∑ i, coef j i * g i) (fun _ => (d + 1) * (d + 1)) hblock
    have hG := hS.reindex (fun p : (Σ _ : Grass K V k, Fin (d + 1)) => (p.2, p.1))
      (fun p : Fin (d + 1) × Grass K V k => (⟨p.2, p.1⟩ : Σ _ : Grass K V k, Fin (d + 1)))
    refine ((hP.comp hG).congr ?_).mono ?_
    · funext f p
      rw [specProj_apply_eq k p.1 (Nat.lt_succ_iff.1 p.1.2) f p.2]
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hN]
      have h1 : N * ((d + 1) * (d + 1)) ≤ (d + 1) * N * (L + 1) := by
        calc N * ((d + 1) * (d + 1)) = (d + 1) * N * (d + 1) := by ring
          _ ≤ (d + 1) * N * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      have h2 : d * (C₀ * N * (L + 1)) ≤ C₀ * (d + 1) * N * (L + 1) := by
        calc d * (C₀ * N * (L + 1)) ≤ (d + 1) * (C₀ * N * (L + 1)) :=
              Nat.mul_le_mul_right _ (Nat.le_succ d)
          _ = C₀ * (d + 1) * N * (L + 1) := by ring
      calc d * (C₀ * N * (L + 1)) + N * ((d + 1) * (d + 1))
          ≤ C₀ * (d + 1) * N * (L + 1) + (d + 1) * N * (L + 1) := Nat.add_le_add h2 h1
        _ = (C₀ + 1) * (d + 1) * N * (L + 1) := by ring
  · have : IsEmpty (Grass K V k) := ⟨fun U => hkn (le_finrank_of_grass U)⟩
    exact LinCost.empty _ _

end Spectral

/-! ### Invariant linear systems -/

section Invariant

/-- **The small system** (equation (small-system)) comes from `d + 1` kernel multiplications:
the columns `K b_j` evaluated at the representatives `U_i`. -/
theorem smallSystem_linCost (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (F : Type u) [Field F], IsUnit (ringChar K : F) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ) (a : ℕ → F)
        (E : Grass K V k),
        LinCost (Set.univ : Set F)
          (fun (x : Fin (gdiam K V k + 1) × Grass K V k → F)
            (p : Fin (gdiam K V k + 1) × Fin (gdiam K V k + 1)) =>
              kernelApply k a (fun W => x (p.2, W)) (orbitRep E p.1))
          ((gdiam K V k + 1) *
            (C * Fintype.card (Grass K V k) * (Nat.log 2 (Fintype.card (Grass K V k)) + 1))) ∧
        ∀ i j, smallSystem k a E i j =
          kernelApply k a (fun W => (fun p : Fin (gdiam K V k + 1) × Grass K V k =>
            orbitInd (F := F) k E p.1 p.2) (j, W)) (orbitRep E i) := by
  obtain ⟨C₀, hC₀⟩ := fast_kernel.{u, v, w} K
  refine ⟨C₀, fun F _ hF V _ _ _ k a E => ⟨?_, fun i j => rfl⟩⟩
  have hK := hC₀ F hF V k a
  have hS := LinCost.sigma (C := (Set.univ : Set F)) (ι := Fin (gdiam K V k + 1))
    (I' := fun _ => Grass K V k) (O' := fun _ => Grass K V k)
    (fun _ g U => kernelApply k a g U) _ (fun _ => hK)
  have h := hS.reindex (fun p : (Σ _ : Fin (gdiam K V k + 1), Grass K V k) => (p.1, p.2))
    (fun p : Fin (gdiam K V k + 1) × Fin (gdiam K V k + 1) =>
      (⟨p.2, orbitRep E p.1⟩ : Σ _ : Fin (gdiam K V k + 1), Grass K V k))
  refine h.mono (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Invariant linear systems**: once `B c = (1, 0, …, 0)ᵀ` is solved, `K⁻¹ = C` with
`C(U, W) = c_{dist(U, W)}`, and applying it takes `O_q(N log N)` operations over every field in
which `p` is invertible. -/
theorem kernelInverse_linCost (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (F : Type u) [Field F], IsUnit (ringChar K : F) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ) (a : ℕ → F)
        (E : Grass K V k) (c : Fin (gdiam K V k + 1) → F),
        smallSystem k a E *ᵥ c = Pi.single 0 1 →
          (∀ f : Grass K V k → F, kernelApply k a (kernelApply k (extCoeff c) f) = f) ∧
          (∀ f : Grass K V k → F, kernelApply k (extCoeff c) (kernelApply k a f) = f) ∧
          LinCost (Set.univ : Set F) (kernelApply (K := K) (V := V) k (extCoeff c))
            (C * Fintype.card (Grass K V k) * (Nat.log 2 (Fintype.card (Grass K V k)) + 1)) := by
  obtain ⟨C₀, hC₀⟩ := fast_kernel.{u, v, w} K
  refine ⟨C₀, fun F _ hF V _ _ _ k a E c hc => ?_⟩
  obtain ⟨h1, h2⟩ := kernelApply_inverse a E c hc
  exact ⟨h1, h2, hC₀ F hF V k (extCoeff c)⟩

end Invariant

end SubspaceConvolution
