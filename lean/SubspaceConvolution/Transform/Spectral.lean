/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.GrAux
import SubspaceConvolution.Transform.Invariant
import SubspaceConvolution.Transform.Kernel

/-!
# Spectral projections of the Grassmann graph (Appendix C)

Let `D₁` be the adjacency matrix of `J_q(n, k)` (`adjEnd`: the intersection kernel with
`a_j = [j = 1]`; `adjEnd_apply_eq_sum_adj`), `d = min(k, n - k)` and
`θ_j = q [k] [n-k] - [j] [n-j+1]` (`eigZ`, `eigval`), `[m] = 1 + q + ⋯ + q^{m-1}`.

* `eigZ_sub_succ` — `θ_j - θ_{j+1} = q^j [n - 2j]`, so the `θ_j`, `j ≤ d`, are distinct
  (`eigval_injOn`).
* `adjEnd_incid_succ`, `adjEnd_incid_zero` — with `I_j = incid j k` (sum over the
  `j`-dimensional subspaces of `U`):
  `D₁ I_j = θ_j I_j + [k-j+1] I_{j-1} (I^{j-1,j})ᵀ`, `D₁ I_0 = θ_0 I_0` (double counting with
  `card_adj` and `card_common_sub`).
* `aeval_adjEnd_eq_zero` — **the key identity** `∏_{j ≤ d} (D₁ - θ_j) = 0`: `(D₁ - θ_j)` maps
  `range I_j` into `range I_{j-1}` and `I_k = id`; for `2k > n` transfer through annihilators
  (`kernelApply_dual`).
* `specProj` — the spectral projections `P_j = L_j(D₁)` (Lagrange basis polynomials);
  `sum_specProj` (`∑ P_j = 1`), `adjEnd_mul_specProj` (`D₁ P_j = θ_j P_j`),
  `specProj_mul_specProj` (`P_i P_j = [i = j] P_j`); `specProj_decomp` (`f = ∑ P_j f` with
  `D₁ P_j f = θ_j P_j f`) and `specProj_eq_of_eigen` (any such decomposition is this one).
-/

open Finset Module Polynomial

set_option linter.unusedSectionVars false

universe u v w

namespace SubspaceConvolution

/-! ### The eigenvalues -/

/-- `θ_j = q [k] [n-k] - [j] [n-j+1]`, as an integer. -/
def eigZ (q n k j : ℕ) : ℤ := q * qnum q k * qnum q (n - k) - qnum q j * qnum q (n - j + 1)

/-- `θ_j - θ_{j+1} = q^j [n - 2j]`. -/
theorem eigZ_sub_succ (q n k j : ℕ) (h : 2 * j < n) :
    eigZ q n k j - eigZ q n k (j + 1) = q ^ j * qnum q (n - 2 * j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
  unfold eigZ
  rw [show 2 * j + m + 1 - j + 1 = (m + 1 + j) + 1 by omega,
    show 2 * j + m + 1 - (j + 1) + 1 = m + 1 + j by omega,
    show 2 * j + m + 1 - 2 * j = m + 1 by omega]
  rw [qnum_succ q (m + 1 + j), qnum_add q (m + 1) j, qnum_succ q j]
  push_cast
  ring

theorem eigZ_succ_lt {q n k j : ℕ} (hq : 1 ≤ q) (h : 2 * (j + 1) ≤ n) :
    eigZ q n k (j + 1) < eigZ q n k j := by
  have h1 := eigZ_sub_succ q n k j (by omega)
  have h2 : 1 ≤ qnum q (n - 2 * j) := one_le_qnum (by omega)
  have h3 : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq
  have h4 : (1 : ℤ) ≤ (q : ℤ) ^ j * qnum q (n - 2 * j) := by
    have : (1 : ℕ) ≤ q ^ j * qnum q (n - 2 * j) := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  omega

/-- The eigenvalues `θ_0 > θ_1 > ⋯ > θ_d` are strictly decreasing. -/
theorem eigZ_lt_of_lt {q n k i j : ℕ} (hq : 1 ≤ q) (hij : i < j) (hj : 2 * j ≤ n) :
    eigZ q n k j < eigZ q n k i := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (eigZ_succ_lt hq hj).trans (ih h (by omega))
    · exact eigZ_succ_lt hq hj

/-- `θ` is symmetric under `k ↦ n - k`. -/
theorem eigZ_symm {q n k : ℕ} (hk : k ≤ n) (j : ℕ) : eigZ q n (n - k) j = eigZ q n k j := by
  unfold eigZ
  rw [Nat.sub_sub_self hk]
  ring

/-- The identity closing the double count: `[k-j-1] q [n-k] = θ_{j+1} + [k-j] [j+1]`. -/
theorem eigZ_identity (q n k j : ℕ) (hjk : j + 1 ≤ k) (hkn : k ≤ n) :
    ((qnum q (k - (j + 1)) : ℤ) * (q * qnum q (n - k))) =
      eigZ q n k (j + 1) + qnum q (k - j) * qnum q (j + 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hjk
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hkn
  unfold eigZ
  rw [show j + 1 + a - (j + 1) = a by omega, show j + 1 + a + b - (j + 1 + a) = b by omega,
    show j + 1 + a + b - (j + 1) + 1 = (a + 1) + b by omega,
    show j + 1 + a - j = a + 1 by omega, show j + 1 + a = a + (j + 1) by omega]
  rw [qnum_add q (a + 1) b, qnum_add q a (j + 1)]
  push_cast
  ring

theorem eigZ_zero (q n k : ℕ) : eigZ q n k 0 = q * qnum q k * qnum q (n - k) := by
  simp [eigZ]

/-! ### The adjacency matrix and the incidence maps `I_j` -/

section Operator

variable {K : Type w} [Field K] [Fintype K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : Type u} [Field F]

/-- The coefficients `a_j = [j = 1]` of the adjacency matrix `D₁`. -/
def adjCoeff : ℕ → F := fun j => if j = 1 then 1 else 0

variable (K V F) in
/-- The adjacency matrix `D₁` of `J_q(n, k)`, as a linear endomorphism. -/
noncomputable def adjEnd (k : ℕ) : Module.End F (Grass K V k → F) := kernelLin K V k adjCoeff

theorem adjEnd_apply (k : ℕ) (f : Grass K V k → F) :
    adjEnd K V F k f = kernelApply k adjCoeff f := rfl

open Classical in
/-- `D₁` sums the weights of the neighbours: it is the adjacency matrix of `J_q(n, k)`. -/
theorem adjEnd_apply_eq_sum_adj (k : ℕ) (f : Grass K V k → F) (U : Grass K V k) :
    adjEnd K V F k f U = ∑ W ∈ univ.filter fun W => (grassGraph k).Adj U W, f W := by
  rw [adjEnd_apply, kernelApply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases h : (grassGraph k).Adj U W
  · rw [ite_eq_left h, adjCoeff, ite_eq_left (gDist_eq_one_iff.2 h), one_mul]
  · rw [ite_eq_right h, adjCoeff, ite_eq_right (fun h' => h (gDist_eq_one_iff.1 h')), zero_mul]

variable (K V F) in
/-- The eigenvalue `θ_j` in `F`. -/
noncomputable def eigval (k j : ℕ) : F := (eigZ (Fintype.card K) (finrank K V) k j : F)

open Classical in
theorem kernelApply_adj_incid (k j : ℕ) (g : Grass K V j → F) (U : Grass K V k) :
    kernelApply k adjCoeff (incid j k g) U =
      ∑ L, g L * (#(univ.filter fun W : Grass K V k =>
        (grassGraph k).Adj U W ∧ L.1 ≤ W.1) : F) := by
  simp only [kernelApply, incid, adjCoeff, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun L _ => ?_
  have h : ∀ W : Grass K V k,
      (if gDist k U W = 1 then (1 : F) else 0) * (if L.1 ≤ W.1 then g L else 0) =
        g L * (if (grassGraph k).Adj U W ∧ L.1 ≤ W.1 then 1 else 0) := by
    intro W
    by_cases h1 : L.1 ≤ W.1 <;> by_cases h2 : (grassGraph k).Adj U W <;>
      simp [h1, h2, gDist_eq_one_iff]
  rw [Finset.sum_congr rfl fun W _ => h W, ← Finset.mul_sum, Finset.sum_boole]

open Classical in
theorem incid_apply_eq (j k : ℕ) (g : Grass K V j → F) (U : Grass K V k) :
    incid j k g U = ∑ L, g L * (if L.1 ≤ U.1 then 1 else 0) := by
  simp only [incid, Finset.sum_filter, mul_ite, mul_one, mul_zero]

open Classical in
theorem incid_incidT_apply (j k : ℕ) (g : Grass K V (j + 1) → F) (U : Grass K V k) :
    incid j k (incidT j (j + 1) g) U =
      ∑ L, g L * (#(univ.filter fun M : Grass K V j => M.1 ≤ U.1 ∧ M.1 ≤ L.1) : F) := by
  simp only [incid, incidT, Finset.sum_filter]
  have h : ∀ M : Grass K V j,
      (if M.1 ≤ U.1 then ∑ L : Grass K V (j + 1), (if M.1 ≤ L.1 then g L else 0) else 0) =
        ∑ L : Grass K V (j + 1), g L * (if M.1 ≤ U.1 ∧ M.1 ≤ L.1 then 1 else 0) := by
    intro M
    by_cases hM : M.1 ≤ U.1
    · simp only [hM, true_and, ite_true, mul_ite, mul_one, mul_zero]
    · simp only [hM, false_and, ite_false, mul_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun M _ => h M, Finset.sum_comm]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole]

open Classical in
theorem incid_diag (k : ℕ) (f : Grass K V k → F) : incid k k f = f := by
  funext U
  unfold incid
  rw [Finset.sum_filter, Finset.sum_eq_single U]
  · exact ite_eq_left le_rfl
  · intro W _ hne
    exact ite_eq_right fun h => hne (grass_eq_of_le h)
  · intro h
    exact absurd (mem_univ U) h

open Classical in
/-- The coefficient identity behind `D₁ I_{j+1}`. -/
theorem card_adj_coeff {k j : ℕ} (hjk : j + 1 ≤ k) (U : Grass K V k) (L : Grass K V (j + 1)) :
    (#(univ.filter fun W : Grass K V k => (grassGraph k).Adj U W ∧ L.1 ≤ W.1) : F) =
      eigval K V F k (j + 1) * (if L.1 ≤ U.1 then 1 else 0) +
        (qnum (Fintype.card K) (k - j) : F) *
          (#(univ.filter fun M : Grass K V j => M.1 ≤ U.1 ∧ M.1 ≤ L.1) : F) := by
  have hkn : k ≤ finrank K V := le_finrank_of_grass U
  have hL := finrank_grass L
  have htj : finrank K ↥(U.1 ⊓ L.1) ≤ j + 1 :=
    (Submodule.finrank_mono (inf_le_right : U.1 ⊓ L.1 ≤ L.1)).trans hL.le
  have hgr : gr K (j + 1) j = qnum (Fintype.card K) (j + 1) := by
    have := gr_pred_eq_qnum K (show 1 ≤ j + 1 by omega)
    simpa using this
  rw [card_adj U L hjk, card_common_sub U L]
  by_cases hLU : L.1 ≤ U.1
  · have ht : finrank K ↥(U.1 ⊓ L.1) = j + 1 := by rw [inf_eq_right.2 hLU, hL]
    rw [ite_eq_left hLU, ite_eq_right (show ¬ (finrank K ↥(U.1 ⊓ L.1) + 1 = j + 1) by omega),
      ite_eq_left hLU, add_zero, mul_one, ht, hgr]
    unfold eigval
    have h := congrArg (fun z : ℤ => (z : F))
      (eigZ_identity (Fintype.card K) (finrank K V) k j hjk hkn)
    push_cast at h ⊢
    linear_combination h
  · rw [ite_eq_right hLU, ite_eq_right hLU, zero_add, mul_zero, zero_add]
    by_cases ht : finrank K ↥(U.1 ⊓ L.1) = j
    · rw [ite_eq_left (show finrank K ↥(U.1 ⊓ L.1) + 1 = j + 1 by omega), ht, gr_self,
        show k + 1 - (j + 1) = k - j by omega]
      simp
    · have hlt : finrank K ↥(U.1 ⊓ L.1) < j := by
        have : finrank K ↥(U.1 ⊓ L.1) ≠ j + 1 := fun h =>
          hLU (inf_eq_right.1 (Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h, hL])))
        omega
      rw [ite_eq_right (show ¬ (finrank K ↥(U.1 ⊓ L.1) + 1 = j + 1) by omega),
        gr_eq_zero_of_lt K hlt]
      simp

/-- `D₁ I_{j+1} = θ_{j+1} I_{j+1} + [k-j] I_j (I^{j,j+1})ᵀ`. -/
theorem adjEnd_incid_succ {k j : ℕ} (hjk : j + 1 ≤ k) (g : Grass K V (j + 1) → F) :
    adjEnd K V F k (incid (j + 1) k g) =
      eigval K V F k (j + 1) • incid (j + 1) k g +
        (qnum (Fintype.card K) (k - j) : F) • incid j k (incidT j (j + 1) g) := by
  funext U
  rw [adjEnd_apply, kernelApply_adj_incid, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, incid_apply_eq, incid_incidT_apply, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [card_adj_coeff hjk U L]
  ring

/-- `D₁ I_0 = θ_0 I_0` (`θ_0` is the degree). -/
theorem adjEnd_incid_zero (k : ℕ) (g : Grass K V 0 → F) :
    adjEnd K V F k (incid 0 k g) = eigval K V F k 0 • incid 0 k g := by
  classical
  funext U
  rw [adjEnd_apply, kernelApply_adj_incid, Pi.smul_apply, smul_eq_mul, incid_apply_eq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  have hL0 : L.1 = ⊥ := Submodule.finrank_eq_zero.1 (finrank_grass L)
  have hLU : L.1 ≤ U.1 := by rw [hL0]; exact bot_le
  rw [card_adj U L (Nat.zero_le k), ite_eq_left hLU,
    ite_eq_right (show ¬ (finrank K ↥(U.1 ⊓ L.1) + 1 = 0) by omega), add_zero, ite_eq_left hLU]
  unfold eigval
  rw [eigZ_zero]
  push_cast
  rw [Nat.sub_zero]
  ring

/-- The induction: `∏_{j ≤ m} (D₁ - θ_j)` kills the range of `I_m`. -/
theorem aeval_prod_incid (k : ℕ) :
    ∀ m ≤ k, ∀ g : Grass K V m → F,
      aeval (adjEnd K V F k) (∏ j ∈ range (m + 1), (X - C (eigval K V F k j)))
        (incid m k g) = 0 := by
  intro m
  induction m with
  | zero =>
    intro _ g
    rw [zero_add, Finset.prod_range_one, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply, adjEnd_incid_zero, sub_self]
  | succ m ih =>
    intro hm g
    rw [Finset.prod_range_succ, map_mul, mul_apply_eq_comp, map_sub, aeval_X, aeval_C,
      LinearMap.sub_apply, Module.algebraMap_end_apply, adjEnd_incid_succ (by omega),
      add_sub_cancel_left, map_smul, ih (by omega), smul_zero]

/-- The key identity for `2k ≤ n` (more generally `∏_{j ≤ k} (D₁ - θ_j) = 0` for every `k`). -/
theorem aeval_adjEnd_prod_self (k : ℕ) :
    aeval (adjEnd K V F k) (∏ j ∈ range (k + 1), (X - C (eigval K V F k j))) = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply, ← incid_diag k f]
  exact aeval_prod_incid k k le_rfl f

/-- Annihilators: `D₁` on `Gr(V, k)` is conjugate to `D₁` on `Gr(V*, n - k)`. -/
theorem adjEnd_eq_conj (k : ℕ) (hk : k ≤ finrank K V) :
    adjEnd K V F k =
      (LinearEquiv.funCongrLeft F F (grassDualEquiv k hk)).conjAlgEquiv F
        (adjEnd K (Module.Dual K V) F (finrank K V - k)) := by
  refine LinearMap.ext fun f => ?_
  funext U
  rw [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, LinearEquiv.funCongrLeft_symm,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, adjEnd_apply, adjEnd_apply,
    kernelApply_dual k hk]
  rfl

/-- **The key identity**: `∏_{j ≤ d} (D₁ - θ_j) = 0`, `d = min(k, n - k)`. -/
theorem aeval_adjEnd_eq_zero (k : ℕ) :
    aeval (adjEnd K V F k) (∏ j ∈ range (gdiam K V k + 1), (X - C (eigval K V F k j))) = 0 := by
  by_cases hkn : k ≤ finrank K V
  · by_cases h2k : 2 * k ≤ finrank K V
    · have hd : gdiam K V k = k := by unfold gdiam; omega
      rw [hd]
      exact aeval_adjEnd_prod_self k
    · have hn : finrank K (Module.Dual K V) = finrank K V := Subspace.dual_finrank_eq
      have hd : gdiam K V k = finrank K V - k := by unfold gdiam; omega
      have hhalf := aeval_adjEnd_prod_self (K := K) (V := Module.Dual K V) (F := F)
        (finrank K V - k)
      have heig : ∀ j, eigval K (Module.Dual K V) F (finrank K V - k) j = eigval K V F k j := by
        intro j
        unfold eigval
        rw [hn, eigZ_symm hkn]
      simp_rw [heig] at hhalf
      rw [hd, adjEnd_eq_conj k hkn, Polynomial.aeval_algHom_apply, hhalf, map_zero]
  · have : IsEmpty (Grass K V k) := ⟨fun U => hkn (le_finrank_of_grass U)⟩
    refine LinearMap.ext fun f => ?_
    funext U
    exact isEmptyElim U

end Operator

/-! ### Spectral projections -/

section Projections

variable {K : Type w} [Field K] [Fintype K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : Type u} [Field F] [CharZero F]

/-- The `θ_j`, `j ≤ d`, are distinct. -/
theorem eigval_injOn (k : ℕ) :
    Set.InjOn (eigval K V F k) (range (gdiam K V k + 1) : Finset ℕ) := by
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  have hij' : eigZ (Fintype.card K) (finrank K V) k i = eigZ (Fintype.card K) (finrank K V) k j :=
    Int.cast_injective hij
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have h2i : 2 * i ≤ finrank K V := by unfold gdiam at hi; omega
  have h2j : 2 * j ≤ finrank K V := by unfold gdiam at hj; omega
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact (eigZ_lt_of_lt hq h h2j).ne hij'.symm
  · exact (eigZ_lt_of_lt hq h h2i).ne hij'

variable (K V F) in
/-- The spectral projection `P_j = L_j(D₁)`, `L_j` the Lagrange basis polynomial at the nodes
`θ_0, …, θ_d`. -/
noncomputable def specProj (k j : ℕ) : Module.End F (Grass K V k → F) :=
  aeval (adjEnd K V F k) (Lagrange.basis (range (gdiam K V k + 1)) (eigval K V F k) j)

theorem aeval_nodal (k : ℕ) :
    aeval (adjEnd K V F k) (Lagrange.nodal (range (gdiam K V k + 1)) (eigval K V F k)) = 0 :=
  aeval_adjEnd_eq_zero k

theorem aeval_X_sub_C_mul_basis (k : ℕ) {j : ℕ} (hj : j ∈ range (gdiam K V k + 1)) :
    aeval (adjEnd K V F k) ((X - C (eigval K V F k j)) *
      Lagrange.basis (range (gdiam K V k + 1)) (eigval K V F k) j) = 0 := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hj, ← Lagrange.nodal_erase_eq_nodal_div hj,
    mul_left_comm, ← Lagrange.nodal_eq_mul_nodal_erase hj, map_mul, aeval_nodal, mul_zero]

/-- `∑_j P_j = 1`. -/
theorem sum_specProj (k : ℕ) : ∑ j ∈ range (gdiam K V k + 1), specProj K V F k j = 1 := by
  unfold specProj
  rw [← map_sum, Lagrange.sum_basis (eigval_injOn k) ⟨0, by simp⟩, map_one]

/-- `p(D₁) P_j = p(θ_j) P_j`. -/
theorem aeval_mul_specProj (k : ℕ) {j : ℕ} (hj : j ∈ range (gdiam K V k + 1)) (p : F[X]) :
    aeval (adjEnd K V F k) p * specProj K V F k j =
      p.eval (eigval K V F k j) • specProj K V F k j := by
  obtain ⟨r, hr⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := eigval K V F k j) (p := p)
  set c := p.eval (eigval K V F k j) with hc
  have hp : p = r * (X - C (eigval K V F k j)) + C c := by
    rw [mul_comm, ← hr]; ring
  unfold specProj
  rw [← map_mul, hp, add_mul, mul_assoc, map_add, map_mul, aeval_X_sub_C_mul_basis k hj,
    mul_zero, zero_add, map_mul, aeval_C, Algebra.smul_def]

/-- `D₁ P_j = θ_j P_j`. -/
theorem adjEnd_mul_specProj (k : ℕ) {j : ℕ} (hj : j ≤ gdiam K V k) :
    adjEnd K V F k * specProj K V F k j = eigval K V F k j • specProj K V F k j := by
  have := aeval_mul_specProj (K := K) (V := V) (F := F) k
    (by simpa using Nat.lt_succ_of_le hj) X
  rwa [aeval_X, eval_X] at this

/-- `P_i P_j = [i = j] P_j`. -/
theorem specProj_mul_specProj (k : ℕ) {i j : ℕ} (hi : i ≤ gdiam K V k) (hj : j ≤ gdiam K V k) :
    specProj K V F k i * specProj K V F k j = if i = j then specProj K V F k j else 0 := by
  have hi' : i ∈ range (gdiam K V k + 1) := by simpa using Nat.lt_succ_of_le hi
  have hj' : j ∈ range (gdiam K V k + 1) := by simpa using Nat.lt_succ_of_le hj
  conv_lhs => rw [specProj]
  rw [aeval_mul_specProj k hj']
  by_cases h : i = j
  · subst h
    rw [Lagrange.eval_basis_self (eigval_injOn k) hi', one_smul, ite_eq_left rfl]
  · rw [Lagrange.eval_basis_of_ne h hj', zero_smul, ite_eq_right h]

/-- If `D₁ g = θ g`, then `p(D₁) g = p(θ) g`. -/
theorem aeval_adjEnd_apply_of_eigen (k : ℕ) {θ : F} {g : Grass K V k → F}
    (h : adjEnd K V F k g = θ • g) (p : F[X]) : aeval (adjEnd K V F k) p g = p.eval θ • g := by
  by_cases hg : g = 0
  · rw [hg, map_zero, smul_zero]
  · exact Module.End.aeval_apply_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 h, hg⟩)

/-- **The components are the eigenspace components**: if `f = ∑_{j ≤ d} g_j` with
`D₁ g_j = θ_j g_j`, then `P_i f = g_i`. -/
theorem specProj_eq_of_eigen (k : ℕ) (f : Grass K V k → F) (g : ℕ → Grass K V k → F)
    (hg : ∀ j ≤ gdiam K V k, adjEnd K V F k (g j) = eigval K V F k j • g j)
    (hf : f = ∑ j ∈ range (gdiam K V k + 1), g j) {i : ℕ} (hi : i ≤ gdiam K V k) :
    specProj K V F k i f = g i := by
  have hi' : i ∈ range (gdiam K V k + 1) := by simpa using Nat.lt_succ_of_le hi
  rw [hf, map_sum, Finset.sum_eq_single i]
  · rw [specProj, aeval_adjEnd_apply_of_eigen k (hg i hi),
      Lagrange.eval_basis_self (eigval_injOn k) hi', one_smul]
  · intro j hj hji
    have hj' : j ≤ gdiam K V k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [specProj, aeval_adjEnd_apply_of_eigen k (hg j hj'),
      Lagrange.eval_basis_of_ne (Ne.symm hji) hj, zero_smul]
  · intro h; exact absurd hi' h

/-- Every `f` is the sum of its components, and each component is an eigenvector:
`f = ∑_j P_j f` and `D₁ (P_j f) = θ_j P_j f`. -/
theorem specProj_decomp (k : ℕ) (f : Grass K V k → F) :
    f = ∑ j ∈ range (gdiam K V k + 1), specProj K V F k j f ∧
      ∀ j ≤ gdiam K V k,
        adjEnd K V F k (specProj K V F k j f) = eigval K V F k j • specProj K V F k j f := by
  refine ⟨?_, fun j hj => ?_⟩
  · have := congrArg (fun T : Module.End F (Grass K V k → F) => T f) (sum_specProj k)
    simp only [LinearMap.sum_apply, one_apply_eq_self] at this
    exact this.symm
  · have := congrArg (fun T : Module.End F (Grass K V k → F) => T f) (adjEnd_mul_specProj k hj)
    simpa only [mul_apply_eq_comp, LinearMap.smul_apply] using this

end Projections

end SubspaceConvolution
