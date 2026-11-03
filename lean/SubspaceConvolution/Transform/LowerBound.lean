/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.LBAux
import SubspaceConvolution.Transform.Incidence
import SubspaceConvolution.Circuit.SLP
import SubspaceConvolution.Circuit.Morgenstern

/-!
# A matching lower bound for incidence (Appendix F, Theorem 7)

Let `dim V = 4r` and `I = I^{r,3r}`, a square matrix (`|Gr(4r, r)| = |Gr(4r, 3r)|`).

* `LowerBoundAux.card_common_super` — `(IᵀI)(U, W) = |Gr(2r+t, r+t)| = |Gr(2r+t, r)| =
  ∑_{L ≤ U ∩ W} c_{dim L}` (`t = dim(U ∩ W)`) with `c_j = |Gr(2r, r-j)| q^{j(r+j)}` (`coefC`,
  `coefC_self : c_r = q^{2r²}`), through the `q`-Vandermonde identity `LBAux.gr_vandermonde`.
* `LowerBoundAux.incidT_incid_apply` — `(IᵀI x)(U) = ∑_{L ≤ U} c_{dim L} ∑_{W ≥ L} x_W`.
* `LowerBoundAux.sum_sq_incid_ge` — `‖I x‖² = ∑_L c_{dim L} (∑_{U ≥ L} x_U)² ≥ q^{2r²} ‖x‖²`.
* `LowerBoundAux.sq_det_ge_of_quadForm` — if `‖B x‖² ≥ c ‖x‖²` for all `x` then `det(B)² ≥ c^v`
  (all eigenvalues of `BᵀB` are at least `c`); hence `LowerBoundAux.abs_det_incMat_ge`:
  `|det I| ≥ q^{r² v}` for the square incidence matrix.
* `incidence_lower_bound` — **Theorem 7**: with Morgenstern's bound (`Circuit.morgenstern`),
  `Ω_q(v log v)` bounded-coefficient gates, `v = |Gr(4r, r)|` (here `c = 1/5`).
* `incidence_lower_bound_attained` — the algorithm of Theorem 2 attains it.

Helper lemmas live in the namespace `SubspaceConvolution.LowerBoundAux`.
-/

open Finset Module Matrix

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

namespace LowerBoundAux

/-! ### The Gram matrix of the incidence matrix -/

section Gram

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The coefficients `c_j = |Gr(2r, r-j)| q^{j(r+j)}`. -/
noncomputable def coefC (K : Type*) [Field K] [Fintype K] (r j : ℕ) : ℕ :=
  gr K (2 * r) (r - j) * Fintype.card K ^ (j * (r + j))

theorem coefC_self (K : Type*) [Field K] [Fintype K] (r : ℕ) :
    coefC K r r = Fintype.card K ^ (2 * r ^ 2) := by
  rw [coefC, Nat.sub_self, gr_zero_right, one_mul]
  ring_nf

open Classical in
/-- `(IᵀI)(U, U') = ∑_{L ≤ U ∩ U'} c_{dim L}` (proof of Theorem 7). -/
theorem card_common_super {r : ℕ} (hV : finrank K V = 4 * r) (U U' : Grass K V r) :
    #(univ.filter fun W : Grass K V (3 * r) => U.1 ≤ W.1 ∧ U'.1 ≤ W.1) =
      ∑ L ∈ univ.filter (fun L : Submodule K V => L ≤ U.1 ⊓ U'.1), coefC K r (finrank K L) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U.1 U'.1
  rw [U.2, U'.2] at hdim
  have htr : finrank K (U.1 ⊓ U'.1 : Submodule K V) ≤ r := by
    have := Submodule.finrank_mono (inf_le_left : U.1 ⊓ U'.1 ≤ U.1)
    rwa [U.2] at this
  have h1 : (univ.filter fun W : Grass K V (3 * r) => U.1 ≤ W.1 ∧ U'.1 ≤ W.1) =
      univ.filter fun W : Grass K V (3 * r) => U.1 ⊔ U'.1 ≤ W.1 := by
    ext W
    simp only [mem_filter, mem_univ, true_and, sup_le_iff]
  rw [h1, LBAux.card_superGrass _ (by omega), hV, LBAux.sum_le_eq_sum_range]
  set t := finrank K (U.1 ⊓ U'.1 : Submodule K V) with ht
  have e1 : 4 * r - finrank K (U.1 ⊔ U'.1 : Submodule K V) = 2 * r + t := by omega
  have e2 : 3 * r - finrank K (U.1 ⊔ U'.1 : Submodule K V) = 2 * r + t - r := by omega
  rw [e1, e2, gr_symm K (by omega : r ≤ 2 * r + t), LBAux.gr_vandermonde K (2 * r) t r]
  rw [← Finset.sum_subset (range_subset_range.2 (by omega : t + 1 ≤ r + 1))]
  · refine sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, coefC, show 2 * r + j - r = r + j by omega]
    ring
  · intro j hj hj'
    simp only [mem_range] at hj hj'
    rw [gr_eq_zero_of_lt K (by omega : t < j)]
    simp

/-- Expanding a sum of squares of linear forms. -/
theorem sum_sq_linear {α β : Type*} [Fintype α] [Fintype β] (a : β → α → ℝ) (w : β → ℝ)
    (x : α → ℝ) :
    ∑ W, w W * (∑ U, a W U * x U) ^ 2 =
      ∑ U, ∑ U', x U * x U' * ∑ W, w W * (a W U * a W U') := by
  simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U' _ => ?_
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

open Classical in
/-- `‖I x‖² = ∑_{L} c_{dim L} (∑_{U ≥ L} x_U)²` (proof of Theorem 7). -/
theorem sum_sq_incid_eq {r : ℕ} (hV : finrank K V = 4 * r) (x : Grass K V r → ℝ) :
    ∑ W : Grass K V (3 * r), (∑ U, (if U.1 ≤ W.1 then (1 : ℝ) else 0) * x U) ^ 2 =
      ∑ L : Submodule K V, (coefC K r (finrank K L) : ℝ) *
        (∑ U : Grass K V r, (if L ≤ U.1 then (1 : ℝ) else 0) * x U) ^ 2 := by
  have h1 := sum_sq_linear (fun (W : Grass K V (3 * r)) (U : Grass K V r) =>
    if U.1 ≤ W.1 then (1 : ℝ) else 0) (fun _ => 1) x
  have h2 := sum_sq_linear (fun (L : Submodule K V) (U : Grass K V r) =>
    if L ≤ U.1 then (1 : ℝ) else 0) (fun L => (coefC K r (finrank K L) : ℝ)) x
  simp only [one_mul] at h1
  rw [h1, h2]
  refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun U' _ => ?_
  congr 1
  have h3 := congrArg (fun n : ℕ => (n : ℝ)) (card_common_super hV U U')
  simp only [Nat.cast_sum] at h3
  rw [Finset.sum_filter] at h3
  simp only [ite_zero_mul_ite_zero, mul_one]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_boole, h3]
  refine Finset.sum_congr rfl fun L _ => ?_
  simp only [le_inf_iff]

open Classical in
/-- `‖I x‖² ≥ q^{2r²} ‖x‖²` (proof of Theorem 7). -/
theorem sum_sq_incid_ge {r : ℕ} (hV : finrank K V = 4 * r) (x : Grass K V r → ℝ) :
    (Fintype.card K : ℝ) ^ (2 * r ^ 2) * ∑ U, x U ^ 2 ≤
      ∑ W : Grass K V (3 * r), (∑ U, (if U.1 ≤ W.1 then (1 : ℝ) else 0) * x U) ^ 2 := by
  rw [sum_sq_incid_eq hV]
  have hsub : ∑ L ∈ univ.filter (fun L : Submodule K V => finrank K L = r),
      (coefC K r (finrank K L) : ℝ) *
        (∑ U : Grass K V r, (if L ≤ U.1 then (1 : ℝ) else 0) * x U) ^ 2
      ≤ ∑ L : Submodule K V, (coefC K r (finrank K L) : ℝ) *
        (∑ U : Grass K V r, (if L ≤ U.1 then (1 : ℝ) else 0) * x U) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun L _ _ => by positivity
  refine le_trans (le_of_eq ?_) hsub
  rw [Finset.mul_sum, Finset.sum_subtype (univ.filter fun L : Submodule K V => finrank K L = r)
    (p := fun L : Submodule K V => finrank K L = r) (by simp)]
  refine Fintype.sum_congr _ _ fun L => ?_
  rw [L.2, coefC_self, Nat.cast_pow]
  congr 1
  rw [Finset.sum_eq_single L]
  · simp
  · intro U _ hUL
    have hne : ¬ (L.1 ≤ U.1) := fun hle =>
      hUL (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [L.2, U.2])).symm)
    simp [hne]
  · simp

open Classical in
/-- `(IᵀI x)(U) = ∑_{L ≤ U} c_{dim L} ∑_{W ≥ L, dim W = r} x(W)` over any commutative ring
(proof of Theorem 7). -/
theorem incidT_incid_apply {R : Type*} [CommRing R] {r : ℕ} (hV : finrank K V = 4 * r)
    (x : Grass K V r → R) (U : Grass K V r) :
    incidT r (3 * r) (incid r (3 * r) x) U =
      ∑ L ∈ univ.filter (fun L : Submodule K V => L ≤ U.1),
        (coefC K r (finrank K L) : R) *
          ∑ W ∈ univ.filter (fun W : Grass K V r => L ≤ W.1), x W := by
  have lhs : incidT r (3 * r) (incid r (3 * r) x) U = ∑ U' : Grass K V r,
      #(univ.filter fun W : Grass K V (3 * r) => U.1 ≤ W.1 ∧ U'.1 ≤ W.1) • x U' := by
    simp only [incidT, incid]
    rw [Finset.sum_comm' (t' := univ)
      (s' := fun U' : Grass K V r =>
        univ.filter fun W : Grass K V (3 * r) => U.1 ≤ W.1 ∧ U'.1 ≤ W.1)]
    · simp only [Finset.sum_const]
    · intro W U'
      simp only [mem_filter, mem_univ, true_and, and_true]
  have rhs : ∑ L ∈ univ.filter (fun L : Submodule K V => L ≤ U.1),
      (coefC K r (finrank K L) : R) * ∑ W ∈ univ.filter (fun W : Grass K V r => L ≤ W.1), x W =
        ∑ U' : Grass K V r, (∑ L ∈ univ.filter (fun L : Submodule K V => L ≤ U.1 ∧ L ≤ U'.1),
          (coefC K r (finrank K L) : R)) * x U' := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (t' := univ)
      (s' := fun U' : Grass K V r => univ.filter fun L : Submodule K V => L ≤ U.1 ∧ L ≤ U'.1)]
    intro L U'
    simp only [mem_filter, mem_univ, true_and, and_true]
  rw [lhs, rhs]
  refine Finset.sum_congr rfl fun U' _ => ?_
  rw [card_common_super hV U U', nsmul_eq_mul, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext L
  simp only [mem_filter, mem_univ, true_and, le_inf_iff]

end Gram

/-! ### Determinants -/

section Det

/-- If `‖B x‖² ≥ c ‖x‖²` for every real vector `x`, then `det(B)² ≥ c^v`: every eigenvalue of the
symmetric matrix `BᵀB` is at least `c`. -/
theorem sq_det_ge_of_quadForm {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ x : n → ℝ, c * (x ⬝ᵥ x) ≤ (B *ᵥ x) ⬝ᵥ (B *ᵥ x)) :
    c ^ Fintype.card n ≤ B.det ^ 2 := by
  have hM := isHermitian_conjTranspose_mul_self B
  have hdet : (Bᴴ * B).det = B.det ^ 2 := by
    rw [det_mul, det_conjTranspose]; simp [sq]
  rw [← hdet, hM.det_eq_prod_eigenvalues]
  have hev : ∀ i, c ≤ hM.eigenvalues i := by
    intro i
    rw [hM.eigenvalues_eq i]
    have h1 : ‖hM.eigenvectorBasis i‖ = 1 := hM.eigenvectorBasis.orthonormal.1 i
    have h2 : (⇑(hM.eigenvectorBasis i) : n → ℝ) ⬝ᵥ ⇑(hM.eigenvectorBasis i) = 1 := by
      have := real_inner_self_eq_norm_sq (hM.eigenvectorBasis i)
      rw [h1, EuclideanSpace.inner_eq_star_dotProduct] at this
      simpa using this
    have h3 := h (⇑(hM.eigenvectorBasis i))
    rw [h2, mul_one] at h3
    simp only [RCLike.re_to_real, star_trivial, conjTranspose_eq_transpose_of_trivial]
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    exact h3
  calc c ^ Fintype.card n = ∏ _i : n, c := by simp
    _ ≤ ∏ i, hM.eigenvalues i := Finset.prod_le_prod₀ (fun _ _ => hc) (fun i _ => hev i)
    _ = _ := by simp

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Classical in
/-- The incidence matrix `I^{r,3r}`, made square through a bijection `e : Gr(3r) ≃ Gr(r)`. -/
noncomputable def incMat {r : ℕ} (e : Grass K V (3 * r) ≃ Grass K V r) :
    Matrix (Grass K V r) (Grass K V r) ℝ :=
  Matrix.of fun i j => if j.1 ≤ (e.symm i).1 then 1 else 0

open Classical in
/-- `|det I| ≥ q^{r² v}`, `v = |Gr(4r, r)|` (proof of Theorem 7). -/
theorem abs_det_incMat_ge {r : ℕ} (hV : finrank K V = 4 * r)
    (e : Grass K V (3 * r) ≃ Grass K V r) :
    (Fintype.card K : ℝ) ^ (r ^ 2 * Fintype.card (Grass K V r)) ≤ |(incMat e).det| := by
  have hq : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
  have h := sq_det_ge_of_quadForm (incMat e) ((Fintype.card K : ℝ) ^ (2 * r ^ 2)) (by positivity)
    (fun x => by
      have h1 := sum_sq_incid_ge hV x
      have h2 : (incMat e *ᵥ x) ⬝ᵥ (incMat e *ᵥ x) =
          ∑ W : Grass K V (3 * r), (∑ U, (if U.1 ≤ W.1 then (1 : ℝ) else 0) * x U) ^ 2 := by
        simp only [dotProduct, mulVec, incMat, of_apply, ← sq]
        exact Equiv.sum_comp e.symm (fun W => (∑ U, (if U.1 ≤ W.1 then (1 : ℝ) else 0) * x U) ^ 2)
      rw [h2]
      simpa [dotProduct, sq] using h1)
  rw [← pow_mul, ← sq_abs] at h
  have h' : ((Fintype.card K : ℝ) ^ (r ^ 2 * Fintype.card (Grass K V r))) ^ 2 ≤
      |(incMat e).det| ^ 2 := by
    rw [← pow_mul]; convert h using 2; ring
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).1 h'

end Det

/-! ### Theorem 7 -/

open Classical in
/-- The bounded-coefficient circuit computing `I^{r,3r}` gives a matrix with `det = det(incMat)`. -/
theorem morgenstern_matrix_eq {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ}
    (e : Grass K V (3 * r) ≃ Grass K V r) :
    (Matrix.of fun i j : Grass K V r =>
        incid (K := K) (V := V) (R := ℂ) r (3 * r) (Pi.single j 1) (e.symm i)) =
      (Complex.ofRealHom).mapMatrix (incMat e) := by
  ext i j
  simp only [of_apply, incid, Finset.sum_pi_single', mem_filter, mem_univ, true_and,
    RingHom.mapMatrix_apply, map_apply, incMat]
  split_ifs <;> simp

end LowerBoundAux

/-- **Theorem 7**, lower bound: applying `I^{r,3r}_{4r}` over `ℂ` with gates `z = αx + βy`,
`|α|, |β| ≤ 1`, takes `Ω_q(v log v)` gates, `v = |Gr(4r, r)|`. -/
theorem incidence_lower_bound (K : Type w) [Field K] [Fintype K] :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ (V : Type v) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V], finrank K V = 4 * r → ∀ s : ℕ,
        LinCost (Metric.closedBall (0 : ℂ) 1) (incid (K := K) (V := V) (R := ℂ) r (3 * r)) s →
          c * (Fintype.card (Grass K V r) : ℝ) * Real.log (Fintype.card (Grass K V r)) ≤ s := by
  refine ⟨1 / 5, by norm_num, fun r hr V _ _ _ hV s hs => ?_⟩
  classical
  have hcard : Fintype.card (Grass K V (3 * r)) = Fintype.card (Grass K V r) := by
    rw [card_grass hV, card_grass hV, show 3 * r = 4 * r - r by omega, gr_symm K (by omega)]
  let e : Grass K V (3 * r) ≃ Grass K V r := Fintype.equivOfCardEq hcard
  have hm := morgenstern e hs
  rw [LowerBoundAux.morgenstern_matrix_eq e, ← RingHom.map_det, Complex.ofRealHom_eq_coe,
    Complex.norm_real, Real.norm_eq_abs] at hm
  have hdet := (LowerBoundAux.abs_det_incMat_ge hV e).trans hm
  set v := Fintype.card (Grass K V r) with hv
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.one_lt_card
  have hq0 : (0 : ℝ) < Fintype.card K := by linarith
  have hlogq : 0 ≤ Real.log (Fintype.card K) := Real.log_nonneg (by linarith)
  -- `r² v log q ≤ s log 2`
  have h1 : (r : ℝ) ^ 2 * v * Real.log (Fintype.card K) ≤ s * Real.log 2 := by
    have := Real.log_le_log (by positivity) hdet
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  -- `log v ≤ 5 r² log q`
  have hv1 : 1 ≤ v := by
    rw [hv, card_grass hV]; exact gr_pos K (by omega)
  have hvle : (v : ℝ) ≤ 4 * (Fintype.card K : ℝ) ^ (3 * r ^ 2) := by
    have := gr_le K (4 * r) r
    rw [show r * (4 * r - r) = 3 * r ^ 2 by
      rw [show 4 * r - r = 3 * r by omega]; ring] at this
    rw [hv, card_grass hV]
    exact_mod_cast this
  have h2 : Real.log v ≤ 5 * (r : ℝ) ^ 2 * Real.log (Fintype.card K) := by
    have hlv := Real.log_le_log (by exact_mod_cast hv1) hvle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlv
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hl2 : Real.log 2 ≤ Real.log (Fintype.card K) := Real.log_le_log (by norm_num) hq2
    have hr1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    push_cast at hlv
    nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  calc 1 / 5 * (v : ℝ) * Real.log v
      ≤ 1 / 5 * v * (5 * (r : ℝ) ^ 2 * Real.log (Fintype.card K)) := by gcongr
    _ = (r : ℝ) ^ 2 * v * Real.log (Fintype.card K) := by ring
    _ ≤ s * Real.log 2 := h1
    _ ≤ s := by nlinarith

/-- **Theorem 7**, upper bound: the algorithm of Theorem 2 applies `I^{r,3r}_{4r}` over `ℂ`
with `O_q(v log v)` gates of modulus at most one. -/
theorem incidence_lower_bound_attained (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ r : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = 4 * r →
        LinCost (Metric.closedBall (0 : ℂ) 1) (incid (K := K) (V := V) (R := ℂ) r (3 * r))
          (C * Fintype.card (Grass K V r) * (Nat.log 2 (Fintype.card (Grass K V r)) + 1)) := by
  obtain ⟨C, hC⟩ := fast_incidence_complex.{v, w} K
  refine ⟨2 * C, fun r V _ _ _ hV => ?_⟩
  have h := hC V r (3 * r) (by omega) (by omega)
  have hcard : Fintype.card (Grass K V (3 * r)) = Fintype.card (Grass K V r) := by
    rw [card_grass hV, card_grass hV, show 3 * r = 4 * r - r by omega, gr_symm K (by omega)]
  rw [hcard] at h
  refine h.mono ?_
  set v := Fintype.card (Grass K V r)
  have hlog : Nat.log 2 (v + v) ≤ Nat.log 2 v + 1 := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · simp [h0]
    · rw [show v + v = v * 2 by ring, Nat.log_mul_base (by norm_num) (by omega)]
  calc C * (v + v) * Nat.log 2 (v + v) ≤ C * (v + v) * (Nat.log 2 v + 1) := by gcongr
    _ = 2 * C * v * (Nat.log 2 v + 1) := by ring

end SubspaceConvolution
