/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Grassmann

/-!
# Invariant linear systems on the Grassmannian (Appendix E)

Fix `E ∈ Gr(V, k)` and let `O_j = {U : dist(U, E) = j}`, `b_j = 𝟙_{O_j}` (`orbitInd`), for
`0 ≤ j ≤ d = min(k, n - k)` (`gdiam`).  Choose `U_i ∈ O_i` (`orbitRep`).  For an intersection
kernel `K(U, W) = a_{dist(U, W)}` over any field `F`:

* `kernelApply_orbitInd` — `K b_j = ∑_i B_{ij} b_i` with `B_{ij} = (K b_j)(U_i)`
  (equation (small-system), `smallSystem`): the stabilizer of `E` is transitive on each `O_i`
  and commutes with `K`.
* `kernelApply_inverse` — if `B c = (1, 0, …, 0)ᵀ`, the kernel `C(U, W) = c_{dist(U, W)}` is a
  two-sided inverse of `K` (`(KC)(U, E) = [U = E]`, invariance gives all columns; no division by
  orbit sizes).
* `bijective_kernelApply_iff` — `K` is invertible iff `det B ≠ 0`.
-/

open Finset Module Matrix

set_option linter.unusedSectionVars false

universe u v w

namespace SubspaceConvolution

variable (K : Type w) [Field K] (V : Type v) [AddCommGroup V] [Module K V] in
/-- The diameter `d = min(k, n - k)` of `J_q(n, k)`. -/
noncomputable abbrev gdiam (k : ℕ) : ℕ := min k (finrank K V - k)

section Invariant

variable {K : Type w} [Field K] [Fintype K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : Type u} [Field F]

open Classical in
/-- The indicator `b_j` of the orbit `O_j = {U : dist(U, E) = j}`. -/
noncomputable def orbitInd (k : ℕ) (E : Grass K V k) (j : ℕ) : Grass K V k → F :=
  fun U => if gDist k U E = j then 1 else 0

/-- Representatives `U_i ∈ O_i`, `0 ≤ i ≤ d`. -/
noncomputable def orbitRep {k : ℕ} (E : Grass K V k) (i : Fin (gdiam K V k + 1)) : Grass K V k :=
  (exists_gDist_eq E (Nat.lt_succ_iff.1 i.2)).choose

theorem gDist_orbitRep {k : ℕ} (E : Grass K V k) (i : Fin (gdiam K V k + 1)) :
    gDist k (orbitRep E i) E = i :=
  (exists_gDist_eq E (Nat.lt_succ_iff.1 i.2)).choose_spec

/-- Equation (small-system): `B_{ij} = (K b_j)(U_i)`. -/
noncomputable def smallSystem (k : ℕ) (a : ℕ → F) (E : Grass K V k) :
    Matrix (Fin (gdiam K V k + 1)) (Fin (gdiam K V k + 1)) F :=
  Matrix.of fun i j => kernelApply k a (orbitInd k E j) (orbitRep E i)

/-- The coefficients `c_0, …, c_d` extended by zero. -/
def extCoeff {d : ℕ} (c : Fin (d + 1) → F) : ℕ → F :=
  fun j => if h : j < d + 1 then c ⟨j, h⟩ else 0

theorem gDist_lt_gdiam_succ {k : ℕ} (U E : Grass K V k) : gDist k U E < gdiam K V k + 1 :=
  Nat.lt_succ_of_le (gDist_le_min U E)

/-- The stabilizer of `E` is transitive on each orbit `O_i`. -/
theorem exists_stab {k : ℕ} {E U U' : Grass K V k} (h : gDist k U E = gDist k U' E) :
    ∃ g : V ≃ₗ[K] V, grassMap g U = U' ∧ grassMap g E = E :=
  exists_grassMap_pair h

theorem orbitInd_grassMap {k : ℕ} {E : Grass K V k} {g : V ≃ₗ[K] V} (hg : grassMap g E = E)
    (j : ℕ) (W : Grass K V k) :
    orbitInd (F := F) k E j (grassMap g W) = orbitInd k E j W := by
  unfold orbitInd
  conv_lhs => rw [← hg, gDist_grassMap]

/-- `K b_j` is constant on each orbit. -/
theorem kernelApply_orbitInd_eq {k : ℕ} (a : ℕ → F) {E U U' : Grass K V k}
    (h : gDist k U E = gDist k U' E) (j : ℕ) :
    kernelApply k a (orbitInd k E j) U' = kernelApply k a (orbitInd k E j) U := by
  obtain ⟨g, hgU, hgE⟩ := exists_stab h
  rw [← hgU, kernelApply_grassMap]
  congr 1
  funext W
  exact orbitInd_grassMap hgE j W

/-- Functions constant on orbits: `(∑_i x_i b_i)(U) = x_{dist(U, E)}`. -/
theorem sum_smul_orbitInd_apply {k : ℕ} (E : Grass K V k) (x : Fin (gdiam K V k + 1) → F)
    (U : Grass K V k) :
    (∑ i, x i • orbitInd k E i) U = x ⟨gDist k U E, gDist_lt_gdiam_succ U E⟩ := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, orbitInd, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (⟨gDist k U E, gDist_lt_gdiam_succ U E⟩ : Fin (gdiam K V k + 1))]
  · exact ite_eq_left rfl
  · intro i _ hi
    exact ite_eq_right fun h => hi (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem extCoeff_gDist {k : ℕ} (E : Grass K V k) (c : Fin (gdiam K V k + 1) → F) :
    (fun W => extCoeff c (gDist k W E)) = ∑ i, c i • orbitInd k E i := by
  funext W
  rw [sum_smul_orbitInd_apply, extCoeff, dite_eq_left (gDist_lt_gdiam_succ W E)]

/-- `K` preserves the span of the `b_j`: `K b_j = ∑_i B_{ij} b_i`. -/
theorem kernelApply_orbitInd {k : ℕ} (a : ℕ → F) (E : Grass K V k)
    (j : Fin (gdiam K V k + 1)) :
    kernelApply k a (orbitInd k E j) = ∑ i, smallSystem k a E i j • orbitInd k E i := by
  funext U
  rw [sum_smul_orbitInd_apply, smallSystem, Matrix.of_apply]
  exact (kernelApply_orbitInd_eq a (by rw [gDist_orbitRep]) j)

theorem kernelApply_sum_smul {k : ℕ} (a : ℕ → F) {ι : Type*} (s : Finset ι) (x : ι → F)
    (f : ι → Grass K V k → F) :
    kernelApply k a (∑ i ∈ s, x i • f i) = ∑ i ∈ s, x i • kernelApply k a (f i) := by
  have := map_sum (kernelLin K V k a) (fun i => x i • f i) s
  simpa only [kernelLin_apply, map_smul] using this

/-- `K (∑_j c_j b_j) = ∑_i (B c)_i b_i`. -/
theorem kernelApply_sum_orbitInd {k : ℕ} (a : ℕ → F) (E : Grass K V k)
    (c : Fin (gdiam K V k + 1) → F) :
    kernelApply k a (∑ j, c j • orbitInd k E j) = ∑ i, (smallSystem k a E *ᵥ c) i • orbitInd k E i := by
  rw [kernelApply_sum_smul]
  simp only [kernelApply_orbitInd, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Step 1: `(KC)(U, E) = [U = E]`. -/
theorem kernel_comp_col {k : ℕ} (a : ℕ → F) (E : Grass K V k) (c : Fin (gdiam K V k + 1) → F)
    (hc : smallSystem k a E *ᵥ c = Pi.single 0 1) (U : Grass K V k) :
    kernelApply k a (fun W => extCoeff c (gDist k W E)) U = if U = E then 1 else 0 := by
  rw [extCoeff_gDist, kernelApply_sum_orbitInd, hc, sum_smul_orbitInd_apply]
  by_cases hU : U = E
  · subst hU
    rw [ite_eq_left rfl, show (⟨gDist k U U, gDist_lt_gdiam_succ U U⟩ : Fin (gdiam K V k + 1)) = 0
      from Fin.ext (gDist_self U)]
    simp
  · rw [ite_eq_right hU]
    have : gDist k U E ≠ 0 := fun h => hU (gDist_eq_zero_iff.1 h)
    simp only [Pi.single_apply]
    exact ite_eq_right fun h => this (congrArg Fin.val h)

/-- Step 2: invariance gives every column, `(KC)(U, X) = [U = X]`. -/
theorem kernel_comp_eq {k : ℕ} (a : ℕ → F) (E : Grass K V k) (c : Fin (gdiam K V k + 1) → F)
    (hc : smallSystem k a E *ᵥ c = Pi.single 0 1) (U X : Grass K V k) :
    ∑ W, a (gDist k U W) * extCoeff c (gDist k W X) = if U = X then 1 else 0 := by
  obtain ⟨g, rfl⟩ := exists_grassMap E X
  have hU : grassMap g (grassMap g.symm U) = U := by
    simpa using grassMap_symm_grassMap g.symm U
  change kernelApply k a (fun W => extCoeff c (gDist k W (grassMap g E))) U = _
  conv_lhs => rw [← hU]
  rw [kernelApply_grassMap]
  simp only [gDist_grassMap]
  rw [kernel_comp_col a E c hc]
  by_cases h : grassMap g.symm U = E
  · rw [ite_eq_left h, ite_eq_left (by rw [← h, hU])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h']; exact grassMap_symm_grassMap g E))]

/-- **Invariant linear systems**: if `B c = (1, 0, …, 0)ᵀ`, the kernel `C(U, W) = c_{dist(U, W)}`
is a two-sided inverse of `K`. -/
theorem kernelApply_inverse {k : ℕ} (a : ℕ → F) (E : Grass K V k)
    (c : Fin (gdiam K V k + 1) → F) (hc : smallSystem k a E *ᵥ c = Pi.single 0 1) :
    (∀ f : Grass K V k → F, kernelApply k a (kernelApply k (extCoeff c) f) = f) ∧
      (∀ f : Grass K V k → F, kernelApply k (extCoeff c) (kernelApply k a f) = f) := by
  classical
  constructor
  · intro f
    funext U
    simp only [kernelApply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, kernel_comp_eq a E c hc U, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · intro f
    funext U
    simp only [kernelApply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have key : ∀ X, ∑ W, extCoeff c (gDist k U W) * a (gDist k W X) = if X = U then 1 else 0 := by
      intro X
      rw [← kernel_comp_eq a E c hc X U]
      refine Finset.sum_congr rfl fun W _ => ?_
      rw [mul_comm, gDist_comm U W, gDist_comm W X]
    simp_rw [← mul_assoc, ← Finset.sum_mul, key, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]

/-- **`K` is invertible iff the small matrix `B` is.** -/
theorem bijective_kernelApply_iff {k : ℕ} (a : ℕ → F) (E : Grass K V k) :
    Function.Bijective (kernelApply (K := K) (V := V) k a) ↔ (smallSystem k a E).det ≠ 0 := by
  constructor
  · intro hK hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have h0 : kernelApply k a (∑ j, c j • orbitInd k E j) = kernelApply k a 0 := by
      rw [kernelApply_sum_orbitInd, hc]
      funext U
      simp [kernelApply]
    have hf := hK.1 h0
    apply hc0
    funext j
    have := congrFun hf (orbitRep E j)
    rw [sum_smul_orbitInd_apply] at this
    simp only [Pi.zero_apply] at this ⊢
    rw [← this]
    exact congrArg c (Fin.ext (gDist_orbitRep E j).symm)
  · intro hdet
    have hunit : IsUnit (smallSystem k a E).det := isUnit_iff_ne_zero.2 hdet
    set c := (smallSystem k a E)⁻¹ *ᵥ Pi.single 0 1 with hc_def
    have hc : smallSystem k a E *ᵥ c = Pi.single 0 1 := by
      rw [hc_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    obtain ⟨h1, h2⟩ := kernelApply_inverse a E c hc
    exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

end Invariant

end SubspaceConvolution
