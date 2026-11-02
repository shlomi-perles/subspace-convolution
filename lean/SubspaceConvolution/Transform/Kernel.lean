/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.KernelAux

/-!
# Intersection kernels on the Grassmannian: Theorem 1.4 (Section 5.3)

For `U, W ∈ Gr(V, k)` the distance in the Grassmann graph is `dist(U, W) = k - dim(U ∩ W)`
(`gDist`), and an intersection kernel is `(K f)(U) = ∑_W a_{dist(U,W)} f(W)` (`kernelApply`).

* `extGr`, `zetaT_extGr` — extend `f` by zero below dimension `k`; the upper transform gives
  `H(L) = ∑_{W ⊇ L} f(W)`.
* `moments` — equation (moments): `∑_{L ≤ U, dim L = j} H(L) = ∑_W |Gr(dim(U ∩ W), j)| f(W)`.
* `kernelCoeff`, `kernelCoeff_spec` — equation (kernel-coefficients), by back-substitution.
* `kernelApply_eq_zeta` — equation (two-transforms): `K f = Z (c_{dim} · Zᵀ f)`.
* `finrank_dualAnnihilator_inf`, `grassDualEquiv`, `gDist_grassDualEquiv`, `kernelApply_dual` —
  annihilators preserve distances, which handles `k > n/2`.
* `fast_kernel` — **Theorem 1.4** with fixed coefficients (a linear straight-line program);
  `fast_kernel_arith` — with the coefficients `a_0, …, a_k` as further inputs (an arithmetic
  straight-line program).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

section Identities

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-- Extend a table on `Gr(V,k)` by zero to all subspaces of dimension `≤ k`. -/
noncomputable def extGr (k : ℕ) (f : Grass K V k → R) : SubLE K V k → R :=
  fun U => if h : finrank K U.1 = k then f ⟨U.1, h⟩ else 0

open Classical in
/-- `H(L) = (Zᵀ f)(L) = ∑_{W ⊇ L} f(W)`. -/
theorem zetaT_extGr (k : ℕ) (f : Grass K V k → R) (L : SubLE K V k) :
    zetaT k (extGr k f) L = ∑ W ∈ univ.filter (fun W : Grass K V k => L.1 ≤ W.1), f W := by
  let ι : Grass K V k ↪ SubLE K V k :=
    ⟨fun W => ⟨W.1, W.2.le⟩, fun W W' h =>
      Subtype.ext (congrArg (fun X : SubLE K V k => X.1) h)⟩
  have hmap : ∑ W ∈ univ.filter (fun W : Grass K V k => L.1 ≤ W.1), f W =
      ∑ W ∈ (univ.filter (fun W : Grass K V k => L.1 ≤ W.1)).map ι, extGr k f W := by
    rw [sum_map]
    refine sum_congr rfl fun W _ => ?_
    show f W = if h : finrank K W.1 = k then f ⟨W.1, h⟩ else 0
    rw [dite_eq_left W.2]
  rw [hmap, zetaT]
  symm
  refine sum_subset ?_ ?_
  · intro W hW
    simp only [mem_map, mem_filter, mem_univ, true_and] at hW ⊢
    obtain ⟨W', hW', rfl⟩ := hW
    exact hW'
  · intro W hW hW'
    show (if h : finrank K W.1 = k then f ⟨W.1, h⟩ else 0) = 0
    refine dite_eq_right fun h => ?_
    apply hW'
    simp only [mem_map, mem_filter, mem_univ, true_and]
    exact ⟨⟨W.1, h⟩, (mem_filter.1 hW).2, rfl⟩

open Classical in
/-- Equation (moments). -/
theorem moments (k j : ℕ) (hj : j ≤ k) (f : Grass K V k → R) (U : Grass K V k) :
    ∑ L ∈ univ.filter (fun L : Grass K V j => L.1 ≤ U.1),
        zetaT k (extGr k f) ⟨L.1, L.2.le.trans hj⟩ =
      ∑ W : Grass K V k, (gr K (finrank K (U.1 ⊓ W.1 : Submodule K V)) j : R) * f W := by
  rw [sum_congr rfl fun L _ => zetaT_extGr k f ⟨L.1, L.2.le.trans hj⟩]
  exact sum_grass_le_sum_ge U.1 f

variable (K) in
/-- Equation (kernel-coefficients), back-substitution `c_t = a_{k-t} - ∑_{j<t} |Gr(t,j)| c_j`. -/
noncomputable def kernelCoeff (k : ℕ) (a : ℕ → R) (t : ℕ) : R :=
  a (k - t) - ∑ j : Fin t, (gr K t j : R) * kernelCoeff k a j
termination_by t
decreasing_by exact j.2

/-- The defining recursion of `kernelCoeff`, as a sum over `range t`. -/
theorem kernelCoeff_eq (k : ℕ) (a : ℕ → R) (t : ℕ) :
    kernelCoeff K k a t = a (k - t) - ∑ j ∈ range t, (gr K t j : R) * kernelCoeff K k a j := by
  rw [kernelCoeff, Fin.sum_univ_eq_sum_range (fun j => (gr K t j : R) * kernelCoeff K k a j)]

variable (K) in
/-- Equation (kernel-coefficients): `a_{k-t} = ∑_{j ≤ t} |Gr(t,j)| c_j`.  (The back-substitution
satisfies this for every `t`; only `t ≤ k` is used.) -/
theorem kernelCoeff_spec (k : ℕ) (a : ℕ → R) {t : ℕ} (_ht : t ≤ k) :
    ∑ j ∈ range (t + 1), (gr K t j : R) * kernelCoeff K k a j = a (k - t) := by
  rw [sum_range_succ, gr_self, Nat.cast_one, one_mul, kernelCoeff_eq (K := K) k a t]
  ring

/-- The coefficients `c` depend linearly on `a`. -/
theorem kernelCoeff_sum {ι : Type*} (s : Finset ι) (x : ι → R) (b : ι → ℕ → R) (k t : ℕ) :
    kernelCoeff K k (fun j => ∑ i ∈ s, x i * b i j) t = ∑ i ∈ s, x i * kernelCoeff K k (b i) t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    have h1 : ∑ j ∈ range t, (gr K t j : R) * kernelCoeff K k (fun j => ∑ i ∈ s, x i * b i j) j =
        ∑ i ∈ s, x i * ∑ j ∈ range t, (gr K t j : R) * kernelCoeff K k (b i) j := by
      calc ∑ j ∈ range t, (gr K t j : R) * kernelCoeff K k (fun j => ∑ i ∈ s, x i * b i j) j
          = ∑ j ∈ range t, (gr K t j : R) * ∑ i ∈ s, x i * kernelCoeff K k (b i) j :=
            sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]
        _ = _ := by
            simp_rw [mul_sum]
            rw [sum_comm]
            refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
            ring
    have h2 : ∑ i ∈ s, x i * kernelCoeff K k (b i) t =
        ∑ i ∈ s, x i * (b i (k - t) - ∑ j ∈ range t, (gr K t j : R) * kernelCoeff K k (b i) j) :=
      sum_congr rfl fun i _ => by rw [kernelCoeff_eq (K := K) k (b i) t]
    rw [kernelCoeff_eq, h1, h2]
    simp_rw [mul_sub, sum_sub_distrib]

/-- Only `a_0, …, a_k` matter. -/
theorem kernelApply_congr_coeff (k : ℕ) {a b : ℕ → R} (h : ∀ j ≤ k, a j = b j)
    (f : Grass K V k → R) (U : Grass K V k) : kernelApply k a f U = kernelApply k b f U := by
  unfold kernelApply
  refine sum_congr rfl fun W _ => ?_
  rw [h (gDist k U W) (Nat.sub_le _ _)]

/-- Intersection dimensions on `Gr(V, k)` are at most `k`. -/
theorem finrank_inf_le_of_grass (k : ℕ) (U W : Grass K V k) :
    finrank K (U.1 ⊓ W.1 : Submodule K V) ≤ k :=
  le_of_le_of_eq (Submodule.finrank_mono inf_le_left) U.2

/-- `∑_{j ≤ k} |Gr(t,j)| c_j = a_{k-t}` for `t ≤ k`. -/
theorem sum_fin_gr_kernelCoeff (k : ℕ) (a : ℕ → R) {t : ℕ} (ht : t ≤ k) :
    ∑ j : Fin (k + 1), (gr K t j : R) * kernelCoeff K k a j = a (k - t) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (gr K t j : R) * kernelCoeff K k a j),
    ← kernelCoeff_spec K k a ht]
  symm
  refine sum_subset (range_subset_range.2 (by omega)) fun j _ hj => ?_
  rw [gr_eq_zero_of_lt K (by simpa using hj), Nat.cast_zero, zero_mul]

open Classical in
/-- Equation (two-transforms). -/
theorem kernelApply_eq_zeta (k : ℕ) (a : ℕ → R) (f : Grass K V k → R) (U : Grass K V k) :
    kernelApply k a f U =
      zeta k (fun L => kernelCoeff K k a (finrank K L.1) * zetaT k (extGr k f) L)
        ⟨U.1, U.2.le⟩ := by
  have step : ∀ j : Fin (k + 1),
      (∑ L : Grass K V j, if L.1 ≤ U.1 then kernelCoeff K k a (finrank K L.1) *
          zetaT k (extGr k f) ⟨L.1, L.2.le.trans (Nat.lt_succ_iff.mp j.2)⟩ else 0) =
        kernelCoeff K k a j *
          ∑ W : Grass K V k, (gr K (finrank K (U.1 ⊓ W.1 : Submodule K V)) j : R) * f W := by
    intro j
    rw [← moments k j (Nat.lt_succ_iff.mp j.2) f U, mul_sum, sum_filter]
    refine sum_congr rfl fun L _ => ?_
    have hL : finrank K L.1 = (j : ℕ) := L.2
    simp only [hL]
  calc kernelApply k a f U
      = ∑ W : Grass K V k, (∑ j : Fin (k + 1),
          (gr K (finrank K (U.1 ⊓ W.1 : Submodule K V)) j : R) * kernelCoeff K k a j) * f W := by
        unfold kernelApply gDist
        refine sum_congr rfl fun W _ => ?_
        rw [sum_fin_gr_kernelCoeff k a (finrank_inf_le_of_grass k U W)]
    _ = ∑ j : Fin (k + 1), kernelCoeff K k a j *
          ∑ W : Grass K V k, (gr K (finrank K (U.1 ⊓ W.1 : Submodule K V)) j : R) * f W := by
        simp_rw [sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun W _ => ?_
        ring
    _ = ∑ j : Fin (k + 1), ∑ L : Grass K V j, if L.1 ≤ U.1 then kernelCoeff K k a (finrank K L.1) *
          zetaT k (extGr k f) ⟨L.1, L.2.le.trans (Nat.lt_succ_iff.mp j.2)⟩ else 0 :=
        sum_congr rfl fun j _ => (step j).symm
    _ = _ := by
        rw [zeta, sum_filter, sum_subLE_eq]

/-! ### Annihilators -/

/-- Annihilators: `dim(U° ∩ W°) = n - dim U - dim W + dim(U ∩ W)`. -/
theorem finrank_dualAnnihilator_inf (U W : Submodule K V) :
    finrank K (U.dualAnnihilator ⊓ W.dualAnnihilator : Submodule K (Module.Dual K V)) +
        finrank K U + finrank K W = finrank K V + finrank K (U ⊓ W : Submodule K V) := by
  rw [← Submodule.dualAnnihilator_sup_eq]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (U ⊔ W)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

/-- `U ↦ U°`, from `Gr(V, k)` to `Gr(V*, n - k)`. -/
noncomputable def grassDualEquiv (k : ℕ) (hk : k ≤ finrank K V) :
    Grass K V k ≃ Grass K (Module.Dual K V) (finrank K V - k) where
  toFun U := ⟨U.1.dualAnnihilator, by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq U.1
    rw [U.2] at this
    show finrank K U.1.dualAnnihilator = finrank K V - k
    omega⟩
  invFun W := ⟨W.1.dualCoannihilator, by
    have h1 := Subspace.finrank_dualCoannihilator_eq (Φ := W.1)
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W.1
    rw [W.2, Subspace.dual_finrank_eq] at h2
    show finrank K W.1.dualCoannihilator = k
    omega⟩
  left_inv U := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv W := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq

/-- The underlying subspace of `grassDualEquiv k hk U` is the annihilator `U°`. -/
theorem grassDualEquiv_apply_coe (k : ℕ) (hk : k ≤ finrank K V) (U : Grass K V k) :
    (grassDualEquiv k hk U).1 = U.1.dualAnnihilator := rfl

/-- Annihilators preserve distances. -/
theorem gDist_grassDualEquiv (k : ℕ) (hk : k ≤ finrank K V) (U W : Grass K V k) :
    gDist (finrank K V - k) (grassDualEquiv k hk U) (grassDualEquiv k hk W) = gDist k U W := by
  unfold gDist
  have h := finrank_dualAnnihilator_inf U.1 W.1
  rw [U.2, W.2] at h
  rw [grassDualEquiv_apply_coe, grassDualEquiv_apply_coe]
  omega

/-- An intersection kernel on `Gr(V, k)` is the same kernel on `Gr(V*, n - k)`. -/
theorem kernelApply_dual (k : ℕ) (hk : k ≤ finrank K V) (a : ℕ → R) (f : Grass K V k → R)
    (U : Grass K V k) :
    kernelApply k a f U =
      kernelApply (finrank K V - k) a (fun W => f ((grassDualEquiv k hk).symm W))
        (grassDualEquiv k hk U) := by
  unfold kernelApply
  refine Fintype.sum_equiv (grassDualEquiv k hk) _ _ fun W => ?_
  dsimp only
  rw [gDist_grassDualEquiv, Equiv.symm_apply_apply]

end Identities

/-! ### Theorem 1.4 -/

section Cost

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-- Extension by zero is free. -/
theorem extGr_linCost (k : ℕ) :
    LinCost (Set.univ : Set R) (extGr (K := K) (V := V) (R := R) k) 0 := by
  have h := (LinCost.sumElim (LinCost.id (C := (Set.univ : Set R)) (I := Grass K V k))
    (LinCost.zero (C := (Set.univ : Set R)) (I := Grass K V k) (O := Unit))).reindex id
    (fun U : SubLE K V k => if h : finrank K U.1 = k then Sum.inl ⟨U.1, h⟩ else Sum.inr ())
  refine (h.congr ?_).mono (by norm_num)
  funext f U
  simp only [extGr]
  split_ifs <;> rfl

/-- The circuit of equation (two-transforms): `Zᵀ`, one scaling per entry, `Z`. -/
theorem kernelApply_linCost_of (k : ℕ) (a : ℕ → R) {s₁ s₂ : ℕ}
    (hzT : LinCost (Set.univ : Set R) (zetaT (K := K) (V := V) k) s₁)
    (hz : LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k) s₂) :
    LinCost (Set.univ : Set R) (kernelApply (K := K) (V := V) k a)
      (s₁ + Fintype.card (SubLE K V k) + s₂) := by
  have h1 := (extGr_linCost (K := K) (V := V) (R := R) k).comp hzT
  have h2 := h1.comp (LinCost.scale fun L : SubLE K V k => kernelCoeff K k a (finrank K L.1))
  have h3 := h2.comp hz
  have h4 := h3.reindex id (fun U : Grass K V k => (⟨U.1, U.2.le⟩ : SubLE K V k))
  refine (h4.congr ?_).mono (by omega)
  funext f U
  rw [kernelApply_eq_zeta]
  rfl

/-- The coefficients `c_0, …, c_k` from `a_0, …, a_k`: a dense `(k+1) × (k+1)` matrix. -/
theorem kernelCoeff_linCost (k : ℕ) :
    LinCost (Set.univ : Set R)
      (fun (x : Fin (k + 1) → R) (t : Fin (k + 1)) =>
        kernelCoeff K k (fun j => if h : j < k + 1 then x ⟨j, h⟩ else 0) t)
      ((k + 1) * (k + 1)) := by
  have h := LinCost.dense (C := (Set.univ : Set R))
    (fun (t s : Fin (k + 1)) => kernelCoeff K k (fun j => if j = (s : ℕ) then (1 : R) else 0) t)
    (fun _ _ => trivial) trivial trivial
  simp only [Fintype.card_fin] at h
  refine h.congr ?_
  funext x t
  have hx : (fun j => if h : j < k + 1 then x ⟨j, h⟩ else 0) =
      fun j => ∑ s : Fin (k + 1), x s * (if j = (s : ℕ) then (1 : R) else 0) := by
    funext j
    by_cases hj : j < k + 1
    · rw [dite_eq_left hj, Fintype.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro s hs
        rw [ite_eq_right, mul_zero]
        intro h
        exact hs (Fin.ext h.symm)
    · rw [dite_eq_right hj]
      refine (sum_eq_zero fun s _ => ?_).symm
      rw [ite_eq_right, mul_zero]
      intro h
      exact hj (h ▸ s.2)
  rw [hx, kernelCoeff_sum]
  exact sum_congr rfl fun s _ => mul_comm _ _

/-- The arithmetic circuit of equation (two-transforms) with the coefficients as inputs. -/
theorem kernelApply_arithCost_of (k : ℕ) {s₁ s₂ : ℕ}
    (hzT : LinCost (Set.univ : Set R) (zetaT (K := K) (V := V) k) s₁)
    (hz : LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k) s₂) :
    ArithCost (fun (x : Fin (k + 1) ⊕ Grass K V k → R) (U : Grass K V k) =>
        kernelApply k (fun j => if h : j < k + 1 then x (Sum.inl ⟨j, h⟩) else 0)
          (fun W => x (Sum.inr W)) U)
      ((k + 1) * (k + 1) + s₁ + Fintype.card (SubLE K V k) + s₂) := by
  have hc := (kernelCoeff_linCost (K := K) (R := R) k).reindex
    (I' := Fin (k + 1) ⊕ Grass K V k) Sum.inl
    (fun L : SubLE K V k => (⟨finrank K L.1, Nat.lt_succ_of_le L.2⟩ : Fin (k + 1)))
  have hH := ((extGr_linCost (K := K) (V := V) (R := R) k).comp hzT).reindex
    (I' := Fin (k + 1) ⊕ Grass K V k) Sum.inr id
  have h1 := ArithCost.of_linCost (hc.sumElim hH)
  have h2 := h1.comp (ArithCost.mulPointwise (R := R) (J := SubLE K V k))
  have h3 := h2.comp (ArithCost.of_linCost hz)
  have h4 := h3.reindex id (fun U : Grass K V k => (⟨U.1, U.2.le⟩ : SubLE K V k))
  refine (h4.congr ?_).mono (by omega)
  funext x U
  rw [kernelApply_eq_zeta]
  rfl

/-- The operation count of equation (two-transforms) is `O(N log N)` for `2k ≤ n`. -/
theorem kernel_bound {C n k M N : ℕ} (hM : M ≤ 2 * N) (hnk : n * k ≤ 2 * Nat.log 2 N) :
    C * n * k * M + M + C * n * k * M ≤ (8 * C + 2) * N * (Nat.log 2 N + 1) := by
  have h1 : C * n * k * M ≤ 4 * (C * N * Nat.log 2 N) := by
    calc C * n * k * M = C * (n * k) * M := by ring
      _ ≤ C * (2 * Nat.log 2 N) * (2 * N) := by gcongr
      _ = 4 * (C * N * Nat.log 2 N) := by ring
  have h2 : (8 * C + 2) * N * (Nat.log 2 N + 1) =
      8 * (C * N * Nat.log 2 N) + 8 * (C * N) + 2 * (N * Nat.log 2 N) + 2 * N := by ring
  omega

/-- The operation count of the arithmetic version, including the `(k+1)²` back-substitution. -/
theorem kernel_arith_bound {C n k M N : ℕ} (hM : M ≤ 2 * N) (hnk : n * k ≤ 2 * Nat.log 2 N)
    (hkn : 2 * k ≤ n) (hN : 1 ≤ N) :
    (k + 1) * (k + 1) + C * n * k * M + M + C * n * k * M ≤
      (8 * C + 9) * N * (Nat.log 2 N + 1) := by
  have h0 := kernel_bound (C := C) hM hnk
  have hk : (k + 1) * (k + 1) ≤ 3 * (n * k) + 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · nlinarith
  have hL : 3 * (n * k) + 1 ≤ 7 * (N * (Nat.log 2 N + 1)) := by
    have : Nat.log 2 N + 1 ≤ N * (Nat.log 2 N + 1) := Nat.le_mul_of_pos_left _ hN
    omega
  have h2 : (8 * C + 9) * N * (Nat.log 2 N + 1) =
      (8 * C + 2) * N * (Nat.log 2 N + 1) + 7 * (N * (Nat.log 2 N + 1)) := by ring
  omega

/-- **Theorem 1.4** for `2k ≤ n`, from the costs of `Z` and `Zᵀ` in Theorem 1.1. -/
theorem fast_kernel_half {C : ℕ} (k : ℕ) (a : ℕ → R) (hkn : 2 * k ≤ finrank K V)
    (hz : LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k)
      (C * finrank K V * k * Fintype.card (SubLE K V k)))
    (hzT : LinCost (Set.univ : Set R) (zetaT (K := K) (V := V) k)
      (C * finrank K V * k * Fintype.card (SubLE K V k))) :
    LinCost (Set.univ : Set R) (kernelApply (K := K) (V := V) k a)
      ((8 * C + 2) * Fintype.card (Grass K V k) *
        (Nat.log 2 (Fintype.card (Grass K V k)) + 1)) := by
  refine (kernelApply_linCost_of k a hzT hz).mono (kernel_bound ?_ ?_)
  · rw [card_subLE rfl, card_grass rfl]
    exact numLE_le_two_mul_gr K hkn
  · rw [card_grass rfl]
    exact mul_le_log_gr K hkn

/-- **Theorem 1.4** (arithmetic version) for `2k ≤ n`. -/
theorem fast_kernel_arith_half {C : ℕ} (k : ℕ) (hkn : 2 * k ≤ finrank K V)
    (hz : LinCost (Set.univ : Set R) (zeta (K := K) (V := V) k)
      (C * finrank K V * k * Fintype.card (SubLE K V k)))
    (hzT : LinCost (Set.univ : Set R) (zetaT (K := K) (V := V) k)
      (C * finrank K V * k * Fintype.card (SubLE K V k))) :
    ArithCost (fun (x : Fin (k + 1) ⊕ Grass K V k → R) (U : Grass K V k) =>
        kernelApply k (fun j => if h : j < k + 1 then x (Sum.inl ⟨j, h⟩) else 0)
          (fun W => x (Sum.inr W)) U)
      ((8 * C + 9) * Fintype.card (Grass K V k) *
        (Nat.log 2 (Fintype.card (Grass K V k)) + 1)) := by
  refine (kernelApply_arithCost_of k hzT hz).mono ?_
  have h := kernel_arith_bound (C := C) (k := k) (n := finrank K V)
    (M := Fintype.card (SubLE K V k)) (N := Fintype.card (Grass K V k)) ?_ ?_ hkn ?_
  · simpa only [add_assoc] using h
  · rw [card_subLE rfl, card_grass rfl]
    exact numLE_le_two_mul_gr K hkn
  · rw [card_grass rfl]
    exact mul_le_log_gr K hkn
  · rw [card_grass rfl]
    exact gr_pos K (by omega)

end Cost

/-- **Theorem 1.4** (Fast multiplication on the Grassmann graph), coefficients fixed: for
`V = F_q^n` and every `k`, the intersection kernel `f ↦ (U ↦ ∑_W a_{dist(U,W)} f(W))` on
`Gr(V, k)` is computed by a linear straight-line program with `O_q(N log N)` gates,
`N = |Gr(n, k)|`, over any commutative ring in which `p` is invertible. -/
theorem fast_kernel (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ) (a : ℕ → R),
        LinCost (Set.univ : Set R) (kernelApply (K := K) (V := V) k a)
          (C * Fintype.card (Grass K V k) * (Nat.log 2 (Fintype.card (Grass K V k)) + 1)) := by
  obtain ⟨C₁, hC₁⟩ := fast_subspace_summation.{u, v, w} K
  obtain ⟨C₂, hC₂⟩ := fast_subspace_summation.{u, max v w, w} K
  refine ⟨8 * (C₁ + C₂) + 2, fun R _ hR V _ _ _ k a => ?_⟩
  by_cases hkn : k ≤ finrank K V
  · by_cases h2k : 2 * k ≤ finrank K V
    · have h := hC₁ R hR V k hkn
      refine (fast_kernel_half k a h2k h.1 h.2.2.1).mono ?_
      gcongr
      omega
    · -- `k > n/2`: annihilators
      set n := finrank K V
      have hn : finrank K (Module.Dual K V) = n := Subspace.dual_finrank_eq
      have h := hC₂ R hR (Module.Dual K V) (n - k) (by omega)
      have hD := fast_kernel_half (V := Module.Dual K V) (n - k) a (by omega) h.1 h.2.2.1
      have hE := hD.reindex (grassDualEquiv k hkn).symm (grassDualEquiv k hkn)
      rw [Fintype.card_congr (grassDualEquiv k hkn).symm] at hE
      refine (hE.congr ?_).mono ?_
      · funext f U
        exact (kernelApply_dual k hkn a f U).symm
      · gcongr
        omega
  · have : IsEmpty (Grass K V k) :=
      ⟨fun U => hkn (U.2 ▸ Submodule.finrank_le U.1)⟩
    exact LinCost.empty _ _

/-- **Theorem 1.4** with the coefficients `a_0, …, a_k` as inputs (arithmetic program). -/
theorem fast_kernel_arith (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ),
        ArithCost (fun (x : Fin (k + 1) ⊕ Grass K V k → R) (U : Grass K V k) =>
            kernelApply k (fun j => if h : j < k + 1 then x (Sum.inl ⟨j, h⟩) else 0)
              (fun W => x (Sum.inr W)) U)
          (C * Fintype.card (Grass K V k) * (Nat.log 2 (Fintype.card (Grass K V k)) + 1)) := by
  obtain ⟨C₁, hC₁⟩ := fast_subspace_summation.{u, v, w} K
  obtain ⟨C₂, hC₂⟩ := fast_subspace_summation.{u, max v w, w} K
  refine ⟨8 * (C₁ + C₂) + 9, fun R _ hR V _ _ _ k => ?_⟩
  by_cases hkn : k ≤ finrank K V
  · by_cases h2k : 2 * k ≤ finrank K V
    · have h := hC₁ R hR V k hkn
      refine (fast_kernel_arith_half k h2k h.1 h.2.2.1).mono ?_
      gcongr
      omega
    · -- `k > n/2`: annihilators
      set n := finrank K V
      have hn : finrank K (Module.Dual K V) = n := Subspace.dual_finrank_eq
      have h := hC₂ R hR (Module.Dual K V) (n - k) (by omega)
      have hD := fast_kernel_arith_half (V := Module.Dual K V) (n - k) (by omega) h.1 h.2.2.1
      have hE := hD.reindex
        (Sum.map (fun j : Fin (n - k + 1) => (⟨j.1, by omega⟩ : Fin (k + 1)))
          (grassDualEquiv k hkn).symm)
        (grassDualEquiv k hkn)
      rw [Fintype.card_congr (grassDualEquiv k hkn).symm] at hE
      refine (hE.congr ?_).mono ?_
      · funext x U
        rw [kernelApply_dual k hkn]
        refine kernelApply_congr_coeff _ (fun j hj => ?_) _ _
        have h1 : j < n - k + 1 := by omega
        have h2 : j < k + 1 := by omega
        rw [dite_eq_left h1, dite_eq_left h2]
        rfl
      · gcongr
        omega
  · have : IsEmpty (Grass K V k) :=
      ⟨fun U => hkn (U.2 ▸ Submodule.finrank_le U.1)⟩
    exact ArithCost.of_linCost (LinCost.empty (C := (Set.univ : Set R)) _ _)

end SubspaceConvolution
