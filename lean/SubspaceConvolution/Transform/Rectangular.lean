/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.RectAux

/-!
# Rectangular kernels (Appendix C, "Different input and output dimensions")

Kernels with columns indexed by `Gr(n, a)` and rows by `Gr(n, b)` whose entry `K(W, U)` depends
only on `dim(U ∩ W)`:

* `rectKernel a b κ` — `(K f)(W) = ∑_{U ∈ Gr(V, a)} κ(dim(U ∩ W)) f(U)`, `W ∈ Gr(V, b)`.
* `rectKernel_eq_sum_incid` — back-substitution in equation (29), through equation
  (31): `K f = ∑_{t ≤ min(a,b)} c_t I^{t,b} (I^{t,a})ᵀ f` with `c = rectCoeff K κ`.
* `finrank_dualAnnihilator_inf_grass`, `rectKernel_dual` — annihilators change the intersection
  dimension to `n - a - b + dim(U ∩ W)`: the kernel on `V` is the kernel
  `κ'(s) = κ(s + a + b - n)` from `Gr(V*, n - a)` to `Gr(V*, n - b)`.
* `rectKernel_linCost_half`, **`fast_rectKernel`** — `S poly(n)` work, precisely
  `O_q((n + 1)³ S)` with `S = |Gr(n, a)| + |Gr(n, b)|`: for `min(a, b) ≤ n/2` every
  intermediate table is at most `S` (unimodality) and each of the `≤ n + 1` terms costs
  `O(S log S) = O_q(n² S)` by Theorem 2; otherwise take annihilators.
* Special cases: the sums by intersection dimension `rectInterSum` (`κ(s) = [s = t]`,
  `rectInterSum_eq_rectKernel`, `fast_rectInterSum`), and for `a = b` the intersection kernels
  of Theorem 3 (`rectKernel_self_eq_kernelApply`).
* Unions of dimensions, on the table of all subspaces: `allKernel κ`,
  `(K f)(W) = ∑_U κ(dim U, dim W, dim(U ∩ W)) f(U)`; `allKernel_eq_zetaAll` (one upper transform
  per input dimension, one weighted lower transform per output dimension) and
  **`fast_allKernel`**, `O_q((n + 1)³ N_q(n))` operations.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

/-! ### The kernel and its expansion in incidence transforms -/

section Identities

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-- A rectangular kernel from `Gr(V, a)` to `Gr(V, b)` depending only on the intersection
dimension: `(K f)(W) = ∑_U κ(dim(U ∩ W)) f(U)`. -/
noncomputable def rectKernel (a b : ℕ) (κ : ℕ → R) (f : Grass K V a → R) (W : Grass K V b) : R :=
  ∑ U, κ (finrank K (U.1 ⊓ W.1 : Submodule K V)) * f U

/-- Intersection dimensions are at most `min(a, b)`. -/
theorem finrank_inf_le_min (a b : ℕ) (U : Grass K V a) (W : Grass K V b) :
    finrank K (U.1 ⊓ W.1 : Submodule K V) ≤ min a b :=
  le_min (le_of_le_of_eq (Submodule.finrank_mono inf_le_left) U.2)
    (le_of_le_of_eq (Submodule.finrank_mono inf_le_right) W.2)

/-- **Back-substitution in equation (29)**, through equation (31):
`K f = ∑_{t ≤ min(a,b)} c_t I^{t,b} (I^{t,a})ᵀ f`, where `c_t = κ(t) - ∑_{j<t} |Gr(t,j)| c_j`. -/
theorem rectKernel_eq_sum_incid (a b : ℕ) (κ : ℕ → R) (f : Grass K V a → R)
    (W : Grass K V b) :
    rectKernel a b κ f W =
      ∑ t ∈ range (min a b + 1), rectCoeff K κ t * incid t b (incidT t a f) W := by
  simp_rw [rect_moments, mul_sum]
  rw [sum_comm]
  unfold rectKernel
  refine sum_congr rfl fun U _ => ?_
  rw [← sum_gr_rectCoeff K κ (finrank_inf_le_min a b U W), sum_mul]
  refine sum_congr rfl fun t _ => ?_
  ring

/-- For `a = b = k` a rectangular kernel is an intersection kernel on `Gr(V, k)`
(Theorem 3), with `a_i = κ(k - i)`. -/
theorem rectKernel_self_eq_kernelApply (k : ℕ) (κ : ℕ → R) :
    rectKernel (K := K) (V := V) k k κ = kernelApply k (fun i => κ (k - i)) := by
  funext f W
  unfold rectKernel kernelApply gDist
  refine sum_congr rfl fun U _ => ?_
  dsimp only
  rw [Nat.sub_sub_self (finrank_inf_le_of_grass k W U), inf_comm]

open Classical in
/-- Sums by intersection dimension, `h_t(W) = ∑_{U ∈ Gr(V, a), dim(U ∩ W) = t} f(U)` for
`W ∈ Gr(V, b)`. -/
noncomputable def rectInterSum (a b t : ℕ) (f : Grass K V a → R) (W : Grass K V b) : R :=
  ∑ U ∈ univ.filter (fun U : Grass K V a => finrank K (U.1 ⊓ W.1 : Submodule K V) = t), f U

/-- The sums by intersection dimension are the kernel `κ(s) = [s = t]`. -/
theorem rectInterSum_eq_rectKernel (a b t : ℕ) :
    rectInterSum (K := K) (V := V) (R := R) a b t =
      rectKernel a b (fun s => if s = t then 1 else 0) := by
  funext f W
  unfold rectInterSum rectKernel
  rw [sum_filter]
  refine sum_congr rfl fun U _ => ?_
  by_cases h : finrank K (U.1 ⊓ W.1 : Submodule K V) = t <;> simp [h]

/-! ### Annihilators -/

/-- Annihilators: for `U ∈ Gr(V, a)`, `W ∈ Gr(V, b)`,
`dim(U° ∩ W°) = n - a - b + dim(U ∩ W)` (written `n + dim(U ∩ W) - a - b`, which is exact in
`ℕ` since `dim(U ∩ W) ≥ a + b - n`). -/
theorem finrank_dualAnnihilator_inf_grass (a b : ℕ) (U : Grass K V a) (W : Grass K V b) :
    finrank K (U.1.dualAnnihilator ⊓ W.1.dualAnnihilator : Submodule K (Module.Dual K V)) =
      finrank K V + finrank K (U.1 ⊓ W.1 : Submodule K V) - a - b := by
  have h := finrank_dualAnnihilator_inf U.1 W.1
  rw [U.2, W.2] at h
  omega

/-- The same in the other direction: `dim(U ∩ W) = dim(U° ∩ W°) + a + b - n`. -/
theorem finrank_inf_eq_dualAnnihilator (a b : ℕ) (U : Grass K V a) (W : Grass K V b) :
    finrank K (U.1 ⊓ W.1 : Submodule K V) =
      finrank K (U.1.dualAnnihilator ⊓ W.1.dualAnnihilator : Submodule K (Module.Dual K V)) +
        a + b - finrank K V := by
  have h := finrank_dualAnnihilator_inf U.1 W.1
  rw [U.2, W.2] at h
  omega

/-- **Annihilators** (used for `a, b > n/2`): the kernel `κ` from `Gr(V, a)` to `Gr(V, b)` is
the kernel `κ'(s) = κ(s + a + b - n)` from `Gr(V*, n - a)` to `Gr(V*, n - b)`, conjugated by
`U ↦ U°`. -/
theorem rectKernel_dual (a b : ℕ) (ha : a ≤ finrank K V) (hb : b ≤ finrank K V) (κ : ℕ → R)
    (f : Grass K V a → R) (W : Grass K V b) :
    rectKernel a b κ f W =
      rectKernel (finrank K V - a) (finrank K V - b) (fun s => κ (s + a + b - finrank K V))
        (fun U => f ((grassDualEquiv a ha).symm U)) (grassDualEquiv b hb W) := by
  unfold rectKernel
  refine Fintype.sum_equiv (grassDualEquiv a ha) _ _ fun U => ?_
  dsimp only
  rw [Equiv.symm_apply_apply, grassDualEquiv_apply_coe, grassDualEquiv_apply_coe,
    ← finrank_inf_eq_dualAnnihilator a b U W]

/-- A kernel from an empty Grassmannian is zero. -/
theorem rectKernel_eq_zero_of_lt (a b : ℕ) (ha : finrank K V < a) (κ : ℕ → R)
    (f : Grass K V a → R) (W : Grass K V b) : rectKernel a b κ f W = 0 := by
  have : IsEmpty (Grass K V a) :=
    ⟨fun U => absurd (U.2 ▸ Submodule.finrank_le U.1 : a ≤ finrank K V) (by omega)⟩
  unfold rectKernel
  exact Fintype.sum_empty _

end Identities

/-! ### The cost: `S poly(n)` work -/

section Cost

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-- One term `I^{t,b} (I^{t,a})ᵀ`, `t ≤ min(a, b) ≤ n/2`: two incidence transforms (Theorem 2)
on tables of size at most `2S`, so `4 C S L` gates with `L = (log₂ q + 4)(n+1)² ≥ log₂ (2S)`. -/
theorem incid_incidT_linCost {C : ℕ}
    (hinc : ∀ a b : ℕ, a ≤ b → b ≤ finrank K V →
      LinCost (Set.univ : Set R) (incid (K := K) (V := V) a b)
          (C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
            Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) ∧
        LinCost (Set.univ : Set R) (incidT (K := K) (V := V) a b)
          (C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
            Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))))
    {a b t : ℕ} (ha : a ≤ finrank K V) (hb : b ≤ finrank K V) (hab : 2 * min a b ≤ finrank K V)
    (ht : t ≤ min a b) :
    LinCost (Set.univ : Set R) (fun f : Grass K V a → R => incid t b (incidT t a f))
      (4 * C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
        ((Nat.log 2 (Fintype.card K) + 4) * (finrank K V + 1) ^ 2)) := by
  have hta : t ≤ a := ht.trans (min_le_left _ _)
  have htb : t ≤ b := ht.trans (min_le_right _ _)
  have h1 := (hinc t a hta ha).2
  have h2 := (hinc t b htb hb).1
  refine (h1.comp h2).mono ?_
  rw [card_grass rfl t, card_grass rfl a, card_grass rfl b]
  set n := finrank K V
  set L := (Nat.log 2 (Fintype.card K) + 4) * (n + 1) ^ 2
  set S := gr K n a + gr K n b
  have hgt : gr K n t ≤ S := gr_le_add_of_le_min K ht hab
  have hlA := log_gr_add_le K n t a
  have hlB := log_gr_add_le K n t b
  have hA : C * (gr K n t + gr K n a) * Nat.log 2 (gr K n t + gr K n a) ≤ C * (2 * S) * L := by
    gcongr
    omega
  have hB : C * (gr K n t + gr K n b) * Nat.log 2 (gr K n t + gr K n b) ≤ C * (2 * S) * L := by
    gcongr
    omega
  calc C * (gr K n t + gr K n a) * Nat.log 2 (gr K n t + gr K n a) +
        C * (gr K n t + gr K n b) * Nat.log 2 (gr K n t + gr K n b)
      ≤ C * (2 * S) * L + C * (2 * S) * L := add_le_add hA hB
    _ = 4 * C * S * L := by ring

/-- **The case `min(a, b) ≤ n/2`**: `min(a, b) + 1 ≤ n + 1` terms of `incid_incidT_linCost`,
combined with `(min(a, b) + 1) |Gr(n, b)|` gates. -/
theorem rectKernel_linCost_half {C : ℕ}
    (hinc : ∀ a b : ℕ, a ≤ b → b ≤ finrank K V →
      LinCost (Set.univ : Set R) (incid (K := K) (V := V) a b)
          (C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
            Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) ∧
        LinCost (Set.univ : Set R) (incidT (K := K) (V := V) a b)
          (C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
            Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))))
    {a b : ℕ} (ha : a ≤ finrank K V) (hb : b ≤ finrank K V) (hab : 2 * min a b ≤ finrank K V)
    (κ : ℕ → R) :
    LinCost (Set.univ : Set R) (rectKernel (K := K) (V := V) a b κ)
      ((4 * C * (Nat.log 2 (Fintype.card K) + 4) + 1) * (finrank K V + 1) ^ 3 *
        (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) := by
  have hterm : ∀ t : Fin (min a b + 1), LinCost (Set.univ : Set R)
      (fun f : Grass K V a → R => incid t b (incidT t a f))
      (4 * C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
        ((Nat.log 2 (Fintype.card K) + 4) * (finrank K V + 1) ^ 2)) :=
    fun t => incid_incidT_linCost hinc ha hb hab (Nat.lt_succ_iff.mp t.2)
  have hw := LinCost.wsum (fun (t : Fin (min a b + 1)) (f : Grass K V a → R) =>
    incid t b (incidT t a f)) _ hterm (fun t => rectCoeff K κ t)
  refine (hw.congr ?_).mono ?_
  · funext f W
    rw [rectKernel_eq_sum_incid, Fin.sum_univ_eq_sum_range
      (fun t => rectCoeff K κ t * incid t b (incidT t a f) W)]
  · rw [Fintype.card_fin]
    set n := finrank K V
    set e := Nat.log 2 (Fintype.card K)
    set S := Fintype.card (Grass K V a) + Fintype.card (Grass K V b)
    have hm : min a b + 1 ≤ n + 1 := by
      have := min_le_left a b
      omega
    have hgb : Fintype.card (Grass K V b) ≤ S := Nat.le_add_left _ _
    have hn3 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    calc (min a b + 1) * (4 * C * S * ((e + 4) * (n + 1) ^ 2)) +
          Fintype.card (Grass K V b) * (min a b + 1)
        ≤ (n + 1) * (4 * C * S * ((e + 4) * (n + 1) ^ 2)) + S * (n + 1) ^ 3 := by
          gcongr
          exact hm.trans hn3
      _ = (4 * C * (e + 4) + 1) * (n + 1) ^ 3 * S := by ring

end Cost

/-- **Rectangular kernels** (Appendix C, "Different input and output dimensions"): over any
commutative ring in which `p` is invertible, a kernel from `Gr(V, a)` to `Gr(V, b)` depending
only on `dim(U ∩ W)` is applied with `O_q((n + 1)³ S)` operations, `S = |Gr(n, a)| + |Gr(n, b)|`
(`S poly(n)` work). -/
theorem fast_rectKernel (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (a b : ℕ)
        (κ : ℕ → R),
        LinCost (Set.univ : Set R) (rectKernel (K := K) (V := V) a b κ)
          (C * (finrank K V + 1) ^ 3 *
            (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) := by
  obtain ⟨C₁, hC₁⟩ := fast_incidence.{u, v, w} K
  obtain ⟨C₂, hC₂⟩ := fast_incidence.{u, max v w, w} K
  refine ⟨4 * (C₁ + C₂) * (Nat.log 2 (Fintype.card K) + 4) + 1,
    fun R _ hR V _ _ _ a b κ => ?_⟩
  by_cases hbn : b ≤ finrank K V
  swap
  · have : IsEmpty (Grass K V b) :=
      ⟨fun W => hbn (W.2 ▸ Submodule.finrank_le W.1)⟩
    exact LinCost.empty _ _
  by_cases han : a ≤ finrank K V
  swap
  · refine (LinCost.zero.congr ?_).mono (Nat.zero_le _)
    funext f W
    exact (rectKernel_eq_zero_of_lt a b (by omega) κ f W).symm
  by_cases hab : 2 * min a b ≤ finrank K V
  · -- `min(a, b) ≤ n/2`
    refine rectKernel_linCost_half (fun a' b' h1 h2 => ?_) han hbn hab κ
    obtain ⟨h3, h4⟩ := hC₁ R hR V a' b' h1 h2
    exact ⟨h3.mono (by gcongr; omega), h4.mono (by gcongr; omega)⟩
  · -- `a, b > n/2`: annihilators
    set n := finrank K V with hn
    have hnD : finrank K (Module.Dual K V) = n := Subspace.dual_finrank_eq
    have hD := rectKernel_linCost_half (V := Module.Dual K V) (C := C₁ + C₂)
      (fun a' b' h1 h2 => by
        obtain ⟨h3, h4⟩ := hC₂ R hR (Module.Dual K V) a' b' h1 h2
        exact ⟨h3.mono (by gcongr; omega), h4.mono (by gcongr; omega)⟩)
      (a := n - a) (b := n - b) (by omega) (by omega) (by omega)
      (fun s => κ (s + a + b - n))
    have hE := hD.reindex (grassDualEquiv a han).symm (grassDualEquiv b hbn)
    rw [Fintype.card_congr (grassDualEquiv a han).symm,
      Fintype.card_congr (grassDualEquiv b hbn).symm, hnD] at hE
    refine hE.congr ?_
    funext f W
    exact (rectKernel_dual a b han hbn κ f W).symm

/-- **Sums by intersection dimension** (Appendix C): `h_t(W) = ∑_{dim(U ∩ W) = t} f(U)` from
`Gr(V, a)` to `Gr(V, b)` in `O_q((n + 1)³ S)` operations. -/
theorem fast_rectInterSum (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (a b t : ℕ),
        LinCost (Set.univ : Set R) (rectInterSum (K := K) (V := V) a b t)
          (C * (finrank K V + 1) ^ 3 *
            (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) := by
  obtain ⟨C, hC⟩ := fast_rectKernel.{u, v, w} K
  exact ⟨C, fun R _ hR V _ _ _ a b t =>
    (hC R hR V a b _).congr (rectInterSum_eq_rectKernel a b t).symm⟩

/-! ### Unions of dimensions: the table of all subspaces -/

section AllSubspaces

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-- A kernel on the table of all subspaces depending only on `dim U`, `dim W` and `dim(U ∩ W)`:
`(K f)(W) = ∑_U κ(dim U, dim W, dim(U ∩ W)) f(U)`. -/
noncomputable def allKernel (κ : ℕ → ℕ → ℕ → R) (f : Submodule K V → R) (W : Submodule K V) :
    R :=
  ∑ U : Submodule K V, κ (finrank K U) (finrank K W) (finrank K (U ⊓ W : Submodule K V)) * f U

/-- Only the rank part `a = dim U` survives a combination of the rank parts. -/
theorem sum_mul_rankPart (c : ℕ → R) (f : Submodule K V → R) (U : Submodule K V) :
    ∑ a ∈ range (finrank K V + 1), c a * rankPart a f U = c (finrank K U) * f U := by
  rw [sum_eq_single (finrank K U)]
  · simp [rankPart]
  · intro a _ ha
    simp [rankPart, Ne.symm ha]
  · intro h
    exact absurd (mem_range.2 (Nat.lt_succ_of_le (Submodule.finrank_le U))) h

open Classical in
/-- `∑_a c_a (Z_nᵀ f_a)(L) = ∑_{U ⊇ L} c_{dim U} f(U)`, `f_a` the rank-`a` part of `f`. -/
theorem sum_mul_zetaAllT_rankPart (c : ℕ → R) (f : Submodule K V → R) (L : Submodule K V) :
    ∑ a ∈ range (finrank K V + 1), c a * zetaAllT (rankPart a f) L =
      ∑ U ∈ univ.filter (fun U : Submodule K V => L ≤ U), c (finrank K U) * f U := by
  unfold zetaAllT
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun U _ => sum_mul_rankPart c f U

open Classical in
/-- **Unions of dimensions** (Appendix C): one upper transform per input dimension
(`H_a = Z_nᵀ f_a`) and one weighted lower transform per output dimension
(`(K f)(W) = Z_n (G_{dim W})(W)` with `G_b(L) = ∑_a c^{a,b}_{dim L} H_a(L)`, where
`c^{a,b} = rectCoeff K (κ a b)` is the back-substitution of equation (29)). -/
theorem allKernel_eq_zetaAll (κ : ℕ → ℕ → ℕ → R) (f : Submodule K V → R) (W : Submodule K V) :
    allKernel κ f W = zetaAll (fun L : Submodule K V => ∑ a ∈ range (finrank K V + 1),
      rectCoeff K (κ a (finrank K W)) (finrank K L) * zetaAllT (rankPart a f) L) W := by
  have h1 : ∀ L : Submodule K V, ∑ a ∈ range (finrank K V + 1),
      rectCoeff K (κ a (finrank K W)) (finrank K L) * zetaAllT (rankPart a f) L =
      ∑ U ∈ univ.filter (fun U : Submodule K V => L ≤ U),
        rectCoeff K (κ (finrank K U) (finrank K W)) (finrank K L) * f U := fun L =>
    sum_mul_zetaAllT_rankPart (fun a => rectCoeff K (κ a (finrank K W)) (finrank K L)) f L
  unfold zetaAll
  rw [sum_congr rfl fun L _ => h1 L]
  rw [sum_comm' (t' := univ) (s' := fun U => univ.filter fun L : Submodule K V => L ≤ U ⊓ W)]
  · unfold allKernel
    refine sum_congr rfl fun U _ => ?_
    rw [← sum_mul, sum_le_finrank_eq (U ⊓ W)
      (fun t => rectCoeff K (κ (finrank K U) (finrank K W)) t), rectCoeff_spec]
  · intro L U
    simp only [mem_filter, mem_univ, true_and, le_inf_iff]
    tauto

/-- The circuit for `allKernel`: `n + 1` upper transforms (one per input dimension), the
weights (`(n+1)²` gates per subspace), `n + 1` lower transforms (one per output dimension). -/
theorem allKernel_linCost_of {s₁ s₂ : ℕ}
    (hT : LinCost (Set.univ : Set R) (zetaAllT (K := K) (V := V)) s₁)
    (hZ : LinCost (Set.univ : Set R) (zetaAll (K := K) (V := V)) s₂) (κ : ℕ → ℕ → ℕ → R) :
    LinCost (Set.univ : Set R) (allKernel (K := K) (V := V) κ)
      ((finrank K V + 1) * s₁ +
        Fintype.card (Submodule K V) * ((finrank K V + 1) * (finrank K V + 1)) +
        (finrank K V + 1) * s₂) := by
  classical
  set n := finrank K V with hn
  -- Stage A: the upper transforms `H_a = Z_nᵀ f_a` of the rank parts
  have hA1 : ∀ a : Fin (n + 1), LinCost (Set.univ : Set R)
      (fun f : Submodule K V → R => zetaAllT (rankPart a f)) s₁ :=
    fun a => ((rankPart_linCost (K := K) (V := V) (R := R) a).comp hT).mono (by omega)
  have hA := (LinCost.sigma (C := (Set.univ : Set R)) (ι := Fin (n + 1))
    (I' := fun _ => Submodule K V) (O' := fun _ => Submodule K V)
    (fun a f => zetaAllT (rankPart a f)) (fun _ => s₁) hA1).reindex
    (I' := Submodule K V) (O' := Fin (n + 1) × Submodule K V) Sigma.snd (fun p => ⟨p.1, p.2⟩)
  -- Stage B: the weighted tables `G_b(L) = ∑_a c^{a,b}_{dim L} H_a(L)`
  have hB1 : ∀ L : Submodule K V, LinCost (Set.univ : Set R)
      (fun (h : Fin (n + 1) → R) (b : Fin (n + 1)) =>
        ∑ a : Fin (n + 1), rectCoeff K (κ a b) (finrank K L) * h a) ((n + 1) * (n + 1)) := by
    intro L
    have := LinCost.dense (C := (Set.univ : Set R))
      (fun (b a : Fin (n + 1)) => rectCoeff K (κ a b) (finrank K L))
      (fun _ _ => trivial) trivial trivial
    simpa only [Fintype.card_fin] using this
  have hB := (LinCost.sigma (C := (Set.univ : Set R)) (ι := Submodule K V)
    (I' := fun _ => Fin (n + 1)) (O' := fun _ => Fin (n + 1))
    (fun (L : Submodule K V) (h : Fin (n + 1) → R) (b : Fin (n + 1)) =>
      ∑ a : Fin (n + 1), rectCoeff K (κ a b) (finrank K L) * h a)
    (fun _ => (n + 1) * (n + 1)) hB1).reindex
    (I' := Fin (n + 1) × Submodule K V) (O' := Fin (n + 1) × Submodule K V)
    (fun p => (p.2, p.1)) (fun p => ⟨p.2, p.1⟩)
  -- Stage C: the lower transforms `Z_n G_b`, read at `b = dim W`
  have hC := (LinCost.sigma (C := (Set.univ : Set R)) (ι := Fin (n + 1))
    (I' := fun _ => Submodule K V) (O' := fun _ => Submodule K V)
    (fun _ => zetaAll) (fun _ => s₂) (fun _ => hZ)).reindex
    (I' := Fin (n + 1) × Submodule K V) (O' := Submodule K V)
    (fun q => (q.1, q.2))
    (fun W => ⟨⟨finrank K W, Nat.lt_succ_of_le (Submodule.finrank_le W)⟩, W⟩)
  refine (((hA.comp hB).comp hC).congr ?_).mono (le_of_eq ?_)
  · funext f W
    rw [allKernel_eq_zetaAll]
    congr 1
    funext L
    exact Fin.sum_univ_eq_sum_range
      (fun a => rectCoeff K (κ a (finrank K W)) (finrank K L) * zetaAllT (rankPart a f) L) _
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- The operation count of `allKernel_linCost_of` is `O((n+1)³ N)`. -/
theorem allKernel_bound (C n N : ℕ) :
    (n + 1) * (C * n * n * N) + N * ((n + 1) * (n + 1)) + (n + 1) * (C * n * n * N) ≤
      (2 * C + 1) * (n + 1) ^ 3 * N := by
  have : (2 * C + 1) * (n + 1) ^ 3 * N =
      ((n + 1) * (C * n * n * N) + N * ((n + 1) * (n + 1)) + (n + 1) * (C * n * n * N)) +
      (N * C * (n + 1) * 2 * (2 * n + 1) + N * (n + 1) * (n + 1) * n) := by ring
  rw [this]
  exact Nat.le_add_right _ _

end AllSubspaces

/-- **Unions of dimensions** (Appendix C, last sentence of "Different input and output
dimensions"): on the table of all subspaces, a kernel depending only on `dim U`, `dim W` and
`dim(U ∩ W)` is applied with `O_q((n + 1)³ N_q(n))` operations over any commutative ring in which
`p` is invertible: one upper transform per input dimension and one weighted lower transform per
output dimension (Theorem 1 for `k = n`). -/
theorem fast_allKernel (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
        (κ : ℕ → ℕ → ℕ → R),
        LinCost (Set.univ : Set R) (allKernel (K := K) (V := V) κ)
          (C * (finrank K V + 1) ^ 3 * Fintype.card (Submodule K V)) := by
  obtain ⟨C, hC⟩ := fast_subspace_summation.{u, v, w} K
  refine ⟨2 * C + 1, fun R _ hR V _ _ _ κ => ?_⟩
  have h := hC R hR V (finrank K V) le_rfl
  rw [card_subLE_top] at h
  have hZ := (h.1.reindex Subtype.val subLETopEquiv.symm).congr
    (funext fun f => funext fun W => (zetaAll_eq_zeta f W).symm)
  have hT := (h.2.2.1.reindex Subtype.val subLETopEquiv.symm).congr
    (funext fun f => funext fun W => (zetaAllT_eq_zetaT f W).symm)
  exact (allKernel_linCost_of hT hZ κ).mono (allKernel_bound C _ _)

end SubspaceConvolution
