/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Applications

/-!
# Auxiliary lemmas for rectangular kernels (Appendix C)

Helpers for `SubspaceConvolution/Transform/Rectangular.lean` ("Different input and output
dimensions").

* `rectCoeff`, `rectCoeff_spec`, `sum_gr_rectCoeff` — back-substitution in equation (29):
  coefficients `c_t` with `∑_{t ≤ d} |Gr(d, t)| c_t = κ(d)` for every `d`.
* `card_filter_le_finrank_eq`, `sum_le_finrank_eq` — the subspaces of `S`, grouped by dimension:
  `∑_{L ≤ S} g(dim L) = ∑_t |Gr(dim S, t)| g(t)`.
* `gr_le_add_of_le_min` — for `min(a, b) ≤ n/2`, every intermediate table `Gr(n, t)`,
  `t ≤ min(a, b)`, is no larger than `|Gr(n, a)| + |Gr(n, b)|`.
* `log_gr_add_le` — `log₂(|Gr(n, i)| + |Gr(n, j)|) ≤ (log₂ q + 4)(n + 1)²`.
* `LinCost.wsum` — a fixed linear combination `∑_i c_i M_i f` of a family of maps.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

/-! ### Back-substitution in equation (29) -/

section Coeff

variable (K : Type w) [Field K] [Fintype K]
variable {R : Type u} [CommRing R]

/-- Back-substitution in equation (29): `c_t = κ(t) - ∑_{j<t} |Gr(t,j)| c_j`. -/
noncomputable def rectCoeff (κ : ℕ → R) (t : ℕ) : R :=
  κ t - ∑ j : Fin t, (gr K t j : R) * rectCoeff κ j
termination_by t
decreasing_by exact j.2

/-- The defining recursion of `rectCoeff`, as a sum over `range t`. -/
theorem rectCoeff_eq (κ : ℕ → R) (t : ℕ) :
    rectCoeff K κ t = κ t - ∑ j ∈ range t, (gr K t j : R) * rectCoeff K κ j := by
  rw [rectCoeff, Fin.sum_univ_eq_sum_range (fun j => (gr K t j : R) * rectCoeff K κ j)]

/-- `∑_{j ≤ t} |Gr(t, j)| c_j = κ(t)`. -/
theorem rectCoeff_spec (κ : ℕ → R) (t : ℕ) :
    ∑ j ∈ range (t + 1), (gr K t j : R) * rectCoeff K κ j = κ t := by
  rw [sum_range_succ, gr_self, Nat.cast_one, one_mul, rectCoeff_eq K κ t]
  ring

/-- The same over any longer range: `∑_{j ≤ m} |Gr(d, j)| c_j = κ(d)` for `d ≤ m`. -/
theorem sum_gr_rectCoeff (κ : ℕ → R) {d m : ℕ} (h : d ≤ m) :
    ∑ j ∈ range (m + 1), (gr K d j : R) * rectCoeff K κ j = κ d := by
  rw [← rectCoeff_spec K κ d]
  symm
  refine sum_subset (range_subset_range.2 (by omega)) fun j _ hj => ?_
  rw [gr_eq_zero_of_lt K (by simpa using hj), Nat.cast_zero, zero_mul]

end Coeff

/-! ### Subspaces of a subspace, grouped by dimension -/

section Inside

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

open Classical in
/-- The `t`-dimensional subspaces inside `S`: there are `|Gr(dim S, t)|` of them. -/
theorem card_filter_le_finrank_eq (S : Submodule K V) (t : ℕ) :
    #((univ.filter fun L : Submodule K V => L ≤ S).filter
        fun L : Submodule K V => finrank K L = t) = gr K (finrank K S) t := by
  rw [← card_grass_inside S t]
  refine card_bij' (fun L hL => (⟨L, (mem_filter.1 hL).2⟩ : Grass K V t)) (fun L _ => L.1)
    ?_ ?_ ?_ ?_
  · intro L hL
    simp only [mem_filter, mem_univ, true_and] at hL ⊢
    exact hL.1
  · intro L hL
    simp only [mem_filter, mem_univ, true_and] at hL ⊢
    exact ⟨hL, L.2⟩
  · intro L hL
    rfl
  · intro L hL
    rfl

open Classical in
/-- Grouping the subspaces of `S` by dimension: `∑_{L ≤ S} g(dim L) = ∑_t |Gr(dim S, t)| g(t)`. -/
theorem sum_le_finrank_eq (S : Submodule K V) (g : ℕ → R) :
    ∑ L ∈ univ.filter (fun L : Submodule K V => L ≤ S), g (finrank K L) =
      ∑ t ∈ range (finrank K S + 1), (gr K (finrank K S) t : R) * g t := by
  rw [← sum_fiberwise_of_maps_to' (t := range (finrank K S + 1))
    (g := fun L : Submodule K V => finrank K L)
    (fun L hL => mem_range.2 (Nat.lt_succ_of_le (Submodule.finrank_mono (mem_filter.1 hL).2)))]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_const, card_filter_le_finrank_eq, nsmul_eq_mul]

end Inside

/-! ### Sizes of the intermediate tables -/

section Sizes

variable (K : Type w) [Field K] [Fintype K]

/-- For `min(a, b) ≤ n/2`, every intermediate table `Gr(n, t)`, `t ≤ min(a, b)`, is no larger
than `|Gr(n, min(a, b))| ≤ |Gr(n, a)| + |Gr(n, b)|` (unimodality). -/
theorem gr_le_add_of_le_min {n a b t : ℕ} (ht : t ≤ min a b) (hab : 2 * min a b ≤ n) :
    gr K n t ≤ gr K n a + gr K n b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h] at ht hab
    exact (CountAux.gr_le_gr K ht (by omega)).trans (Nat.le_add_right _ _)
  · rw [min_eq_right h] at ht hab
    exact (CountAux.gr_le_gr K ht (by omega)).trans (Nat.le_add_left _ _)

/-- `|Gr(n, j)| ≤ 4 q^{n²}`. -/
theorem gr_le_four_mul_pow_sq (n j : ℕ) : gr K n j ≤ 4 * Fintype.card K ^ (n * n) := by
  have hq : 0 < Fintype.card K := Fintype.card_pos
  refine (gr_le K n j).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq ?_))
  rcases le_total j n with h | h
  · exact Nat.mul_le_mul h (Nat.sub_le _ _)
  · rw [Nat.sub_eq_zero_of_le h, mul_zero]
    exact Nat.zero_le _

/-- `log₂(|Gr(n, i)| + |Gr(n, j)|) ≤ (log₂ q + 4)(n + 1)²`: the logarithmic factor of
Theorem 2 is `O_q(n²)`. -/
theorem log_gr_add_le (n i j : ℕ) :
    Nat.log 2 (gr K n i + gr K n j) ≤ (Nat.log 2 (Fintype.card K) + 4) * (n + 1) ^ 2 := by
  set e := Nat.log 2 (Fintype.card K)
  have hq : Fintype.card K ≤ 2 ^ (e + 1) := (Nat.lt_pow_succ_log_self one_lt_two _).le
  have h1 : gr K n i + gr K n j ≤ 2 ^ (3 + (e + 1) * (n * n)) := by
    calc gr K n i + gr K n j
        ≤ 4 * Fintype.card K ^ (n * n) + 4 * Fintype.card K ^ (n * n) :=
          add_le_add (gr_le_four_mul_pow_sq K n i) (gr_le_four_mul_pow_sq K n j)
      _ = 2 ^ 3 * Fintype.card K ^ (n * n) := by ring
      _ ≤ 2 ^ 3 * (2 ^ (e + 1)) ^ (n * n) := by gcongr
      _ = 2 ^ (3 + (e + 1) * (n * n)) := by rw [← pow_mul, ← pow_add]
  calc Nat.log 2 (gr K n i + gr K n j) ≤ Nat.log 2 (2 ^ (3 + (e + 1) * (n * n))) :=
        Nat.log_mono_right h1
    _ = 3 + (e + 1) * (n * n) := Nat.log_pow one_lt_two _
    _ ≤ (e + 4) * (n + 1) ^ 2 := by nlinarith [Nat.zero_le (e * n), Nat.zero_le n]

end Sizes

/-! ### Linear combinations of maps -/

namespace Circuit.LinCost

variable {R : Type u} [CommRing R]

/-- A fixed linear combination `∑_i c_i M_i f` of a family of maps: the maps side by side, then
`|ι|` gates per output. -/
theorem wsum {ι I O : Type*} [Fintype ι] [Fintype O] (M : ι → (I → R) → O → R) (s : ℕ)
    (h : ∀ i, LinCost (Set.univ : Set R) (M i) s) (c : ι → R) :
    LinCost (Set.univ : Set R) (fun f o => ∑ i, c i * M i f o)
      (Fintype.card ι * s + Fintype.card O * Fintype.card ι) := by
  have h1 := (LinCost.sigma (C := (Set.univ : Set R)) (I' := fun _ : ι => I)
    (O' := fun _ : ι => O) M (fun _ => s) h).reindex (I' := I) (O' := ι × O) Sigma.snd
    (fun p => ⟨p.1, p.2⟩)
  have h2 := (LinCost.sigma (C := (Set.univ : Set R)) (ι := O) (I' := fun _ => ι)
    (O' := fun _ => Unit) (fun _ g _ => ∑ i, c i * g i)
    (fun _ => Fintype.card Unit * Fintype.card ι)
    (fun _ => LinCost.dense (C := (Set.univ : Set R)) (fun (_ : Unit) i => c i)
      (fun _ _ => trivial) trivial trivial)).reindex
    (I' := ι × O) (O' := O) (fun p => (p.2, p.1)) (fun o => ⟨o, ()⟩)
  refine ((h1.comp h2).congr ?_).mono (le_of_eq ?_)
  · rfl
  · simp [sum_const, card_univ, smul_eq_mul]

end Circuit.LinCost

end SubspaceConvolution
