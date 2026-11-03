/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Step
import SubspaceConvolution.Transform.Count

/-!
# The fast incidence transform: Theorem 2

* `incid_linCost` — the recursion of Section 4 (equation (12), two inside calls) with the
  budget `incidBound` of Appendix B, over a ring with a Fourier character.
* `fast_incidence` — **Theorem 2** over any commutative ring in which `p` is invertible, for
  `I^{a,b}` and its transpose.
* `fast_incidence_complex` — over `ℂ` the algorithm uses only constants of modulus at most one
  (the upper bound of Theorem 7).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

/-! ### Boundary cases of the recursion -/

section Boundary

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type*} [CommRing R]

/-- The zero subspace, as the unique point of `Gr(V, 0)`. -/
def grassBot : Grass K V 0 := ⟨⊥, finrank_bot K V⟩

theorem grass_zero_eq (U : Grass K V 0) : U.1 = ⊥ := Submodule.finrank_eq_zero.1 U.2

theorem grass_top_eq {n : ℕ} (hn : finrank K V = n) (W : Grass K V n) : W.1 = ⊤ :=
  Submodule.eq_top_of_finrank_eq (W.2.trans hn.symm)

/-- `I^{a,a}` is the identity. -/
theorem incid_self (a : ℕ) : (incid (K := K) (V := V) (R := R) a a) = fun f => f := by
  classical
  funext f W
  unfold incid
  rw [Finset.sum_eq_single W]
  · intro U hU hne
    exfalso
    apply hne
    have hle : U.1 ≤ W.1 := (Finset.mem_filter.1 hU).2
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (U.2.trans W.2.symm))
  · intro h
    exfalso
    exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩)

/-- `I^{0,b}` copies `f(0)` to every output. -/
theorem incid_zero_left (b : ℕ) :
    (incid (K := K) (V := V) (R := R) 0 b) = fun f _ => f grassBot := by
  classical
  funext f W
  unfold incid
  rw [Finset.sum_eq_single grassBot]
  · intro U _ hne
    exfalso
    exact hne (Subtype.ext (grass_zero_eq U))
  · intro h
    exfalso
    refine h (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    show (⊥ : Submodule K V) ≤ W.1
    exact bot_le

/-- `I^{a,n}` sums all inputs. -/
theorem incid_top_right {n : ℕ} (hn : finrank K V = n) (a : ℕ) :
    (incid (K := K) (V := V) (R := R) a n) = fun f _ => ∑ U, f U := by
  classical
  funext f W
  unfold incid
  rw [Finset.filter_true_of_mem]
  intro U _
  rw [grass_top_eq hn W]
  exact le_top

theorem card_grass_top_le {n : ℕ} (hn : finrank K V = n) : Fintype.card (Grass K V n) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro W W'
  exact Subtype.ext ((grass_top_eq hn W).trans (grass_top_eq hn W').symm)

variable {C : Set R}

theorem linCost_incid_self (a : ℕ) : LinCost C (incid (K := K) (V := V) (R := R) a a) 0 :=
  LinCost.id.congr (incid_self a).symm

theorem linCost_incid_zero_left (b : ℕ) :
    LinCost C (incid (K := K) (V := V) (R := R) 0 b) 0 := by
  have h := (LinCost.id (C := C) (I := Grass K V 0)).reindex id
    (fun _ : Grass K V b => grassBot)
  refine h.congr ?_
  rw [incid_zero_left]
  rfl

theorem linCost_incid_top_right (h0 : (0 : R) ∈ C) (h1 : (1 : R) ∈ C) {n : ℕ}
    (hn : finrank K V = n) (a : ℕ) :
    LinCost C (incid (K := K) (V := V) (R := R) a n) (Fintype.card (Grass K V a)) := by
  have h := LinCost.dense (C := C) (fun (_ : Grass K V n) (_ : Grass K V a) => (1 : R))
    (fun _ _ => h1) h0 h1
  refine (h.congr ?_).mono ?_
  · rw [incid_top_right hn]
    funext f o
    simp only [one_mul]
  · calc Fintype.card (Grass K V n) * Fintype.card (Grass K V a)
        ≤ 1 * Fintype.card (Grass K V a) := Nat.mul_le_mul_right _ (card_grass_top_le hn)
      _ = Fintype.card (Grass K V a) := one_mul _

end Boundary

/-! ### Counting the pieces of one recursion step -/

section Pieces

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The crossing part of `Gr(V, a)` has `∑_{B ∈ Gr(H, a-1)} |H/B| ≤ |Gr(V, a)|` elements. -/
theorem sum_card_quot_le (D : HypData K V) {a : ℕ} (ha : 0 < a) :
    ∑ B : SubP K D.H (· = a - 1), Fintype.card (D.H ⧸ B.1) ≤ Fintype.card (Grass K V a) := by
  have hP : ∀ d, (fun x => x = a) (d + 1) ↔ (fun x => x = a - 1) d := fun d => by
    simp only; omega
  rw [Fintype.card_congr (D.split (· = a) (· = a - 1) hP), Fintype.card_sum, Fintype.card_sigma]
  exact Nat.le_add_left _ _

/-- The local work of the interior step is at most `(2q+1) n S`. -/
theorem stepWork_incid_le (D : HypData K V) {n a b : ℕ} (hn : finrank K V = n) (ha : 0 < a)
    (hab : a < b) :
    stepWork K (finrank K V) (H := D.H) (· = a - 1) (· = b - 1) ≤
      (2 * Fintype.card K + 1) * n * (gr K n a + gr K n b) := by
  unfold stepWork
  rw [hn, ← card_grass hn a, ← card_grass hn b]
  exact Nat.mul_le_mul_left _ (add_le_add (by convert sum_card_quot_le D ha)
    (by convert sum_card_quot_le D (show 0 < b by omega)))

theorem finrank_ker_le (ξ : Module.Dual K V) : finrank K (LinearMap.ker ξ) ≤ finrank K V :=
  Submodule.finrank_le _

theorem le_finrank_ker (ξ : Module.Dual K V) :
    finrank K V ≤ finrank K (LinearMap.ker ξ) + 1 := by
  by_cases hξ : ξ = 0
  · subst hξ
    rw [finrank_ker_zero]
    omega
  · rw [finrank_ker_of_ne hξ]

/-- Summing a function of `dim ker ξ` over all frequencies: `ξ = 0` has a kernel of full
dimension, and the `q^m - 1` nonzero frequencies have hyperplanes as kernels.  (Stated for any
`Fintype` instance on the dual, so that it rewrites whatever instance a sum was elaborated with.) -/
theorem sum_dual_ker {inst : Fintype (Module.Dual K V)} (g : ℕ → ℕ) :
    ∑ ξ : Module.Dual K V, g (finrank K (LinearMap.ker ξ)) =
      g (finrank K V) + (Fintype.card K ^ finrank K V - 1) * g (finrank K V - 1) := by
  classical
  obtain rfl : inst = instFintypeDualFd K V := Subsingleton.elim _ _
  rw [Fintype.sum_eq_add_sum_compl 0, finrank_ker_zero]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => g (finrank K V - 1)), Finset.sum_const, smul_eq_mul,
    Finset.card_compl, card_dual, Finset.card_singleton]
  intro ξ hξ
  have hne : ξ ≠ 0 := by simpa using hξ
  have := finrank_ker_of_ne hne
  congr 1
  omega

end Pieces

/-! ### The recursion of Section 4 -/

section FourierRing

variable {K : Type w} [Field K] [Fintype K] {S : Type*} [CommRing S]

/-- One interior step `0 < a < b < n` of the recursion of Section 4, assuming the bound for all
smaller dimensions. -/
theorem incid_linCost_step (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n a b : ℕ}
    (hn : finrank K V = n) (ha : 0 < a) (hab : a < b) (hbn : b < n)
    (ih : ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W],
      finrank K W < n → ∀ a' b', a' ≤ b' → b' ≤ finrank K W →
        LinCost C (incid (K := K) (V := W) (R := S) a' b')
          (incidBound K (4 * (2 * Fintype.card K + 1) + 4) (finrank K W) a' b')) :
    LinCost C (incid (K := K) (V := V) (R := S) a b)
      (incidBound K (4 * (2 * Fintype.card K + 1) + 4) n a b) := by
  obtain ⟨D⟩ := HypData.nonempty (K := K) (V := V) (by omega)
  have hH : finrank K D.H + 1 = n := hn ▸ D.finrank_H
  have hP : ∀ d, (fun x => x = a) (d + 1) ↔ (fun x => x = a - 1) d := fun d => by
    simp only; omega
  have hQ : ∀ d, (fun x => x = b) (d + 1) ↔ (fun x => x = b - 1) d := fun d => by
    simp only; omega
  have h_in := LinCost.sumElim (ih D.H (by omega) a b hab.le (by omega))
    (ih D.H (by omega) a (b - 1) (by omega) (by omega))
  have h_blk : ∀ ξ : Module.Dual K D.H,
      LinCost C (containT (K := K) (V := LinearMap.ker ξ) (R := S) (· = a - 1) (· = b - 1))
        (incidBound K (4 * (2 * Fintype.card K + 1) + 4) (finrank K (LinearMap.ker ξ))
          (a - 1) (b - 1)) := by
    intro ξ
    have h1 := finrank_ker_le ξ
    have h2 := le_finrank_ker ξ
    exact ih _ (by omega) (a - 1) (b - 1) (by omega) (by omega)
  have hstep := containT_step F hC D (P := (· = a)) (P' := (· = a - 1)) (Q := (· = b))
    (Q' := (· = b - 1)) hP hQ h_in
    (fun ξ => incidBound K (4 * (2 * Fintype.card K + 1) + 4) (finrank K (LinearMap.ker ξ))
      (a - 1) (b - 1)) h_blk
  refine hstep.mono ?_
  rw [sum_dual_ker (fun m => incidBound K (4 * (2 * Fintype.card K + 1) + 4) m (a - 1) (b - 1))]
  have hwork := stepWork_incid_le D hn ha hab
  have hbudget := incid_budget_step K (2 * Fintype.card K + 1) ha hab hbn
  have hm : finrank K D.H = n - 1 := by omega
  have hm' : n - 1 - 1 = n - 2 := by omega
  rw [hm, hm']
  omega

/-- **Section 4 and Appendix B** over a Fourier ring. -/
theorem incid_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (a b : ℕ) (hab : a ≤ b)
    (hbn : b ≤ finrank K V) :
    LinCost C (incid (K := K) (V := V) (R := S) a b)
      (incidBound K (4 * (2 * Fintype.card K + 1) + 4) (finrank K V) a b) := by
  have h0 : (0 : S) ∈ C := hC (Or.inl rfl)
  have h1 : (1 : S) ∈ C := hC (Or.inr (Or.inl rfl))
  suffices H : ∀ n, ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W],
      finrank K W = n → ∀ a b, a ≤ b → b ≤ n →
        LinCost C (incid (K := K) (V := W) (R := S) a b)
          (incidBound K (4 * (2 * Fintype.card K + 1) + 4) n a b) from
    H _ V rfl a b hab hbn
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ _ hn a b hab hbn
  rcases Nat.eq_or_lt_of_le hab with hab' | hab'
  · subst hab'
    exact (linCost_incid_self a).mono (Nat.zero_le _)
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact (linCost_incid_zero_left b).mono (Nat.zero_le _)
  rcases Nat.eq_or_lt_of_le hbn with hbn' | hbn'
  · subst hbn'
    refine (linCost_incid_top_right h0 h1 hn a).mono ?_
    rw [card_grass hn]
    unfold incidBound
    omega
  · exact incid_linCost_step F hC W hn ha hab' hbn'
      (fun W' _ _ _ hW' a' b' h1 h2 => ih _ hW' W' rfl a' b' h1 h2)

end FourierRing

/-! ### Theorem 2 -/

section Ring

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-- Over any commutative ring with `p` invertible: run the recursion over
`R[t]/(1 + t + ⋯ + t^{p-1})` and extract the constant coefficient (Section 3.4). -/
theorem incid_linCost_ring (hR : IsUnit (ringChar K : R)) (a b : ℕ) (hab : a ≤ b)
    (hbn : b ≤ finrank K V) :
    LinCost (Set.univ : Set R) (incid (K := K) (V := V) a b)
      (2 * (ringChar K - 1) ^ 2 *
          incidBound K (4 * (2 * Fintype.card K + 1) + 4) (finrank K V) a b +
        (ringChar K - 1) * Fintype.card (Grass K V a)) := by
  have hp2 : 2 ≤ ringChar K := (CharP.prime_ringChar K).two_le
  have h := incid_linCost (FourierData.ext K R hR) (C := Set.univ) (Set.subset_univ _) V a b
    hab hbn
  have h2 := LinCost.baseChange (ExtRing.basis R (ringChar K) (by omega)) h ⟨0, by omega⟩
  rw [Fintype.card_fin] at h2
  refine h2.congr ?_
  funext f o
  unfold incid
  rw [← map_sum]
  exact ExtRing.basis_repr_algebraMap R (ringChar K) hp2 _

/-- `incidT a b` is the transpose of `incid a b` (for any decidable equality on the inputs). -/
theorem transposeMap_incid (a b : ℕ) [DecidableEq (Grass K V a)] :
    transposeMap (incid (K := K) (V := V) (R := R) a b) = incidT a b := by
  classical
  funext g U
  unfold transposeMap incid incidT
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_pi_single']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_mul, one_mul, zero_mul]

end Ring

/-- **Theorem 2.** `I^{a,b}_n` and its transpose take `O_q(S log S)` arithmetic operations,
`S = |Gr(n,a)| + |Gr(n,b)|`. -/
theorem fast_incidence (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (R : Type u) [CommRing R], IsUnit (ringChar K : R) →
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (a b : ℕ),
        a ≤ b → b ≤ finrank K V →
        LinCost (Set.univ : Set R) (incid (K := K) (V := V) a b)
            (C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
              Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) ∧
          LinCost (Set.univ : Set R) (incidT (K := K) (V := V) a b)
            (C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
              Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) := by
  classical
  set E := 2 * (ringChar K - 1) ^ 2 * (2 * (4 * (2 * Fintype.card K + 1) + 4) + 1) +
    (ringChar K - 1) with hE
  refine ⟨2 * E + 1, fun R _ hR V _ _ _ a b hab hbn => ?_⟩
  have hS : 2 ≤ gr K (finrank K V) a + gr K (finrank K V) b := two_le_gr_add_gr K hab hbn
  have hL : 1 ≤ Nat.log 2 (gr K (finrank K V) a + gr K (finrank K V) b) :=
    Nat.log_pos (by norm_num) hS
  have hB := incidBound_le K (4 * (2 * Fintype.card K + 1) + 4) hab hbn
  have h := incid_linCost_ring (R := R) (V := V) hR a b hab hbn
  rw [card_grass rfl a] at h
  rw [card_grass rfl a, card_grass rfl b]
  set S := gr K (finrank K V) a + gr K (finrank K V) b with hSdef
  set L := Nat.log 2 S with hLdef
  have hA : gr K (finrank K V) a ≤ S * L := by
    calc gr K (finrank K V) a ≤ S := Nat.le_add_right _ _
      _ = S * 1 := (mul_one _).symm
      _ ≤ S * L := Nat.mul_le_mul_left _ hL
  have hBb : gr K (finrank K V) b ≤ S * L := by
    calc gr K (finrank K V) b ≤ S := Nat.le_add_left _ _
      _ = S * 1 := (mul_one _).symm
      _ ≤ S * L := Nat.mul_le_mul_left _ hL
  have hcost : 2 * (ringChar K - 1) ^ 2 *
        incidBound K (4 * (2 * Fintype.card K + 1) + 4) (finrank K V) a b +
      (ringChar K - 1) * gr K (finrank K V) a ≤ E * S * L := by
    calc 2 * (ringChar K - 1) ^ 2 *
          incidBound K (4 * (2 * Fintype.card K + 1) + 4) (finrank K V) a b +
        (ringChar K - 1) * gr K (finrank K V) a
        ≤ 2 * (ringChar K - 1) ^ 2 * ((2 * (4 * (2 * Fintype.card K + 1) + 4) + 1) * S * L) +
          (ringChar K - 1) * (S * L) := by gcongr
      _ = E * S * L := by rw [hE]; ring
  have h' := h.mono hcost
  refine ⟨h'.mono ?_, ?_⟩
  · gcongr
    omega
  · have hT := (h'.transpose (Set.mem_univ 0) (Set.mem_univ 1)).congr (transposeMap_incid a b)
    refine hT.mono ?_
    rw [card_grass rfl b]
    calc 2 * (E * S * L) + gr K (finrank K V) b ≤ 2 * (E * S * L) + S * L := by gcongr
      _ = (2 * E + 1) * S * L := by ring

/-- **Theorem 2 over `ℂ` in the bounded-coefficient model**: the algorithm uses only additions,
roots of unity and Fourier normalizations, all of modulus at most one (Appendix F). -/
theorem fast_incidence_complex (K : Type w) [Field K] [Fintype K] :
    ∃ C : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (a b : ℕ),
        a ≤ b → b ≤ finrank K V →
        LinCost (Metric.closedBall (0 : ℂ) 1) (incid (K := K) (V := V) (R := ℂ) a b)
          (C * (Fintype.card (Grass K V a) + Fintype.card (Grass K V b)) *
            Nat.log 2 (Fintype.card (Grass K V a) + Fintype.card (Grass K V b))) := by
  refine ⟨2 * (4 * (2 * Fintype.card K + 1) + 4) + 1, fun V _ _ _ a b hab hbn => ?_⟩
  rw [card_grass rfl a, card_grass rfl b]
  exact (incid_linCost (FourierData.complex K) (FourierData.complex_consts K) V a b hab
    hbn).mono (incidBound_le K _ hab hbn)

end SubspaceConvolution
