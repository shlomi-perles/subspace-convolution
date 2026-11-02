/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Crossing

/-!
# Auxiliary lemmas for Fourier transforms on quotients

Linear algebra over the finite field `K` and character sums for `FourierData`, used in
`Transform/Fourier.lean`.  Everything lives in the namespace `SubspaceConvolution.FourierAux`.

* `card_eq_pow_finrank_fd` — a `K`-space of dimension `e` has `q^e` elements.
* `freqDualEquiv B` — functionals vanishing on `B` are the functionals on `W ⧸ B`.
* `sum_psi_linear_eq_zero` — a character sum along a nonzero functional vanishes
  (proved by averaging over translates, so it holds over any coefficient ring).
* `sum_psi_apply_dual`, `sum_dual_psi_apply`, `sum_freq_liftQ` — the orthogonality relations on a
  finite-dimensional space, its dual, and the frequencies vanishing on `B`.
* `subIn`, `subOut` — subspaces of `W` inside `C` versus subspaces of `C`.
* `cosetLE_iff_factor`, `sum_ite_cosetLE` — a `B`-coset lies in exactly one `D`-coset.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.FourierAux

variable {K : Type*} [Field K] [Fintype K]
variable {S : Type*} [CommRing S]

section Counting

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A `K`-space of dimension `e` has `q^e` elements (for any `Fintype` instance). -/
theorem card_eq_pow_finrank_fd [Fintype V] :
    Fintype.card V = Fintype.card K ^ finrank K V := by
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K)]

/-- The dual space has `q^e` elements (for any `Fintype` instance). -/
theorem card_dual_fd [Fintype (Module.Dual K V)] :
    Fintype.card (Module.Dual K V) = Fintype.card K ^ finrank K V := by
  rw [card_eq_pow_finrank_fd (K := K), Subspace.dual_finrank_eq]

end Counting

section Freq

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Functionals vanishing on `B` are the functionals on `W ⧸ B`. -/
noncomputable def freqDualEquiv (B : Submodule K W) :
    {ξ : Module.Dual K W // B ≤ LinearMap.ker ξ} ≃ Module.Dual K (W ⧸ B) where
  toFun ξ := B.liftQ ξ.1 ξ.2
  invFun φ := ⟨φ ∘ₗ B.mkQ, fun w hw => by
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).2 hw]⟩
  left_inv ξ := by
    apply Subtype.ext
    exact Submodule.liftQ_mkQ B ξ.1 ξ.2
  right_inv φ := by
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ B _ _

@[simp] theorem freqDualEquiv_apply (B : Submodule K W)
    (ξ : {ξ : Module.Dual K W // B ≤ LinearMap.ker ξ}) :
    freqDualEquiv B ξ = B.liftQ ξ.1 ξ.2 := rfl

@[simp] theorem freqDualEquiv_symm_apply_coe (B : Submodule K W) (φ : Module.Dual K (W ⧸ B)) :
    ((freqDualEquiv B).symm φ).1 = φ ∘ₗ B.mkQ := rfl

end Freq

/-- A character sum along a nonzero linear functional vanishes.  The proof averages over the
translates `m + t m₀` and uses that `q` is invertible, so it works over any coefficient ring
(which may have zero divisors). -/
theorem sum_psi_linear_eq_zero (F : FourierData K S) {M : Type*} [AddCommGroup M] [Module K M]
    [Fintype M] (L : M →ₗ[K] K) {m₀ : M} (h : L m₀ ≠ 0) : ∑ m, F.ψ (L m) = 0 := by
  have hshift : ∀ t : K, ∑ m, F.ψ (L (m + t • m₀)) = ∑ m, F.ψ (L m) := fun t =>
    Fintype.sum_equiv (Equiv.addRight (t • m₀)) _ _ (fun m => rfl)
  have key : (Fintype.card K : S) * ∑ m, F.ψ (L m) = 0 := by
    calc (Fintype.card K : S) * ∑ m, F.ψ (L m)
        = ∑ t : K, ∑ m, F.ψ (L (m + t • m₀)) := by
          simp only [hshift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ m, F.ψ (L m) * ∑ t : K, F.ψ (L m₀ * t) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_add, map_smul, smul_eq_mul, AddChar.map_add_eq_mul, mul_comm t]
      _ = 0 := by simp only [F.sum_mul_eq_zero _ h, mul_zero, Finset.sum_const_zero]
  calc ∑ m, F.ψ (L m) = F.qinv * ((Fintype.card K : S) * ∑ m, F.ψ (L m)) := by
        rw [← mul_assoc, F.qinv_mul, one_mul]
    _ = 0 := by rw [key, mul_zero]

section Orthogonality

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Classical in
/-- Orthogonality on `V`: `∑_x ψ(φ x) = q^{dim V} [φ = 0]`. -/
theorem sum_psi_apply_dual (F : FourierData K S) [Fintype V] (φ : Module.Dual K V) :
    ∑ x : V, F.ψ (φ x) = if φ = 0 then (Fintype.card K : S) ^ finrank K V else 0 := by
  split_ifs with hφ
  · subst hφ
    simp only [LinearMap.zero_apply, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, card_eq_pow_finrank_fd (K := K) (V := V),
      Nat.cast_pow]
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ x₀ ≠ 0 := by
      by_contra! hc
      exact hφ (LinearMap.ext hc)
    exact sum_psi_linear_eq_zero F φ hx₀

open Classical in
/-- Orthogonality on the dual: `∑_φ ψ(φ v) = q^{dim V} [v = 0]`. -/
theorem sum_dual_psi_apply (F : FourierData K S) [Fintype (Module.Dual K V)] (v : V) :
    ∑ φ : Module.Dual K V, F.ψ (φ v) =
      if v = 0 then (Fintype.card K : S) ^ finrank K V else 0 := by
  split_ifs with hv
  · subst hv
    simp only [map_zero, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, card_dual_fd (K := K) (V := V), Nat.cast_pow]
  · obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_ne_zero K hv
    exact sum_psi_linear_eq_zero F (Module.Dual.eval K V v) hφ₀

open Classical in
/-- Orthogonality on the frequencies vanishing on `B`, evaluated at a coset `u`. -/
theorem sum_freq_liftQ (F : FourierData K S) {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (B : Submodule K W)
    [Fintype {ξ : Module.Dual K W // B ≤ LinearMap.ker ξ}] (u : W ⧸ B) :
    ∑ ξ : {ξ : Module.Dual K W // B ≤ LinearMap.ker ξ}, F.ψ (B.liftQ ξ.1 ξ.2 u) =
      if u = 0 then (Fintype.card K : S) ^ finrank K (W ⧸ B) else 0 := by
  rw [← sum_dual_psi_apply F u]
  exact Fintype.sum_equiv (freqDualEquiv B) _ _ (fun ξ => rfl)

end Orthogonality

section Coordinates

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A functional in coordinates: `φ (∑ᵢ xᵢ bᵢ) = ∑ᵢ φ(bᵢ) xᵢ`. -/
theorem dual_apply_equivFun_symm {ι : Type*} [Fintype ι] (b : Module.Basis ι K V)
    (φ : Module.Dual K V) (x : ι → K) :
    φ (b.equivFun.symm x) = ∑ i, (b.constr K).symm φ i * x i := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul,
    Module.Basis.constr_symm_apply, mul_comm]

/-- For `B ≤ C`, `B` regarded as a subspace of `C` has the same dimension. -/
theorem finrank_comap_subtype_of_le {B C : Submodule K V} (h : B ≤ C) :
    finrank K (B.comap C.subtype) = finrank K B :=
  (Submodule.comapSubtypeEquivOfLe h).finrank_eq

end Coordinates

section SubIn

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- A subspace `B ≤ C` of `W`, regarded as a subspace of `C`. -/
def subIn {P : ℕ → Prop} (B : SubP K W P) (C : Submodule K W) (hB : B.1 ≤ C) : SubP K C P :=
  ⟨B.1.comap C.subtype, by rw [finrank_comap_subtype_of_le hB]; exact B.2⟩

/-- A subspace of `C`, regarded as a subspace of `W`. -/
def subOut {P : ℕ → Prop} {C : Submodule K W} (U : SubP K C P) : SubP K W P :=
  ⟨U.1.map C.subtype, by rw [Submodule.finrank_map_subtype_eq]; exact U.2⟩

@[simp] theorem subIn_coe {P : ℕ → Prop} (B : SubP K W P) (C : Submodule K W) (hB : B.1 ≤ C) :
    (subIn B C hB).1 = B.1.comap C.subtype := rfl

@[simp] theorem subOut_coe {P : ℕ → Prop} {C : Submodule K W} (U : SubP K C P) :
    (subOut U).1 = U.1.map C.subtype := rfl

theorem subOut_le {P : ℕ → Prop} {C : Submodule K W} (U : SubP K C P) : (subOut U).1 ≤ C :=
  Submodule.map_subtype_le _ _

theorem subOut_subIn {P : ℕ → Prop} (B : SubP K W P) {C : Submodule K W} (hB : B.1 ≤ C) :
    subOut (subIn B C hB) = B := by
  apply Subtype.ext
  rw [subOut_coe, subIn_coe, Submodule.map_comap_subtype, inf_eq_right.2 hB]

theorem subIn_subOut {P : ℕ → Prop} {C : Submodule K W} (U : SubP K C P) :
    subIn (subOut U) C (subOut_le U) = U := by
  apply Subtype.ext
  exact Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _) U.1

theorem subIn_le_subIn_iff {P Q : ℕ → Prop} {B : SubP K W P} {D : SubP K W Q}
    {C : Submodule K W} (hB : B.1 ≤ C) (hD : D.1 ≤ C) :
    (subIn B C hB).1 ≤ (subIn D C hD).1 ↔ B.1 ≤ D.1 := by
  constructor
  · intro h
    have h' := Submodule.map_mono (f := C.subtype) h
    rwa [subIn_coe, subIn_coe, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
      inf_eq_right.2 hB, inf_eq_right.2 hD] at h'
  · intro h
    exact Submodule.comap_mono h

theorem subOut_le_iff {P : ℕ → Prop} {C : Submodule K W} (U : SubP K C P) (D : Submodule K W) :
    (subOut U).1 ≤ D ↔ U.1 ≤ D.comap C.subtype :=
  Submodule.map_le_iff_le_comap

end SubIn

section Coset

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- For `B ≤ D`, the `B`-coset `y` lies in the `D`-coset `x` iff `x` is the image of `y`. -/
theorem cosetLE_iff_factor {B D : Submodule K W} (hBD : B ≤ D) (y : W ⧸ B) (x : W ⧸ D) :
    cosetLE B D y x ↔ x = Submodule.factor hBD y := by
  constructor
  · rintro ⟨-, w, rfl, rfl⟩
    rfl
  · rintro rfl
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective B y
    exact ⟨hBD, w, rfl, rfl⟩

theorem not_cosetLE {B D : Submodule K W} (hBD : ¬ B ≤ D) (y : W ⧸ B) (x : W ⧸ D) :
    ¬ cosetLE B D y x := fun h => hBD h.1

open Classical in
/-- Every `B`-coset lies in exactly one `D`-coset (for `B ≤ D`). -/
theorem sum_ite_cosetLE [FiniteDimensional K W] {B D : Submodule K W} (hBD : B ≤ D) (y : W ⧸ B)
    (g : W ⧸ D → S) :
    ∑ x : W ⧸ D, (if cosetLE B D y x then g x else 0) = g (Submodule.factor hBD y) := by
  simp only [cosetLE_iff_factor hBD, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A functional vanishing on `D` takes the same value on a `B`-coset and on the `D`-coset
containing it. -/
theorem liftQ_factor {B D : Submodule K W} (hBD : B ≤ D) (ξ : Module.Dual K W)
    (hD : D ≤ LinearMap.ker ξ) (y : W ⧸ B) :
    D.liftQ ξ hD (Submodule.factor hBD y) = B.liftQ ξ (hBD.trans hD) y := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective B y
  rfl

end Coset

/-- A sum over a type equals the sum over a subtype when the summand vanishes off it. -/
theorem sum_eq_sum_subtype_of_zero {α M : Type*} [Fintype α] [AddCommMonoid M] (p : α → Prop)
    [Fintype {x // p x}] (f : α → M) (hf : ∀ a, ¬ p a → f a = 0) :
    ∑ a, f a = ∑ a : {x // p x}, f a.1 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rfl
  · exact hf a ha

end SubspaceConvolution.FourierAux
