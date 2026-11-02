/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Crossing
import SubspaceConvolution.Circuit.SLP
import SubspaceConvolution.Transform.FourierAux
import SubspaceConvolution.Transform.FourierAuxRing

/-!
# Fourier transforms on quotients (Sections 2.1, 3.2, 3.4)

For `B ≤ W`, frequencies are the functionals vanishing on `B` (`Freq B`, the annihilator `B°`).

* `fourierQ F B` — equation (fft); `fourierQInv F B` — equation (ifft); inversion both ways.
* `sum_freq_psi` — `∑_{λ ∈ B°} ψ(λ(z)) = q^{dim W - dim B} [z ∈ B]`.
* `fourierQ_eq_dft` — after choosing coordinates, `fourierQ` is the `e`-dimensional DFT
  `Circuit.dft` (so it costs `O_q(e |W/B|)` by `Circuit.dft_cost`).
* `fourier_affineT` — **Lemma 3.1** (affine Fourier identity).
* `affineT_eq` — **equation (block)**: `A = F⁻¹ ∘ (⊕_λ Z_{ker λ}) ∘ F`, with the entries regrouped
  by frequency through `freqEquiv`.
* Coefficient rings: `FourierData.complex` (`ψ(t) = exp(2πi Tr(t)/p)`, all circuit constants of
  modulus at most one) and `FourierData.ext` on `ExtRing R p = R[t]/(1 + t + ⋯ + t^{p-1})`
  (Section 3.4), which is free over `R` with a basis whose `0`-th coordinate extracts constants.

Helpers: `freqTo`/`freqFrom` (the two directions of `freqEquiv`, with `freqEquiv_apply`,
`freqEquiv_symm_apply`), `blockT_freqEquiv`, `fourierSig_freqEquiv_symm`, and `sum_le_eq_blockT`
(one block of equation (block)).  General lemmas are in `Transform/FourierAux.lean` and
`Transform/FourierAuxRing.lean` (namespace `SubspaceConvolution.FourierAux`).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {K : Type*} [Field K] [Fintype K]

section Fourier

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {S : Type*} [CommRing S]

/-- Frequencies vanishing on `B`: the annihilator `B°`. -/
abbrev Freq (B : Submodule K W) := {ξ : Module.Dual K W // B ≤ LinearMap.ker ξ}

noncomputable instance instFintypeFreq (B : Submodule K W) : Fintype (Freq B) := Fintype.ofFinite _

/-- Equation (fft): `ĥ_λ(B) = ∑_{x + B} h_B(x + B) ψ(λ(x))`. -/
noncomputable def fourierQ (F : FourierData K S) (B : Submodule K W) (h : W ⧸ B → S)
    (ξ : Freq B) : S :=
  ∑ x : W ⧸ B, h x * F.ψ (B.liftQ ξ.1 ξ.2 x)

/-- Equation (ifft): `h_B(x + B) = q^{-(dim W - dim B)} ∑_{λ ∈ B°} ĥ_λ(B) ψ(-λ(x))`. -/
noncomputable def fourierQInv (F : FourierData K S) (B : Submodule K W) (g : Freq B → S)
    (x : W ⧸ B) : S :=
  F.qinv ^ finrank K (W ⧸ B) * ∑ ξ : Freq B, g ξ * F.ψ (-(B.liftQ ξ.1 ξ.2 x))

theorem card_quotient (B : Submodule K W) :
    Fintype.card (W ⧸ B) = Fintype.card K ^ finrank K (W ⧸ B) :=
  FourierAux.card_eq_pow_finrank_fd

theorem card_freq (B : Submodule K W) : Fintype.card (Freq B) = Fintype.card (W ⧸ B) := by
  rw [Fintype.card_congr (FourierAux.freqDualEquiv B), FourierAux.card_dual_fd, card_quotient]

theorem card_dual : Fintype.card (Module.Dual K W) = Fintype.card K ^ finrank K W :=
  FourierAux.card_dual_fd

theorem finrank_ker_of_ne {ξ : Module.Dual K W} (h : ξ ≠ 0) :
    finrank K (LinearMap.ker ξ) + 1 = finrank K W :=
  Module.Dual.finrank_ker_add_one_of_ne_zero h

theorem finrank_ker_zero : finrank K (LinearMap.ker (0 : Module.Dual K W)) = finrank K W := by
  rw [LinearMap.ker_zero, finrank_top]

open Classical in
/-- Character orthogonality on `B°`. -/
theorem sum_freq_psi (F : FourierData K S) (B : Submodule K W) (z : W) :
    ∑ ξ : Freq B, F.ψ (ξ.1 z) = if z ∈ B then (Fintype.card K : S) ^ finrank K (W ⧸ B) else 0 := by
  have h := FourierAux.sum_freq_liftQ F B (Submodule.Quotient.mk z)
  simp only [Submodule.liftQ_apply] at h
  rw [h]
  by_cases hz : z ∈ B
  · rw [ite_eq_left ((Submodule.Quotient.mk_eq_zero B).2 hz), ite_eq_left hz]
  · rw [ite_eq_right (fun h0 => hz ((Submodule.Quotient.mk_eq_zero B).1 h0)), ite_eq_right hz]

theorem fourierQInv_fourierQ (F : FourierData K S) (B : Submodule K W) (h : W ⧸ B → S) :
    fourierQInv F B (fourierQ F B h) = h := by
  classical
  funext x
  have hsum : ∀ y : W ⧸ B, ∑ ξ : Freq B, F.ψ (B.liftQ ξ.1 ξ.2 (y - x)) =
      if y = x then (Fintype.card K : S) ^ finrank K (W ⧸ B) else 0 := by
    intro y
    rw [FourierAux.sum_freq_liftQ F B (y - x)]
    by_cases hyx : y = x
    · rw [ite_eq_left (sub_eq_zero.2 hyx), ite_eq_left hyx]
    · rw [ite_eq_right (fun h0 => hyx (sub_eq_zero.1 h0)), ite_eq_right hyx]
  calc fourierQInv F B (fourierQ F B h) x
      = F.qinv ^ finrank K (W ⧸ B) *
          ∑ y, h y * ∑ ξ : Freq B, F.ψ (B.liftQ ξ.1 ξ.2 (y - x)) := by
        simp only [fourierQInv, fourierQ]
        congr 1
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ξ _ => ?_
        rw [map_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, mul_assoc]
    _ = F.qinv ^ finrank K (W ⧸ B) * (h x * (Fintype.card K : S) ^ finrank K (W ⧸ B)) := by
        simp only [hsum, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = h x := by
        rw [mul_left_comm, ← mul_pow, F.qinv_mul, one_pow, mul_one]

theorem fourierQ_fourierQInv (F : FourierData K S) (B : Submodule K W) (g : Freq B → S) :
    fourierQ F B (fourierQInv F B g) = g := by
  classical
  funext ξ
  have hsum : ∀ η : Freq B,
      ∑ x : W ⧸ B, F.ψ ((B.liftQ ξ.1 ξ.2 - B.liftQ η.1 η.2) x) =
        if η = ξ then (Fintype.card K : S) ^ finrank K (W ⧸ B) else 0 := by
    intro η
    rw [FourierAux.sum_psi_apply_dual F]
    by_cases hηξ : η = ξ
    · rw [ite_eq_left (by rw [hηξ, sub_self]), ite_eq_left hηξ]
    · rw [ite_eq_right, ite_eq_right hηξ]
      intro h0
      apply hηξ
      apply (FourierAux.freqDualEquiv B).injective
      simp only [FourierAux.freqDualEquiv_apply]
      exact (sub_eq_zero.1 h0).symm
  calc fourierQ F B (fourierQInv F B g) ξ
      = F.qinv ^ finrank K (W ⧸ B) *
          ∑ η, g η * ∑ x : W ⧸ B, F.ψ ((B.liftQ ξ.1 ξ.2 - B.liftQ η.1 η.2) x) := by
        simp only [fourierQInv, fourierQ]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun x _ => ?_
        rw [LinearMap.sub_apply, sub_eq_neg_add, AddChar.map_add_eq_mul]
        ring
    _ = F.qinv ^ finrank K (W ⧸ B) * (g ξ * (Fintype.card K : S) ^ finrank K (W ⧸ B)) := by
        simp only [hsum, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = g ξ := by
        rw [mul_left_comm, ← mul_pow, F.qinv_mul, one_pow, mul_one]

/-- In coordinates, `fourierQ` and `fourierQInv` are the `e`-dimensional DFT and its inverse. -/
theorem fourierQ_eq_dft (F : FourierData K S) (B : Submodule K W) :
    ∃ (σ : (Fin (finrank K (W ⧸ B)) → K) ≃ W ⧸ B) (τ : Freq B ≃ (Fin (finrank K (W ⧸ B)) → K)),
      (∀ h ξ, fourierQ F B h ξ = Circuit.dft F _ (fun x => h (σ x)) (τ ξ)) ∧
      (∀ g x, fourierQInv F B g x = Circuit.idft F _ (fun ξ => g (τ.symm ξ)) (σ.symm x)) := by
  let b := Module.finBasis K (W ⧸ B)
  let σ : (Fin (finrank K (W ⧸ B)) → K) ≃ W ⧸ B := b.equivFun.symm.toEquiv
  let τ : Freq B ≃ (Fin (finrank K (W ⧸ B)) → K) :=
    (FourierAux.freqDualEquiv B).trans (b.constr K).symm.toEquiv
  have key : ∀ (ξ : Freq B) (c : Fin (finrank K (W ⧸ B)) → K),
      B.liftQ ξ.1 ξ.2 (σ c) = ∑ i, τ ξ i * c i := fun ξ c =>
    FourierAux.dual_apply_equivFun_symm b _ c
  refine ⟨σ, τ, ?_, ?_⟩
  · intro h ξ
    simp only [fourierQ, Circuit.dft]
    refine (Fintype.sum_equiv σ _ _ (fun c => ?_)).symm
    rw [key]
  · intro g x
    simp only [fourierQInv, Circuit.idft]
    congr 1
    refine Fintype.sum_equiv τ _ _ (fun ξ => ?_)
    rw [Equiv.symm_apply_apply, ← key, Equiv.apply_symm_apply]

/-! ### Tables over all directions -/

/-- `F`: Fourier-transform every coset table `h_B`. -/
noncomputable def fourierSig (F : FourierData K S) (P' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) (Bξ : Σ B : SubP K W P', Freq B.1) : S :=
  fourierQ F Bξ.1.1 (fun x => h ⟨Bξ.1, x⟩) Bξ.2

/-- `F⁻¹`. -/
noncomputable def fourierInvSig (F : FourierData K S) (Q' : ℕ → Prop)
    (g : (Σ D : SubP K W Q', Freq D.1) → S) (Dx : Σ D : SubP K W Q', W ⧸ D.1) : S :=
  fourierQInv F Dx.1.1 (fun ξ => g ⟨Dx.1, ξ⟩) Dx.2

theorem fourierInvSig_fourierSig (F : FourierData K S) (P' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) : fourierInvSig F P' (fourierSig F P' h) = h := by
  funext Bx
  exact congrFun (fourierQInv_fourierQ F Bx.1.1 (fun x => h ⟨Bx.1, x⟩)) Bx.2

theorem fourierSig_fourierInvSig (F : FourierData K S) (P' : ℕ → Prop)
    (g : (Σ B : SubP K W P', Freq B.1) → S) : fourierSig F P' (fourierInvSig F P' g) = g := by
  funext Bξ
  exact congrFun (fourierQ_fourierQInv F Bξ.1.1 (fun ξ => g ⟨Bξ.1, ξ⟩)) Bξ.2

/-- The forward map of `freqEquiv`: `(B, λ) ↦ (λ, B ≤ ker λ)`. -/
def freqTo (P' : ℕ → Prop) (Bξ : Σ B : SubP K W P', Freq B.1) :
    Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P' :=
  ⟨Bξ.2.1, FourierAux.subIn Bξ.1 (LinearMap.ker Bξ.2.1) Bξ.2.2⟩

/-- The inverse map of `freqEquiv`: `(λ, B' ≤ ker λ) ↦ (B', λ)` with `B'` regarded in `W`. -/
def freqFrom (P' : ℕ → Prop) (ξB : Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P') :
    Σ B : SubP K W P', Freq B.1 :=
  ⟨FourierAux.subOut ξB.2, ⟨ξB.1, FourierAux.subOut_le ξB.2⟩⟩

theorem freqFrom_freqTo (P' : ℕ → Prop) (Bξ : Σ B : SubP K W P', Freq B.1) :
    freqFrom P' (freqTo P' Bξ) = Bξ :=
  Sigma.subtype_ext (FourierAux.subOut_subIn Bξ.1 Bξ.2.2) rfl

theorem freqTo_freqFrom (P' : ℕ → Prop) (ξB : Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P') :
    freqTo P' (freqFrom P' ξB) = ξB :=
  Sigma.ext rfl (heq_of_eq (FourierAux.subIn_subOut ξB.2))

/-- Regrouping the Fourier entries by frequency: pairs `(B, λ)` with `B ≤ ker λ`, listed by `λ`,
with `B` regarded as a subspace of `ker λ`. -/
noncomputable def freqEquiv (P' : ℕ → Prop) :
    (Σ B : SubP K W P', Freq B.1) ≃ Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P' :=
  ⟨freqTo P', freqFrom P', freqFrom_freqTo P', freqTo_freqFrom P'⟩

theorem freqEquiv_apply (P' : ℕ → Prop) (Bξ : Σ B : SubP K W P', Freq B.1) :
    freqEquiv P' Bξ = freqTo P' Bξ := rfl

theorem freqEquiv_symm_apply (P' : ℕ → Prop)
    (ξB : Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P') :
    (freqEquiv P').symm ξB = freqFrom P' ξB := rfl

theorem freqEquiv_fst (P' : ℕ → Prop) (Bξ : Σ B : SubP K W P', Freq B.1) :
    (freqEquiv P' Bξ).1 = Bξ.2.1 := rfl

theorem freqEquiv_map (P' : ℕ → Prop) (Bξ : Σ B : SubP K W P', Freq B.1) :
    (freqEquiv P' Bξ).2.1.map (LinearMap.ker (freqEquiv P' Bξ).1).subtype = Bξ.1.1 :=
  congrArg Subtype.val (FourierAux.subOut_subIn Bξ.1 Bξ.2.2)

/-- `⊕_λ T_{ker λ}`: the containment transform inside each kernel, one block per frequency. -/
noncomputable def blockT (P' Q' : ℕ → Prop)
    (u : (Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P') → S)
    (v : Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) Q') : S :=
  containT P' Q' (fun B => u ⟨v.1, B⟩) v.2

theorem fourierQ_congr_sub (F : FourierData K S) {P' : ℕ → Prop}
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) {B₁ B₂ : SubP K W P'} (e : B₁ = B₂)
    (ξ : Module.Dual K W) (h₁ : B₁.1 ≤ LinearMap.ker ξ) (h₂ : B₂.1 ≤ LinearMap.ker ξ) :
    fourierQ F B₁.1 (fun y => h ⟨B₁, y⟩) ⟨ξ, h₁⟩ =
      fourierQ F B₂.1 (fun y => h ⟨B₂, y⟩) ⟨ξ, h₂⟩ := by
  subst e
  rfl

theorem blockT_freqEquiv (P' Q' : ℕ → Prop)
    (u : (Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P') → S) (D : SubP K W Q')
    (ξ : Freq D.1) :
    blockT P' Q' u (freqEquiv Q' ⟨D, ξ⟩) =
      containT P' Q' (fun U => u ⟨ξ.1, U⟩) (FourierAux.subIn D (LinearMap.ker ξ.1) ξ.2) := rfl

theorem fourierSig_freqEquiv_symm (F : FourierData K S) (P' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) (ξ : Module.Dual K W)
    (U : SubP K (LinearMap.ker ξ) P') :
    fourierSig F P' h ((freqEquiv P').symm ⟨ξ, U⟩) =
      fourierQ F (FourierAux.subOut U).1 (fun y => h ⟨FourierAux.subOut U, y⟩)
        ⟨ξ, FourierAux.subOut_le U⟩ := rfl

open Classical in
/-- The block of frequency `λ`: summing `ĥ_λ(B)` over `B ≤ D` is the containment transform inside
`ker λ`. -/
theorem sum_le_eq_blockT (F : FourierData K S) (P' Q' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) (D : SubP K W Q') (ξ : Freq D.1) :
    ∑ B : {B : SubP K W P' // B.1 ≤ D.1},
        fourierQ F B.1.1 (fun y => h ⟨B.1, y⟩) ⟨ξ.1, B.2.trans ξ.2⟩ =
      blockT P' Q' (fun ξB => fourierSig F P' h ((freqEquiv P').symm ξB))
        (freqEquiv Q' ⟨D, ξ⟩) := by
  rw [blockT_freqEquiv, containT]
  refine Finset.sum_bij'
    (fun B _ => FourierAux.subIn B.1 (LinearMap.ker ξ.1) (B.2.trans ξ.2))
    (fun U hU =>
      ⟨FourierAux.subOut U, (FourierAux.subOut_le_iff U D.1).2 (Finset.mem_filter.1 hU).2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro B _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (FourierAux.subIn_le_subIn_iff _ _).2 B.2⟩
  · intro U _
    exact Finset.mem_univ _
  · intro B _
    exact Subtype.ext (FourierAux.subOut_subIn _ _)
  · intro U _
    exact FourierAux.subIn_subOut U
  · intro B _
    rw [fourierSig_freqEquiv_symm]
    exact fourierQ_congr_sub F h (FourierAux.subOut_subIn _ _).symm _ _ _

open Classical in
/-- **Lemma 3.1** (affine Fourier identity). -/
theorem fourier_affineT (F : FourierData K S) (P' Q' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) (D : SubP K W Q') (ξ : Freq D.1) :
    fourierQ F D.1 (fun x => affineT P' Q' h ⟨D, x⟩) ξ =
      ∑ B : {B : SubP K W P' // B.1 ≤ D.1},
        fourierQ F B.1.1 (fun y => h ⟨B.1, y⟩) ⟨ξ.1, B.2.trans ξ.2⟩ := by
  have step1 : fourierQ F D.1 (fun x => affineT P' Q' h ⟨D, x⟩) ξ =
      ∑ B : SubP K W P', ∑ y : W ⧸ B.1, ∑ x : W ⧸ D.1,
        (if cosetLE B.1 D.1 y x then h ⟨B, y⟩ * F.ψ (D.1.liftQ ξ.1 ξ.2 x) else 0) := by
    simp only [fourierQ, affineT, Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm, Fintype.sum_sigma]
  rw [step1, FourierAux.sum_eq_sum_subtype_of_zero (fun B : SubP K W P' => B.1 ≤ D.1)]
  · refine Finset.sum_congr rfl fun B _ => ?_
    simp only [fourierQ]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [FourierAux.sum_ite_cosetLE B.2 y, FourierAux.liftQ_factor B.2 ξ.1 ξ.2 y]
  · intro B hB
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x _ => ?_
    rw [ite_eq_right (FourierAux.not_cosetLE hB y x)]

/-- **Equation (block)**: `A = F⁻¹ ∘ (⊕_λ T_{ker λ}) ∘ F`. -/
theorem affineT_eq (F : FourierData K S) (P' Q' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) :
    affineT P' Q' h =
      fourierInvSig F Q' (fun Dξ =>
        blockT P' Q' (fun ξB => fourierSig F P' h ((freqEquiv P').symm ξB)) (freqEquiv Q' Dξ)) := by
  funext Dx
  obtain ⟨D, x⟩ := Dx
  calc affineT P' Q' h ⟨D, x⟩
      = fourierQInv F D.1 (fourierQ F D.1 (fun x => affineT P' Q' h ⟨D, x⟩)) x :=
        (congrFun (fourierQInv_fourierQ F D.1 (fun x => affineT P' Q' h ⟨D, x⟩)) x).symm
    _ = fourierQInv F D.1 (fun ξ => blockT P' Q'
          (fun ξB => fourierSig F P' h ((freqEquiv P').symm ξB)) (freqEquiv Q' ⟨D, ξ⟩)) x := by
        congr 1
        funext ξ
        rw [fourier_affineT, sum_le_eq_blockT]

end Fourier

/-! ### Coefficient rings -/

/-- Over `ℂ`: `ψ(t) = exp(2πi Tr(t)/p)`. -/
noncomputable def FourierData.complex (K : Type*) [Field K] [Fintype K] : FourierData K ℂ :=
  ⟨FourierAux.complexChar K, FourierAux.complexChar_sum_mul_eq_zero,
    FourierAux.isUnit_card_complex⟩

/-- Over `ℂ` every constant of the Fourier circuits has modulus at most one. -/
theorem FourierData.complex_consts (K : Type*) [Field K] [Fintype K] :
    (FourierData.complex K).consts ⊆ Metric.closedBall (0 : ℂ) 1 := by
  have hψ : ∀ x, ‖(FourierData.complex K).ψ x‖ = 1 := fun x => FourierAux.norm_complexChar K x
  have hq : ‖(FourierData.complex K).qinv‖ ≤ 1 := by
    have h1 := congrArg norm (FourierData.complex K).qinv_mul
    rw [norm_mul, norm_one, Complex.norm_natCast] at h1
    have h2 : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    nlinarith [norm_nonneg (FourierData.complex K).qinv]
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  rcases hc with rfl | rfl | rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · simp
  · simp
  · simp
  · rw [hψ]
  · rw [norm_mul, hψ, mul_one]
    exact hq

/-- `R[t]/(1 + t + ⋯ + t^{p-1})` (Section 3.4). -/
abbrev ExtRing (R : Type*) [CommRing R] (p : ℕ) :=
  AdjoinRoot (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i)

/-- The extension is free over `R` with basis `1, t, …, t^{p-2}`. -/
noncomputable def ExtRing.basis (R : Type*) [CommRing R] (p : ℕ) (hp : 0 < p) :
    Module.Basis (Fin (p - 1)) R (ExtRing R p) :=
  FourierAux.extBasis R p hp

/-- The `0`-th coordinate of a constant is the constant. -/
theorem ExtRing.basis_repr_algebraMap (R : Type*) [CommRing R] (p : ℕ) (hp : 2 ≤ p) (r : R) :
    (ExtRing.basis R p (by omega)).repr (algebraMap R (ExtRing R p) r) ⟨0, by omega⟩ = r :=
  FourierAux.extBasis_repr_algebraMap R p hp r

/-- Section 3.4: over any commutative ring in which `p = char K` is invertible,
`ψ(x) = ζ^{Tr x}` on `R[t]/(1 + t + ⋯ + t^{p-1})` is a primitive character and `q` is invertible. -/
noncomputable def FourierData.ext (K : Type*) [Field K] [Fintype K] (R : Type*) [CommRing R]
    (hp : IsUnit ((ringChar K : ℕ) : R)) : FourierData K (ExtRing R (ringChar K)) :=
  ⟨FourierAux.extChar R K, FourierAux.extChar_sum_mul_eq_zero hp, FourierAux.isUnit_card_ext hp⟩

end SubspaceConvolution
