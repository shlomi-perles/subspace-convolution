/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Fourier

/-!
# Helper lemmas for one recursion step

* `linCost_selAdd`, `linCost_selSub` — copying entries and adding/subtracting pairs of entries
  costs one gate per sum.
* `linCost_assemble`, `linCost_assembleInv` — the final assembly of a recursion step
  (equations (cut) and (inverse)): an inside map, a crossing map and one addition (subtraction)
  per crossing output (input).
* `fourierQ_linCost`, `fourierQInv_linCost`, `fourierSig_linCost`, `fourierInvSig_linCost` —
  costs of the Fourier transforms on the coset tables.
* `blockMap`, `fourierConj` — `F⁻¹ ∘ (⊕_λ T_λ) ∘ F` for an arbitrary family of block maps
  `T_λ`, its cost `fourierConj_linCost`, and the algebra `fourierConj_comp`, `fourierConj_id`.
* `affineT_eq_fourierConj`, `affineT_fourierConj_zetaInv` — equation (block) and its inverse.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

namespace StepAux

section Select

variable {R : Type*} [CommRing R] {C : Set R}

/-- Copying some entries and adding pairs of others: one gate per sum. -/
theorem linCost_selAdd {J O₁ O₂ : Type*} [Fintype O₂] (h1 : (1 : R) ∈ C)
    (a : O₁ → J) (b c : O₂ → J) :
    LinCost C (fun (u : J → R) => Sum.elim (fun o => u (a o)) (fun o => u (b o) + u (c o)))
      (Fintype.card O₂) := by
  have h₁ : LinCost C (fun (u : J → R) (o : O₁) => u (a o)) 0 :=
    (LinCost.id (C := C) (I := J)).reindex id a
  have h₂ : LinCost C (fun (u : J → R) (o : O₂) => u (b o)) 0 :=
    (LinCost.id (C := C) (I := J)).reindex id b
  have h₃ : LinCost C (fun (u : J → R) (o : O₂) => u (c o)) 0 :=
    (LinCost.id (C := C) (I := J)).reindex id c
  have h₄ := LinCost.lincomb h₂ h₃ h1 h1
  have h₅ := LinCost.sumElim h₁ h₄
  refine (h₅.congr ?_).mono (by simp only [add_zero, zero_add, le_refl])
  funext u o
  simp only [one_mul]

/-- One subtraction per output. -/
theorem linCost_selSub {J O : Type*} [Fintype O] (h1 : (1 : R) ∈ C) (hm1 : (-1 : R) ∈ C)
    (b c : O → J) :
    LinCost C (fun (u : J → R) (o : O) => u (b o) - u (c o)) (Fintype.card O) := by
  have h₂ : LinCost C (fun (u : J → R) (o : O) => u (b o)) 0 :=
    (LinCost.id (C := C) (I := J)).reindex id b
  have h₃ : LinCost C (fun (u : J → R) (o : O) => u (c o)) 0 :=
    (LinCost.id (C := C) (I := J)).reindex id c
  have h₄ := LinCost.lincomb h₂ h₃ h1 hm1
  refine (h₄.congr ?_).mono (by simp only [add_zero, zero_add, le_refl])
  funext u o
  ring

/-- **Assembly of a step (equations (cut), (rank-cut))**: the inside outputs are read off the
inside map; each crossing output adds an inside value and the crossing value. -/
theorem linCost_assemble {I₀ I₁ O₀ O₀' O₁ : Type*} [Fintype O₁] (h1 : (1 : R) ∈ C)
    {M_in : (I₀ → R) → O₀ ⊕ O₀' → R} {s_in : ℕ} (h_in : LinCost C M_in s_in)
    {M_cr : (I₁ → R) → O₁ → R} {s_cr : ℕ} (h_cr : LinCost C M_cr s_cr) (π : O₁ → O₀') :
    LinCost C (fun g : I₀ ⊕ I₁ → R =>
        Sum.elim (fun o => M_in (fun i => g (Sum.inl i)) (Sum.inl o))
          (fun o => M_in (fun i => g (Sum.inl i)) (Sum.inr (π o)) +
            M_cr (fun i => g (Sum.inr i)) o))
      (s_in + s_cr + Fintype.card O₁) := by
  have hA := LinCost.sumElim (h_in.reindex (Sum.inl : I₀ → I₀ ⊕ I₁) id)
    (h_cr.reindex (Sum.inr : I₁ → I₀ ⊕ I₁) id)
  have hB := linCost_selAdd (C := C) (J := (O₀ ⊕ O₀') ⊕ O₁) h1
    (fun o : O₀ => Sum.inl (Sum.inl o)) (fun o : O₁ => Sum.inl (Sum.inr (π o))) Sum.inr
  refine (hA.comp hB).congr ?_
  funext g o
  rfl

/-- **Assembly of an inverse step (equation (inverse))**: the inside part is inverted by `M₀`;
the crossing part first subtracts the known inside values, then is inverted by `M₁`. -/
theorem linCost_assembleInv {I₀ I₁ : Type*} [Fintype I₁] (h1 : (1 : R) ∈ C)
    (hm1 : (-1 : R) ∈ C) {M₀ : (I₀ → R) → I₀ → R} {s₀ : ℕ} (h₀ : LinCost C M₀ s₀)
    {M₁ : (I₁ → R) → I₁ → R} {s₁ : ℕ} (h₁ : LinCost C M₁ s₁) (π : I₁ → I₀) :
    LinCost C (fun g : I₀ ⊕ I₁ → R => Sum.elim (M₀ (fun i => g (Sum.inl i)))
        (M₁ (fun x => g (Sum.inr x) - g (Sum.inl (π x)))))
      (s₀ + Fintype.card I₁ + s₁) := by
  have hA := LinCost.sumElim (h₀.reindex (Sum.inl : I₀ → I₀ ⊕ I₁) id)
    (linCost_selSub (C := C) (J := I₀ ⊕ I₁) h1 hm1 (Sum.inr : I₁ → I₀ ⊕ I₁)
      (fun x => Sum.inl (π x)))
  have hB := LinCost.sumElim ((LinCost.id (C := C) (I := I₀ ⊕ I₁)).reindex id
    (Sum.inl : I₀ → I₀ ⊕ I₁)) (h₁.reindex (Sum.inr : I₁ → I₀ ⊕ I₁) id)
  refine ((hA.comp hB).congr ?_).mono (by omega)
  funext g o
  cases o <;> rfl

end Select

variable {K : Type*} [Field K] [Fintype K] {S : Type*} [CommRing S]

section Consts

theorem zero_mem_consts (F : FourierData K S) : (0 : S) ∈ F.consts := Or.inl rfl

theorem one_mem_consts (F : FourierData K S) : (1 : S) ∈ F.consts := Or.inr (Or.inl rfl)

theorem neg_one_mem_consts (F : FourierData K S) : (-1 : S) ∈ F.consts :=
  Or.inr (Or.inr (Or.inl rfl))

end Consts

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

section FourierCost

/-- The Fourier transform of one coset table (equation (fft)) costs `e q |W/B|`,
`e = dim W/B`. -/
theorem fourierQ_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (B : Submodule K W) :
    LinCost C (fourierQ F B)
      (finrank K (W ⧸ B) * Fintype.card K * Fintype.card (W ⧸ B)) := by
  obtain ⟨σ, τ, h1, -⟩ := fourierQ_eq_dft F B
  have h := (Circuit.dft_cost F hC (finrank K (W ⧸ B))).reindex σ τ
  refine (h.congr ?_).mono (le_of_eq ?_)
  · funext g ξ
    exact (h1 g ξ).symm
  · rw [card_quotient, pow_succ]
    ring

/-- The inverse transform of one table (equation (ifft)). -/
theorem fourierQInv_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (B : Submodule K W) :
    LinCost C (fourierQInv F B)
      (finrank K (W ⧸ B) * Fintype.card K * Fintype.card (W ⧸ B)) := by
  obtain ⟨σ, τ, -, h2⟩ := fourierQ_eq_dft F B
  have h := (Circuit.idft_cost F hC (finrank K (W ⧸ B))).reindex τ.symm σ.symm
  refine (h.congr ?_).mono (le_of_eq ?_)
  · funext g x
    exact (h2 g x).symm
  · rw [card_quotient, pow_succ]
    ring

theorem sum_finrank_quotient_le (P' : ℕ → Prop) {n : ℕ} (hn : finrank K W ≤ n) :
    ∑ B : SubP K W P', finrank K (W ⧸ B.1) * Fintype.card K * Fintype.card (W ⧸ B.1) ≤
      n * Fintype.card K * ∑ B : SubP K W P', Fintype.card (W ⧸ B.1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun B _ => ?_
  have := Submodule.finrank_quotient_le B.1
  have h' : finrank K (W ⧸ B.1) ≤ n := le_trans this hn
  gcongr

/-- `F`: all the coset tables, `n q ∑_B |W/B|` gates for `dim W ≤ n`. -/
theorem fourierSig_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (P' : ℕ → Prop) {n : ℕ} (hn : finrank K W ≤ n) :
    LinCost C (fourierSig F P' (W := W))
      (n * Fintype.card K * ∑ B : SubP K W P', Fintype.card (W ⧸ B.1)) := by
  have h := LinCost.sigma (C := C) (fun B : SubP K W P' => fourierQ F B.1) _
    (fun B => fourierQ_linCost F hC B.1)
  exact (h.congr rfl).mono (sum_finrank_quotient_le P' hn)

/-- `F⁻¹`: all the coset tables. -/
theorem fourierInvSig_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (Q' : ℕ → Prop) {n : ℕ} (hn : finrank K W ≤ n) :
    LinCost C (fourierInvSig F Q' (W := W))
      (n * Fintype.card K * ∑ D : SubP K W Q', Fintype.card (W ⧸ D.1)) := by
  have h := LinCost.sigma (C := C) (fun D : SubP K W Q' => fourierQInv F D.1) _
    (fun D => fourierQInv_linCost F hC D.1)
  exact (h.congr rfl).mono (sum_finrank_quotient_le Q' hn)

end FourierCost

section Conj

/-- `⊕_λ T_λ`: one block map per frequency. -/
noncomputable def blockMap {P' Q' : ℕ → Prop}
    (T : ∀ ξ : Module.Dual K W,
      (SubP K (LinearMap.ker ξ) P' → S) → SubP K (LinearMap.ker ξ) Q' → S)
    (u : (Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) P') → S)
    (v : Σ ξ : Module.Dual K W, SubP K (LinearMap.ker ξ) Q') : S :=
  T v.1 (fun B => u ⟨v.1, B⟩) v.2

/-- `F⁻¹ ∘ (⊕_λ T_λ) ∘ F`, with the regrouping by frequency. -/
noncomputable def fourierConj (F : FourierData K S) (P' Q' : ℕ → Prop)
    (T : ∀ ξ : Module.Dual K W,
      (SubP K (LinearMap.ker ξ) P' → S) → SubP K (LinearMap.ker ξ) Q' → S)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) : (Σ D : SubP K W Q', W ⧸ D.1) → S :=
  fourierInvSig F Q' (fun Dξ =>
    blockMap T (fun ξB => fourierSig F P' h ((freqEquiv P').symm ξB)) (freqEquiv Q' Dξ))

/-- The cost of `F⁻¹ ∘ (⊕_λ T_λ) ∘ F`. -/
theorem fourierConj_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (P' Q' : ℕ → Prop) {n : ℕ} (hn : finrank K W ≤ n)
    (T : ∀ ξ : Module.Dual K W,
      (SubP K (LinearMap.ker ξ) P' → S) → SubP K (LinearMap.ker ξ) Q' → S)
    (s : Module.Dual K W → ℕ) (hT : ∀ ξ, LinCost C (T ξ) (s ξ)) :
    LinCost C (fourierConj F P' Q' T)
      (n * Fintype.card K * ∑ B : SubP K W P', Fintype.card (W ⧸ B.1) + ∑ ξ, s ξ +
        n * Fintype.card K * ∑ D : SubP K W Q', Fintype.card (W ⧸ D.1)) := by
  have h₁ := (fourierSig_linCost F hC P' hn).reindex id (freqEquiv P').symm
  have h₂ := (LinCost.sigma T s hT).reindex id (freqEquiv Q')
  have h₃ := fourierInvSig_linCost F hC Q' hn
  refine ((h₁.comp h₂).comp h₃).congr ?_
  funext h
  rfl

theorem fourierConj_comp (F : FourierData K S) (P' Q' R' : ℕ → Prop)
    (T₁ : ∀ ξ : Module.Dual K W,
      (SubP K (LinearMap.ker ξ) Q' → S) → SubP K (LinearMap.ker ξ) R' → S)
    (T₂ : ∀ ξ : Module.Dual K W,
      (SubP K (LinearMap.ker ξ) P' → S) → SubP K (LinearMap.ker ξ) Q' → S)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) :
    fourierConj F Q' R' T₁ (fourierConj F P' Q' T₂ h) =
      fourierConj F P' R' (fun ξ f => T₁ ξ (T₂ ξ f)) h := by
  unfold fourierConj
  simp only [fourierSig_fourierInvSig, Equiv.apply_symm_apply]
  rfl

theorem fourierConj_id (F : FourierData K S) (P' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) :
    fourierConj F P' P' (fun _ f => f) h = h := by
  unfold fourierConj blockMap
  simp only [Sigma.eta, Equiv.symm_apply_apply]
  exact fourierInvSig_fourierSig F P' h

/-- **Equation (block)** in the form `A = F⁻¹ ∘ (⊕_λ T_{ker λ}) ∘ F`. -/
theorem affineT_eq_fourierConj (F : FourierData K S) (P' Q' : ℕ → Prop)
    (h : (Σ B : SubP K W P', W ⧸ B.1) → S) :
    affineT P' Q' h = fourierConj F P' Q' (fun _ => containT P' Q') h :=
  affineT_eq F P' Q' h

/-- The affine transform `A`: Fourier transforms and one transform per frequency. -/
theorem affineT_linCost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C)
    (P' Q' : ℕ → Prop) {n : ℕ} (hn : finrank K W ≤ n) (s : Module.Dual K W → ℕ)
    (h_blk : ∀ ξ, LinCost C (containT (K := K) (V := LinearMap.ker ξ) (R := S) P' Q') (s ξ)) :
    LinCost C (affineT (K := K) P' Q' (W := W) (R := S))
      (n * Fintype.card K * ∑ B : SubP K W P', Fintype.card (W ⧸ B.1) + ∑ ξ, s ξ +
        n * Fintype.card K * ∑ D : SubP K W Q', Fintype.card (W ⧸ D.1)) := by
  refine (fourierConj_linCost F hC P' Q' hn _ s h_blk).congr ?_
  funext h
  exact (affineT_eq_fourierConj F P' Q' h).symm

/-- **Equation (inverse)**: `A⁻¹ = F⁻¹ ∘ (⊕_λ Z⁻¹_{ker λ}) ∘ F` (cutoff `k` on both sides). -/
theorem affineT_fourierConj_zetaInv (F : FourierData K S) (k : ℕ)
    (d : (Σ B : SubLE K W k, W ⧸ B.1) → S) :
    affineT (K := K) (· ≤ k) (· ≤ k)
      (fourierConj F (· ≤ k) (· ≤ k) (fun _ => zetaInv k) d) = d := by
  rw [affineT_eq_fourierConj F, fourierConj_comp]
  have : (fun (ξ : Module.Dual K W) (f : SubLE K (LinearMap.ker ξ) k → S) =>
      containT (· ≤ k) (· ≤ k) (zetaInv k f)) = fun _ f => f := by
    funext ξ f
    exact zeta_zetaInv k f
  rw [this, fourierConj_id]

end Conj

end StepAux

end SubspaceConvolution
