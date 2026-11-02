/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Fourier
import SubspaceConvolution.Transform.StepAux

/-!
# One step of the hyperplane recursion, as a circuit

`containT_step`: for a hyperplane `H` of `V` (`HypData`), the containment transform
`containT P Q` on `V` is computed from
* the inside transforms `containT P Q` and `containT P Q'` on `H` (one map, cost `s_in`),
* one containment transform `containT P' Q'` on each `ker λ`, `λ ∈ H*` (cost `s λ`),
* the Fourier transforms of the crossing tables and the inverse transforms of the outputs, and
  one addition per crossing output (equations (cut), (rank-cut), (block)).

`zetaInv_step`: the same for `Z⁻¹`, through equation (inverse).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

variable {K : Type*} [Field K] [Fintype K] {S : Type*} [CommRing S]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The local work of one recursion step: Fourier transforms of the crossing input tables,
inverse transforms of the crossing output tables, one addition per crossing output. -/
noncomputable def stepWork (K : Type*) [Field K] [Fintype K] (n : ℕ) {H : Type*} [AddCommGroup H]
    [Module K H] [FiniteDimensional K H] (P' Q' : ℕ → Prop) : ℕ :=
  (2 * Fintype.card K + 1) * n *
    (∑ B : SubP K H P', Fintype.card (H ⧸ B.1) + ∑ W : SubP K H Q', Fintype.card (H ⧸ W.1))

namespace StepAux

/-- A subspace of dimension at most `k`, as one of dimension at most `k + 1`. -/
def embLE {W : Type*} [AddCommGroup W] [Module K W] (k : ℕ) (B : SubLE K W k) :
    SubLE K W (k + 1) :=
  ⟨B.1, Nat.le_succ_of_le B.2⟩

theorem hPk (k : ℕ) : ∀ d, d + 1 ≤ k + 1 ↔ d ≤ k := fun _ => Nat.succ_le_succ_iff

/-- The circuit of equation (inverse): `f₀ = Z⁻¹ g₀`, `f₁ = A⁻¹ (g₁ - g₀(D))`. -/
noncomputable def invCand (F : FourierData K S) (D : HypData K V) (k : ℕ)
    (g : SubLE K V (k + 1) → S) (W : SubLE K V (k + 1)) : S :=
  Sum.elim
    (zetaInv (k + 1) (fun U => g ((D.split (· ≤ k + 1) (· ≤ k) (hPk k)).symm (Sum.inl U))))
    (fourierConj F (· ≤ k) (· ≤ k) (fun _ => zetaInv k)
      (fun x => g ((D.split (· ≤ k + 1) (· ≤ k) (hPk k)).symm (Sum.inr x)) -
        g ((D.split (· ≤ k + 1) (· ≤ k) (hPk k)).symm (Sum.inl (embLE k x.1)))))
    (D.split (· ≤ k + 1) (· ≤ k) (hPk k) W)

theorem zeta_invCand (F : FourierData K S) (D : HypData K V) (k : ℕ)
    (g : SubLE K V (k + 1) → S) : zeta (k + 1) (invCand F D k g) = g := by
  funext W
  obtain ⟨z, rfl⟩ := (D.split (· ≤ k + 1) (· ≤ k) (hPk k)).symm.surjective W
  rw [zeta_eq_containT]
  cases z with
  | inl W' =>
    rw [D.containT_split_inl (P := (· ≤ k + 1)) (P' := (· ≤ k)) (Q := (· ≤ k + 1))
      (Q' := (· ≤ k)) (hPk k) (hPk k)]
    simp only [invCand, Equiv.apply_symm_apply, Sum.elim_inl]
    exact congrFun (zeta_zetaInv (k + 1) _) W'
  | inr Wx =>
    rw [D.containT_split_inr (P := (· ≤ k + 1)) (P' := (· ≤ k)) (Q := (· ≤ k + 1))
      (Q' := (· ≤ k)) (hPk k) (hPk k)]
    simp only [invCand, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [affineT_fourierConj_zetaInv]
    have e3 := congrFun (zeta_zetaInv (k + 1)
      (fun U => g ((D.split (· ≤ k + 1) (· ≤ k) (hPk k)).symm (Sum.inl U)))) (embLE k Wx.1)
    rw [show ∀ f : SubLE K D.H (k + 1) → S,
      containT (· ≤ k + 1) (· ≤ k) f Wx.1 = zeta (k + 1) f (embLE k Wx.1) from fun _ => rfl,
      e3]
    ring

theorem invCand_eq (F : FourierData K S) (D : HypData K V) (k : ℕ) :
    invCand F D k = zetaInv (k + 1) := by
  funext g
  calc invCand F D k g = zetaInv (k + 1) (zeta (k + 1) (invCand F D k g)) :=
        (zetaInv_zeta _ _).symm
    _ = zetaInv (k + 1) g := by rw [zeta_invCand]

end StepAux

/-- **One step of Sections 3 and 4.** -/
theorem containT_step (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C) (D : HypData K V)
    {P P' Q Q' : ℕ → Prop} (hP : ∀ d, P (d + 1) ↔ P' d) (hQ : ∀ d, Q (d + 1) ↔ Q' d)
    {s_in : ℕ}
    (h_in : LinCost C (fun f₀ : SubP K D.H P → S => Sum.elim (containT P Q f₀) (containT P Q' f₀))
      s_in)
    (s : Module.Dual K D.H → ℕ)
    (h_blk : ∀ ξ, LinCost C (containT (K := K) (V := LinearMap.ker ξ) (R := S) P' Q') (s ξ)) :
    LinCost C (containT (K := K) (V := V) (R := S) P Q)
      (s_in + ∑ ξ, s ξ + stepWork K (finrank K V) (H := D.H) P' Q') := by
  have hH := D.finrank_H
  have hn : 0 < finrank K V := by omega
  have hHn : finrank K D.H ≤ finrank K V := by omega
  have h_aff := StepAux.affineT_linCost F hC P' Q' hHn s h_blk
  have hA := StepAux.linCost_assemble (hC (StepAux.one_mem_consts F)) h_in h_aff
    (fun Wx : (Σ W : SubP K D.H Q', D.H ⧸ W.1) => Wx.1)
  have hfull := hA.reindex (D.split P P' hP).symm (D.split Q Q' hQ)
  refine (hfull.congr ?_).mono ?_
  · funext f W
    obtain ⟨z, rfl⟩ := (D.split Q Q' hQ).symm.surjective W
    simp only [Equiv.apply_symm_apply]
    cases z with
    | inl W' => exact (D.containT_split_inl hP hQ f W').symm
    | inr Wx => exact (D.containT_split_inr hP hQ f Wx).symm
  · simp only [stepWork, Fintype.card_sigma]
    generalize (∑ B : SubP K D.H P', Fintype.card (D.H ⧸ B.1)) = X₁
    generalize (∑ W : SubP K D.H Q', Fintype.card (D.H ⧸ W.1)) = X₂
    generalize (∑ ξ, s ξ) = T
    generalize Fintype.card K = q
    generalize finrank K V = n at hn ⊢
    have h2 : X₂ ≤ n * X₂ := Nat.le_mul_of_pos_left X₂ hn
    have h3 := Nat.zero_le (n * q * X₁)
    have h4 := Nat.zero_le (n * X₁)
    have h5 := Nat.zero_le (n * q * X₂)
    nlinarith

/-- **One step of equation (inverse)** for `Z⁻¹`. -/
theorem zetaInv_step (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C) (D : HypData K V)
    (k : ℕ) {s₀ : ℕ} (h₀ : LinCost C (zetaInv (K := K) (V := D.H) (R := S) (k + 1)) s₀)
    (s : Module.Dual K D.H → ℕ)
    (h_blk : ∀ ξ, LinCost C (zetaInv (K := K) (V := LinearMap.ker ξ) (R := S) k) (s ξ)) :
    LinCost C (zetaInv (K := K) (V := V) (R := S) (k + 1))
      (s₀ + ∑ ξ, s ξ + stepWork K (finrank K V) (H := D.H) (· ≤ k) (· ≤ k)) := by
  have hH := D.finrank_H
  have hn : 0 < finrank K V := by omega
  have hHn : finrank K D.H ≤ finrank K V := by omega
  have h_conj := StepAux.fourierConj_linCost F hC (· ≤ k) (· ≤ k) hHn
    (fun _ => zetaInv k) s h_blk
  have hA := StepAux.linCost_assembleInv (hC (StepAux.one_mem_consts F))
    (hC (StepAux.neg_one_mem_consts F)) h₀ h_conj
    (fun x : (Σ B : SubLE K D.H k, D.H ⧸ B.1) => StepAux.embLE k x.1)
  have hfull := hA.reindex (D.split (· ≤ k + 1) (· ≤ k) (StepAux.hPk k)).symm
    (D.split (· ≤ k + 1) (· ≤ k) (StepAux.hPk k))
  have hcand : LinCost C (StepAux.invCand F D k) _ := hfull.congr (by funext g W; rfl)
  refine (hcand.congr (StepAux.invCand_eq F D k)).mono ?_
  simp only [stepWork, Fintype.card_sigma]
  generalize (∑ B : SubP K D.H (· ≤ k), Fintype.card (D.H ⧸ B.1)) = X
  generalize (∑ ξ, s ξ) = T
  generalize Fintype.card K = q
  generalize finrank K V = n at hn ⊢
  have h2 : X ≤ n * X := Nat.le_mul_of_pos_left X hn
  nlinarith

end SubspaceConvolution
