/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Defs

/-!
# Coefficient rings for the Fourier transforms (Sections 2.1 and 3.4)

* `absTrace K : K →+ ZMod p` — the absolute trace (`p = char K`), and its nondegeneracy in the
  normalized form `exists_absTrace_mul_eq_one`.
* `complexChar K` — `ψ(t) = exp(2πi Tr(t)/p)`, of modulus one and primitive.
* `extBasis R p` — `R[t]/(1 + t + ⋯ + t^{p-1})` is free over `R` with basis `1, t, …, t^{p-2}`
  (`extBasis_repr_algebraMap`: the `0`-th coordinate of a constant is the constant).
* `extChar R K` — `ψ(x) = ζ^{Tr x}` with `ζ = t`, primitive whenever `p` is invertible in `R`
  (`extChar_sum_mul_eq_zero`); no roots of unity or domain hypotheses are needed.

Everything lives in the namespace `SubspaceConvolution.FourierAux`.
-/

open Finset Module Polynomial

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.FourierAux

/-! ### Character sums by averaging -/

/-- A character sum vanishes if some translate direction `b` has `∑_{j<n} χ(j b) = 0` with `n`
invertible: averaging over the translates `x + j b`. -/
theorem addChar_sum_eq_zero_of_shift {G S : Type*} [AddCommGroup G] [Fintype G] [CommRing S]
    (χ : AddChar G S) (b : G) (n : ℕ) (hn : IsUnit (n : S))
    (hb : ∑ j ∈ range n, χ (j • b) = 0) : ∑ x, χ x = 0 := by
  have hshift : ∀ j : ℕ, ∑ x, χ (x + j • b) = ∑ x, χ x := fun j =>
    Fintype.sum_equiv (Equiv.addRight (j • b)) _ _ (fun x => rfl)
  have key : (n : S) * ∑ x, χ x = 0 := by
    calc (n : S) * ∑ x, χ x = ∑ j ∈ range n, ∑ x, χ (x + j • b) := by
          simp only [hshift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∑ x, χ x * ∑ j ∈ range n, χ (j • b) := by
          rw [Finset.sum_comm]
          simp only [AddChar.map_add_eq_mul, Finset.mul_sum]
      _ = 0 := by simp only [hb, mul_zero, Finset.sum_const_zero]
  exact hn.mul_right_eq_zero.1 key

/-! ### The absolute trace -/

section Trace

variable (K : Type*) [Field K] [Fintype K]

theorem ringChar_prime : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)

/-- The prime-field algebra structure on `K`. -/
noncomputable abbrev zmodAlg : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)

/-- The absolute trace `Tr : K → F_p`. -/
noncomputable def absTrace : K →+ ZMod (ringChar K) :=
  letI := zmodAlg K
  (Algebra.trace (ZMod (ringChar K)) K).toAddMonoidHom

variable {K}

/-- Nondegeneracy of the trace form: for `a ≠ 0` some `b` has `Tr(a b) = 1`. -/
theorem exists_absTrace_mul_eq_one {a : K} (ha : a ≠ 0) : ∃ b : K, absTrace K (a * b) = 1 := by
  let _ := zmodAlg K
  have : Fact (ringChar K).Prime := ⟨ringChar_prime K⟩
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate K ha
  refine ⟨(Algebra.trace (ZMod (ringChar K)) K (a * b))⁻¹ • b, ?_⟩
  simp only [absTrace, LinearMap.toAddMonoidHom_coe]
  rw [mul_smul_comm, map_smul, smul_eq_mul, inv_mul_cancel₀ hb]

end Trace

/-! ### The complex character -/

section Complex

variable (K : Type*) [Field K] [Fintype K]

/-- `ψ(t) = exp(2πi Tr(t)/p)`. -/
noncomputable def complexChar : AddChar K ℂ :=
  haveI : NeZero (ringChar K) := ⟨(ringChar_prime K).ne_zero⟩
  ZMod.stdAddChar.compAddMonoidHom (absTrace K)

theorem norm_complexChar (x : K) : ‖complexChar K x‖ = 1 := by
  simp only [complexChar, AddChar.compAddMonoidHom_apply, ZMod.stdAddChar_apply, Circle.norm_coe]

variable {K}

theorem complexChar_sum_mul_eq_zero (a : K) (ha : a ≠ 0) :
    ∑ x : K, complexChar K (a * x) = 0 := by
  have : NeZero (ringChar K) := ⟨(ringChar_prime K).ne_zero⟩
  have : Fact (1 < ringChar K) := ⟨(ringChar_prime K).one_lt⟩
  obtain ⟨b, hb⟩ := exists_absTrace_mul_eq_one ha
  have hne : (complexChar K).mulShift a ≠ 1 := by
    intro h1
    have h2 := DFunLike.congr_fun h1 b
    rw [AddChar.mulShift_apply, one_apply] at h2
    simp only [complexChar, AddChar.compAddMonoidHom_apply, hb] at h2
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := ringChar K))] at h2
    exact one_ne_zero (ZMod.injective_stdAddChar h2)
  have h3 := AddChar.sum_eq_zero_of_ne_one hne
  simpa only [AddChar.mulShift_apply] using h3

theorem isUnit_card_complex : IsUnit (Fintype.card K : ℂ) :=
  isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

end Complex

/-! ### The extension ring `R[t]/(1 + t + ⋯ + t^{p-1})` -/

section Ext

variable (R : Type*) [CommRing R] (p : ℕ)

/-- `1 + X + ⋯ + X^{p-1}`. -/
noncomputable abbrev geomPoly : R[X] := ∑ i ∈ Finset.range p, (X : R[X]) ^ i

theorem natDegree_geomPoly [Nontrivial R] (hp : 0 < p) : (geomPoly R p).natDegree = p - 1 := by
  have hmul : (X - C 1) * geomPoly R p = X ^ p - C 1 := by
    rw [map_one, mul_geom_sum]
  have h1 : ((X - C 1) * geomPoly R p).natDegree =
      (X - C (1 : R)).natDegree + (geomPoly R p).natDegree :=
    (monic_X_sub_C (1 : R)).natDegree_mul (monic_geom_sum_X hp.ne')
  rw [hmul, natDegree_X_pow_sub_C, natDegree_X_sub_C] at h1
  omega

theorem subsingleton_of_natDegree_geomPoly (hp : 0 < p)
    (h : ¬ (geomPoly R p).natDegree = p - 1) : Subsingleton R :=
  not_nontrivial_iff_subsingleton.1 fun _ => h (natDegree_geomPoly R p hp)

/-- `R[t]/(1 + ⋯ + t^{p-1})` is free with basis `1, t, …, t^{p-2}`.  (Over the zero ring every
family is a basis.) -/
noncomputable def extBasis (hp : 0 < p) : Basis (Fin (p - 1)) R (AdjoinRoot (geomPoly R p)) :=
  if h : (geomPoly R p).natDegree = p - 1 then
    (AdjoinRoot.powerBasisAux' (monic_geom_sum_X hp.ne')).reindex (finCongr h)
  else
    haveI := subsingleton_of_natDegree_geomPoly R p hp h
    haveI : Subsingleton (AdjoinRoot (geomPoly R p)) :=
      Module.subsingleton R (AdjoinRoot (geomPoly R p))
    Basis.ofEquivFun (LinearEquiv.ofSubsingleton _ _)

theorem extBasis_repr_algebraMap (hp : 2 ≤ p) (r : R) :
    (extBasis R p (by omega)).repr (algebraMap R (AdjoinRoot (geomPoly R p)) r)
      ⟨0, by omega⟩ = r := by
  unfold extBasis
  split_ifs with h
  · have hg := monic_geom_sum_X (R := R) (n := p) (by omega)
    have h0 : 0 < (AdjoinRoot.powerBasis' hg).dim := by
      rw [AdjoinRoot.powerBasis'_dim, h]; omega
    have h1 : ((AdjoinRoot.powerBasisAux' hg).reindex (finCongr h)) ⟨0, by omega⟩ = 1 := by
      rw [Basis.reindex_apply]
      have h2 := (AdjoinRoot.powerBasis' hg).basis_eq_pow ⟨0, h0⟩
      simp only [pow_zero] at h2
      exact h2
    rw [Algebra.algebraMap_eq_smul_one, ← h1, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · have := subsingleton_of_natDegree_geomPoly R p (by omega) h
    exact Subsingleton.elim _ _

/-- `ζ = t mod (1 + t + ⋯ + t^{p-1})`. -/
noncomputable abbrev extRoot : AdjoinRoot (geomPoly R p) := AdjoinRoot.root (geomPoly R p)

theorem sum_pow_extRoot : ∑ i ∈ range p, (extRoot R p) ^ i = 0 := by
  have h : aeval (extRoot R p) (geomPoly R p) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simpa only [geomPoly, map_sum, map_pow, aeval_X] using h

theorem extRoot_pow : (extRoot R p) ^ p = 1 := by
  have h := geom_sum_mul (extRoot R p) p
  rw [sum_pow_extRoot, zero_mul] at h
  exact sub_eq_zero.1 h.symm

/-- The character `j ↦ ζ^j` of `ZMod p`, for `ζ^p = 1`. -/
def powChar {M : Type*} [Monoid M] (p : ℕ) [NeZero p] (ζ : M) (hζ : ζ ^ p = 1) :
    AddChar (ZMod p) M where
  toFun j := ζ ^ j.val
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) p, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem powChar_apply {M : Type*} [Monoid M] (p : ℕ) [NeZero p] (ζ : M) (hζ : ζ ^ p = 1)
    (j : ZMod p) : powChar p ζ hζ j = ζ ^ j.val := rfl

variable (K : Type*) [Field K] [Fintype K]

/-- `ψ(x) = ζ^{Tr x}`. -/
noncomputable def extChar : AddChar K (AdjoinRoot (geomPoly R (ringChar K))) :=
  haveI : NeZero (ringChar K) := ⟨(ringChar_prime K).ne_zero⟩
  (powChar (ringChar K) (extRoot R (ringChar K)) (extRoot_pow R _)).compAddMonoidHom (absTrace K)

variable {R K}

theorem isUnit_ringChar_ext (hp : IsUnit ((ringChar K : ℕ) : R)) :
    IsUnit ((ringChar K : ℕ) : AdjoinRoot (geomPoly R (ringChar K))) := by
  have h := hp.map (algebraMap R (AdjoinRoot (geomPoly R (ringChar K))))
  rwa [map_natCast] at h

theorem extChar_sum_mul_eq_zero (hp : IsUnit ((ringChar K : ℕ) : R)) (a : K) (ha : a ≠ 0) :
    ∑ x : K, extChar R K (a * x) = 0 := by
  have : NeZero (ringChar K) := ⟨(ringChar_prime K).ne_zero⟩
  have : Fact (1 < ringChar K) := ⟨(ringChar_prime K).one_lt⟩
  obtain ⟨b, hb⟩ := exists_absTrace_mul_eq_one ha
  have h := addChar_sum_eq_zero_of_shift ((extChar R K).mulShift a) b (ringChar K)
    (isUnit_ringChar_ext hp) ?_
  · simpa only [AddChar.mulShift_apply] using h
  · have hj : ∀ j : ℕ, (extChar R K).mulShift a (j • b) = (extRoot R (ringChar K)) ^ j := by
      intro j
      rw [AddChar.mulShift_apply, mul_smul_comm]
      simp only [extChar, AddChar.compAddMonoidHom_apply, hb,
        AddChar.map_nsmul_eq_pow, powChar_apply, ZMod.val_one]
      rw [pow_one]
    simp only [hj]
    exact sum_pow_extRoot R (ringChar K)

theorem isUnit_card_ext (hp : IsUnit ((ringChar K : ℕ) : R)) :
    IsUnit (Fintype.card K : AdjoinRoot (geomPoly R (ringChar K))) := by
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [hn, Nat.cast_pow]
  exact (isUnit_ringChar_ext hp).pow _

end Ext

end SubspaceConvolution.FourierAux
