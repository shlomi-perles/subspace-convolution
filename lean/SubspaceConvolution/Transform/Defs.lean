/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.SubspaceCount

/-!
# The subspace transforms of the paper: shared definitions

Throughout, `K` is a finite field (`F_q`) and `V` a finite-dimensional `K`-space (playing the
role of `F_q^n`; working with abstract spaces lets the recursion of Section 3 call itself on
`ker λ` without choosing coordinates).

* `SubLE K V k` — subspaces of dimension at most `k` (the index set of `Z_{n,k}`);
  `Grass K V j` — the `j`-dimensional subspaces (`Gr(n, j)`).
* `zeta k` — the truncated zeta transform `(Z_{n,k} f)(W) = ∑_{U ≤ W, dim U ≤ k} f(U)`;
  `zetaT k` — its transpose (sums over superspaces);
  `zetaInv k`, `zetaTInv k` — their inverses (Möbius transforms), with
  `zeta_zetaInv`, `zetaInv_zeta`, `zetaT_zetaTInv`, `zetaTInv_zetaT`.
* `incid a b` — the incidence transform `I^{a,b}`; `incidT a b` — its transpose.
* `gDist`, `grassGraph`, `kernelApply` — distances, the Grassmann graph `J_q(n,k)` and
  intersection kernels `K(U,W) = a_{dist(U,W)}`.
* `spanConv` — span convolution; `spanCount` — exact-span counts (Theorem 5.1).
* `FourierData` — a coefficient ring with a primitive additive character of `K`
  (Sections 2.1 and 3.4).
* `numLE K n k = M_q(n,k)`, `gr K n j = |Gr(n,j)|`, and `card_subLE`/`card_grass`: the counts
  depend only on the dimension.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

section Finite

/-- Subspaces whose dimension satisfies `P`.  The two index sets of the paper are special cases:
`SubLE K V k` (dimension at most `k`) and `Grass K V j` (dimension exactly `j`). -/
abbrev SubP (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (P : ℕ → Prop) :=
  {U : Submodule K V // P (finrank K U)}

/-- Subspaces of dimension at most `k`: the index set of the truncated zeta transform. -/
abbrev SubLE (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  SubP K V (· ≤ k)

/-- The Grassmannian `Gr(V, j)`: the `j`-dimensional subspaces. -/
abbrev Grass (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (j : ℕ) :=
  SubP K V (· = j)

variable (K : Type*) [Field K] [Fintype K]
variable (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

include K in
theorem finite_of_fd : Finite V := Module.finite_of_finite K

noncomputable instance instFintypeSubmoduleFd : Fintype (Submodule K V) :=
  haveI := finite_of_fd K V
  Fintype.ofFinite _

noncomputable instance instFintypeSubP (P : ℕ → Prop) : Fintype (SubP K V P) := Fintype.ofFinite _

/-- Cosets of a subspace form a finite set. -/
noncomputable instance instFintypeQuotientFd (B : Submodule K V) : Fintype (V ⧸ B) :=
  haveI := finite_of_fd K V
  haveI : Finite (V ⧸ B) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective B)
  Fintype.ofFinite _

/-- Linear functionals on `V` form a finite set. -/
noncomputable instance instFintypeDualFd : Fintype (Module.Dual K V) :=
  haveI : Finite (Module.Dual K V) := Module.finite_of_finite K
  Fintype.ofFinite _

end Finite

/-! ### Counts -/

section Counts

variable (K : Type*) [Field K] [Fintype K]

/-- `M_q(n, k)`: the number of subspaces of `K^n` of dimension at most `k`. -/
noncomputable def numLE (n k : ℕ) : ℕ := Fintype.card (SubLE K (Fin n → K) k)

/-- `|Gr(n, j)|`: the number of `j`-dimensional subspaces of `K^n`. -/
noncomputable def gr (n j : ℕ) : ℕ := Fintype.card (Grass K (Fin n → K) j)

variable {K}
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Subspaces of `V` correspond to subspaces of `K^n`, preserving dimensions. -/
noncomputable def submoduleEquivFin {n : ℕ} (h : finrank K V = n) :
    Submodule K V ≃o Submodule K (Fin n → K) :=
  Submodule.orderIsoMapComap (LinearEquiv.ofFinrankEq V (Fin n → K) (by simp [h]))

theorem finrank_submoduleEquivFin {n : ℕ} (h : finrank K V = n) (U : Submodule K V) :
    finrank K (submoduleEquivFin h U) = finrank K U := by
  exact LinearEquiv.finrank_map_eq _ _

theorem card_subLE {n : ℕ} (h : finrank K V = n) (k : ℕ) :
    Fintype.card (SubLE K V k) = numLE K n k := by
  unfold numLE
  refine Fintype.card_congr ((submoduleEquivFin h).toEquiv.subtypeEquiv fun U => ?_)
  simp [finrank_submoduleEquivFin h U]

theorem card_grass {n : ℕ} (h : finrank K V = n) (j : ℕ) :
    Fintype.card (Grass K V j) = gr K n j := by
  unfold gr
  refine Fintype.card_congr ((submoduleEquivFin h).toEquiv.subtypeEquiv fun U => ?_)
  simp [finrank_submoduleEquivFin h U]

end Counts

/-! ### The transforms -/

section Transforms

variable {K : Type*} [Field K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type*} [CommRing R]

open Classical in
/-- The truncated zeta transform `(Z_{n,k} f)(W) = ∑_{U ≤ W, dim U ≤ k} f(U)`. -/
noncomputable def zeta (k : ℕ) (f : SubLE K V k → R) (W : SubLE K V k) : R :=
  ∑ U ∈ univ.filter (fun U : SubLE K V k => U.1 ≤ W.1), f U

open Classical in
/-- Its transpose `(Z_{n,k}ᵀ g)(U) = ∑_{W ≥ U, dim W ≤ k} g(W)`: sums over superspaces. -/
noncomputable def zetaT (k : ℕ) (g : SubLE K V k → R) (U : SubLE K V k) : R :=
  ∑ W ∈ univ.filter (fun W : SubLE K V k => U.1 ≤ W.1), g W

open Classical in
/-- The inverse of `Z_{n,k}` (the Möbius transform), by recursion on the dimension. -/
noncomputable def zetaInv (k : ℕ) (g : SubLE K V k → R) (W : SubLE K V k) : R :=
  g W - ∑ U : {U : SubLE K V k // U.1 < W.1}, zetaInv k g U.1
termination_by finrank K W.1
decreasing_by exact Submodule.finrank_lt_finrank_of_lt U.2

open Classical in
/-- The inverse of `Z_{n,k}ᵀ`, by recursion on the codimension. -/
noncomputable def zetaTInv (k : ℕ) (g : SubLE K V k → R) (U : SubLE K V k) : R :=
  g U - ∑ W : {W : SubLE K V k // U.1 < W.1}, zetaTInv k g W.1
termination_by finrank K V - finrank K U.1
decreasing_by
  have h1 := Submodule.finrank_lt_finrank_of_lt W.2
  have h2 := Submodule.finrank_le W.1.1
  omega

open Classical in
theorem zetaInv_eq (k : ℕ) (g : SubLE K V k → R) (W : SubLE K V k) :
    zetaInv k g W = g W - ∑ U : {U : SubLE K V k // U.1 < W.1}, zetaInv k g U.1 := by
  rw [zetaInv]

open Classical in
theorem zetaTInv_eq (k : ℕ) (g : SubLE K V k → R) (U : SubLE K V k) :
    zetaTInv k g U = g U - ∑ W : {W : SubLE K V k // U.1 < W.1}, zetaTInv k g W.1 := by
  rw [zetaTInv]

open Classical in
/-- Splitting a sum over `U ≤ W` into `U = W` and `U < W`. -/
theorem sum_le_eq_add_sum_lt (k : ℕ) (f : SubLE K V k → R) (W : SubLE K V k) :
    ∑ U ∈ univ.filter (fun U : SubLE K V k => U.1 ≤ W.1), f U =
      f W + ∑ U : {U : SubLE K V k // U.1 < W.1}, f U.1 := by
  rw [← sum_filter_add_sum_filter_not _ (fun U : SubLE K V k => U = W)]
  congr 1
  · rw [filter_filter, show (univ.filter fun U : SubLE K V k => U.1 ≤ W.1 ∧ U = W) = {W} by
      ext U; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨le_rfl, rfl⟩]
    simp
  · rw [filter_filter]
    refine sum_bij' (fun U hU => ⟨U, ?_⟩) (fun U _ => U.1) ?_ ?_ ?_ ?_ ?_
    · obtain ⟨h1, h2⟩ := (mem_filter.1 hU).2
      exact lt_of_le_of_ne h1 fun h => h2 (Subtype.ext h)
    · intro _ _; exact mem_univ _
    · intro U _
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨U.2.le, fun h => (ne_of_lt U.2) (congrArg Subtype.val h)⟩
    · intro _ _; rfl
    · intro _ _; rfl
    · intro _ _; rfl

open Classical in
theorem sum_ge_eq_add_sum_gt (k : ℕ) (f : SubLE K V k → R) (U : SubLE K V k) :
    ∑ W ∈ univ.filter (fun W : SubLE K V k => U.1 ≤ W.1), f W =
      f U + ∑ W : {W : SubLE K V k // U.1 < W.1}, f W.1 := by
  rw [← sum_filter_add_sum_filter_not _ (fun W : SubLE K V k => W = U)]
  congr 1
  · rw [filter_filter, show (univ.filter fun W : SubLE K V k => U.1 ≤ W.1 ∧ W = U) = {U} by
      ext W; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨le_rfl, rfl⟩]
    simp
  · rw [filter_filter]
    refine sum_bij' (fun W hW => ⟨W, ?_⟩) (fun W _ => W.1) ?_ ?_ ?_ ?_ ?_
    · obtain ⟨h1, h2⟩ := (mem_filter.1 hW).2
      exact lt_of_le_of_ne h1 fun h => h2 (Subtype.ext h.symm)
    · intro _ _; exact mem_univ _
    · intro W _
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨W.2.le, fun h => (ne_of_lt W.2) (congrArg Subtype.val h.symm)⟩
    · intro _ _; rfl
    · intro _ _; rfl
    · intro _ _; rfl

/-- `Z (Z⁻¹ g) = g`. -/
theorem zeta_zetaInv (k : ℕ) (g : SubLE K V k → R) : zeta k (zetaInv k g) = g := by
  funext W
  rw [zeta, sum_le_eq_add_sum_lt, zetaInv_eq k g W]
  ring

open Classical in
/-- `Z⁻¹ (Z f) = f`. -/
theorem zetaInv_zeta (k : ℕ) (f : SubLE K V k → R) : zetaInv k (zeta k f) = f := by
  funext W
  induction' h : finrank K W.1 using Nat.strong_induction_on with d ih generalizing W
  rw [zetaInv_eq, zeta, sum_le_eq_add_sum_lt]
  have : ∑ U : {U : SubLE K V k // U.1 < W.1}, zetaInv k (zeta k f) U.1 =
      ∑ U : {U : SubLE K V k // U.1 < W.1}, f U.1 := by
    refine Fintype.sum_congr _ _ fun U => ?_
    exact ih _ (h ▸ Submodule.finrank_lt_finrank_of_lt U.2) U.1 rfl
  rw [this]
  ring

/-- `Zᵀ (Zᵀ⁻¹ g) = g`. -/
theorem zetaT_zetaTInv (k : ℕ) (g : SubLE K V k → R) : zetaT k (zetaTInv k g) = g := by
  funext U
  rw [zetaT, sum_ge_eq_add_sum_gt, zetaTInv_eq k g U]
  ring

open Classical in
/-- `Zᵀ⁻¹ (Zᵀ f) = f`. -/
theorem zetaTInv_zetaT (k : ℕ) (f : SubLE K V k → R) : zetaTInv k (zetaT k f) = f := by
  funext U
  induction' h : finrank K V - finrank K U.1 using Nat.strong_induction_on with d ih generalizing U
  rw [zetaTInv_eq, zetaT, sum_ge_eq_add_sum_gt]
  have : ∑ W : {W : SubLE K V k // U.1 < W.1}, zetaTInv k (zetaT k f) W.1 =
      ∑ W : {W : SubLE K V k // U.1 < W.1}, f W.1 := by
    refine Fintype.sum_congr _ _ fun W => ?_
    have h1 := Submodule.finrank_lt_finrank_of_lt W.2
    have h2 := Submodule.finrank_le W.1.1
    exact ih _ (by omega) W.1 rfl
  rw [this]
  ring

open Classical in
/-- The incidence transform `(I^{a,b} f)(W) = ∑_{U ≤ W, dim U = a} f(U)`, `dim W = b`. -/
noncomputable def incid (a b : ℕ) (f : Grass K V a → R) (W : Grass K V b) : R :=
  ∑ U ∈ univ.filter (fun U : Grass K V a => U.1 ≤ W.1), f U

open Classical in
/-- Its transpose: `(I^{a,b}ᵀ g)(U) = ∑_{W ≥ U, dim W = b} g(W)`. -/
noncomputable def incidT (a b : ℕ) (g : Grass K V b → R) (U : Grass K V a) : R :=
  ∑ W ∈ univ.filter (fun W : Grass K V b => U.1 ≤ W.1), g W

/-- The distance `k - dim(U ∩ W)` on `Gr(V, k)`. -/
noncomputable def gDist (k : ℕ) (U W : Grass K V k) : ℕ := k - finrank K (U.1 ⊓ W.1 : Submodule K V)

/-- The Grassmann graph `J_q(n, k)`: `U ~ W` iff `dim(U ∩ W) = k - 1`. -/
def grassGraph (k : ℕ) : SimpleGraph (Grass K V k) where
  Adj U W := U ≠ W ∧ finrank K (U.1 ⊓ W.1 : Submodule K V) + 1 = k
  symm := ⟨fun U W h => ⟨h.1.symm, by rw [inf_comm]; exact h.2⟩⟩
  loopless := ⟨fun U h => h.1 rfl⟩

/-- An intersection kernel: `(K f)(U) = ∑_W a_{dist(U,W)} f(W)` on `Gr(V, k)`. -/
noncomputable def kernelApply (k : ℕ) (a : ℕ → R) (f : Grass K V k → R) (U : Grass K V k) : R :=
  ∑ W, a (gDist k U W) * f W

open Classical in
/-- Span convolution `(f ⋆ g)(W) = ∑_{U + U' = W} f(U) g(U')`. -/
noncomputable def spanConv (f g : Submodule K V → R) (W : Submodule K V) : R :=
  ∑ U, ∑ U', if U ⊔ U' = W then f U * g U' else 0

open Classical in
/-- The full zeta transform on all subspaces. -/
noncomputable def zetaAll (f : Submodule K V → R) (W : Submodule K V) : R :=
  ∑ U ∈ univ.filter (fun U : Submodule K V => U ≤ W), f U

open Classical in
/-- Exact-span counts `C(U) = #{A ⊆ [ℓ] : span{v_i : i ∈ A} = U}` (Theorem 5.1). -/
noncomputable def spanCount {ℓ : ℕ} (v : Fin ℓ → V) (U : Submodule K V) : ℕ :=
  #(univ.filter fun A : Finset (Fin ℓ) => Submodule.span K (v '' (A : Set (Fin ℓ))) = U)

open Classical in
/-- The general containment transform from `P`-dimensional to `Q`-dimensional subspaces:
`(T f)(W) = ∑_{U ≤ W, P(dim U)} f(U)` for `Q(dim W)`.  Both `zeta` and `incid` are instances
(`zeta_eq_containT`, `incid_eq_containT`), and the hyperplane recursion of Sections 3 and 4 is
proved once for this transform. -/
noncomputable def containT (P Q : ℕ → Prop) (f : SubP K V P → R) (W : SubP K V Q) : R :=
  ∑ U ∈ univ.filter (fun U : SubP K V P => U.1 ≤ W.1), f U

theorem zeta_eq_containT (k : ℕ) :
    (zeta k : (SubLE K V k → R) → SubLE K V k → R) = containT (· ≤ k) (· ≤ k) := rfl

theorem incid_eq_containT (a b : ℕ) :
    (incid a b : (Grass K V a → R) → Grass K V b → R) = containT (· = a) (· = b) := rfl

end Transforms

/-! ### Fourier coefficient rings -/

/-- Coefficients for Fourier transforms over the finite field `K = F_q` (Section 2.1, 3.4): a
commutative ring `S` in which `q` is invertible, with an additive character `ψ : K → S` that is
primitive in the sense `∑_x ψ(a x) = 0` for `a ≠ 0`.  Examples: `ℂ` with
`ψ(t) = exp(2πi Tr(t)/p)`, and `R[t]/(1 + t + ⋯ + t^{p-1})` for any commutative ring `R` with `p`
invertible. -/
structure FourierData (K : Type*) [Field K] [Fintype K] (S : Type*) [CommRing S] where
  /-- the additive character -/
  ψ : AddChar K S
  /-- primitivity -/
  sum_mul_eq_zero : ∀ a : K, a ≠ 0 → ∑ x : K, ψ (a * x) = 0
  /-- `q` is invertible -/
  isUnit_card : IsUnit (Fintype.card K : S)

namespace FourierData

variable {K : Type*} [Field K] [Fintype K] {S : Type*} [CommRing S]

/-- `q⁻¹` in `S`. -/
noncomputable def qinv (F : FourierData K S) : S := ↑(F.isUnit_card.unit⁻¹)

theorem qinv_mul (F : FourierData K S) : F.qinv * (Fintype.card K : S) = 1 := by
  simp [qinv]

theorem mul_qinv (F : FourierData K S) : (Fintype.card K : S) * F.qinv = 1 := by
  simp [qinv]

/-- The constants used by the Fourier-based circuits: `0, 1, -1`, the character values `ψ(x)`
and the normalized values `q⁻¹ ψ(x)`.  Over `ℂ` all of them have modulus at most one. -/
def consts (F : FourierData K S) : Set S :=
  {c | c = 0 ∨ c = 1 ∨ c = -1 ∨ (∃ x, c = F.ψ x) ∨ (∃ x, c = F.qinv * F.ψ x)}

end FourierData

end SubspaceConvolution
