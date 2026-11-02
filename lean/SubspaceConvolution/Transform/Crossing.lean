/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Defs

/-!
# The hyperplane cut (Lemma 2.1, equations (cut) and (rank-cut))

Fix a hyperplane `H ≤ V` and a vector `e ∉ H` (`HypData`); in the paper `V = F_q^n`,
`H = F_q^{n-1} × {0}`, `e = (0, …, 0, 1)`.

* `HypData.lift B x = U(B, x + B) = (B × {0}) + ⟨x + e⟩` (`x + B` a coset of `B ≤ H`).
* **Lemma 2.1** (`HypData.existsUnique_lift`, `lift_inf_H`, `finrank_lift`, `lift_le_lift_iff`):
  every subspace not contained in `H` is a unique `U(B, x + B)`; `U ∩ H = B`;
  `dim U = dim B + 1`; and `U(B₁, x₁ + B₁) ≤ U(B₂, x₂ + B₂)` iff `B₁ ≤ B₂` and `x₁ - x₂ ∈ B₂`.
* `HypData.split P P' hP` — subspaces of `V` with dimension in `P` are the inside ones (in `H`)
  and the crossing ones, indexed by `(B, x + B)` with `dim B ∈ P'` (`P (d + 1) ↔ P' d`).
* `affineT` — the affine transform `(A h)_D(x + D) = ∑_{B ≤ D} ∑_{y + B ⊆ x + D} h_B(y + B)`.
* `HypData.containT_split_inl`, `HypData.containT_split_inr` — **equations (cut) and
  (rank-cut)**, for the general containment transform `containT P Q`:
  inside outputs see only inside inputs; a crossing output `U(D, x + D)` sees the inside inputs
  below `D` and the affine sum of the crossing inputs.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {K : Type*} [Field K] [Fintype K]

section Coset

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Coset containment `y + B ⊆ x + D`: `B ≤ D` and the two cosets meet. -/
def cosetLE (B D : Submodule K W) (y : W ⧸ B) (x : W ⧸ D) : Prop :=
  B ≤ D ∧ ∃ w : W, Submodule.Quotient.mk w = y ∧ Submodule.Quotient.mk w = x

end Coset

section Affine

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {R : Type*} [CommRing R]

open Classical in
/-- The affine transform `(A h)_D(x + D) = ∑_{B ≤ D} ∑_{y + B ⊆ x + D} h_B(y + B)` (Section 3.1),
from directions with dimension in `P'` to directions with dimension in `Q'`. -/
noncomputable def affineT (P' Q' : ℕ → Prop) (h : (Σ B : SubP K W P', W ⧸ B.1) → R)
    (Dx : Σ D : SubP K W Q', W ⧸ D.1) : R :=
  ∑ By ∈ univ.filter (fun By : Σ B : SubP K W P', W ⧸ B.1 => cosetLE By.1.1 Dx.1.1 By.2 Dx.2),
    h By

end Affine

section Hyperplane

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable (K V) in
/-- A hyperplane `H` of `V` and a vector `e` outside it. -/
structure HypData where
  H : Submodule K V
  e : V
  he : e ∉ H
  sup_eq_top : H ⊔ K ∙ e = ⊤

namespace HypData

theorem nonempty (h : 0 < finrank K V) : Nonempty (HypData K V) := by
  have : Nontrivial V := Module.finrank_pos_iff.1 h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hv
  refine ⟨⟨LinearMap.ker φ, v, fun hm => hφ (LinearMap.mem_ker.1 hm), ?_⟩⟩
  refine eq_top_iff.2 fun w _ => ?_
  rw [← sub_add_cancel w ((φ w / φ v) • v)]
  refine Submodule.add_mem_sup ?_ (Submodule.mem_span_singleton.2 ⟨_, rfl⟩)
  rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hφ, sub_self]

theorem e_ne_zero (D : HypData K V) : D.e ≠ 0 := fun h => D.he (h ▸ D.H.zero_mem)

/-- Every vector is `h + c • e` with `h ∈ H`. -/
theorem exists_decomp (D : HypData K V) (v : V) : ∃ h ∈ D.H, ∃ c : K, h + c • D.e = v := by
  have hv : v ∈ D.H ⊔ K ∙ D.e := by rw [D.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨h, hh, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨h, hh, c, rfl⟩

/-- `h + c • e ∈ H` (with `h ∈ H`) forces `c = 0`. -/
theorem add_smul_e_mem_iff (D : HypData K V) {h : V} (hh : h ∈ D.H) (c : K) :
    h + c • D.e ∈ D.H ↔ c = 0 := by
  rw [D.H.add_mem_iff_right hh]
  constructor
  · intro hc
    by_contra hc0
    exact D.he ((D.H.smul_mem_iff hc0).1 hc)
  · rintro rfl
    rw [zero_smul]
    exact D.H.zero_mem

theorem add_e_not_mem (D : HypData K V) (x : D.H) : (x : V) + D.e ∉ D.H := fun h =>
  D.he ((D.H.add_mem_iff_right x.2).1 h)

theorem add_e_ne_zero (D : HypData K V) (x : D.H) : (x : V) + D.e ≠ 0 := fun h0 =>
  D.add_e_not_mem x (by rw [h0]; exact D.H.zero_mem)

theorem finrank_H (D : HypData K V) : finrank K D.H + 1 = finrank K V := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq D.H (K ∙ D.e)
  rw [D.sup_eq_top, ((Submodule.disjoint_span_singleton' D.e_ne_zero).2 D.he).eq_bot,
    finrank_top, finrank_bot, finrank_span_singleton D.e_ne_zero, add_zero] at h1
  exact h1.symm

/-- `U(B, x + B)` from a representative `x ∈ H`. -/
def liftRep (D : HypData K V) (B : Submodule K D.H) (x : D.H) : Submodule K V :=
  B.map D.H.subtype ⊔ K ∙ ((x : V) + D.e)

theorem liftRep_le_of_sub_mem (D : HypData K V) (B : Submodule K D.H) {x x' : D.H}
    (h : x - x' ∈ B) : D.liftRep B x ≤ D.liftRep B x' := by
  refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
  have hx : (x : V) + D.e = ((x - x' : D.H) : V) + ((x' : V) + D.e) := by
    rw [Submodule.coe_sub]; abel
  rw [hx]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem h) (Submodule.mem_span_singleton_self _)

theorem liftRep_congr (D : HypData K V) (B : Submodule K D.H) {x x' : D.H} (h : x - x' ∈ B) :
    D.liftRep B x = D.liftRep B x' := by
  exact le_antisymm (D.liftRep_le_of_sub_mem B h)
    (D.liftRep_le_of_sub_mem B (by rw [← neg_sub]; exact B.neg_mem h))

theorem mem_liftRep (D : HypData K V) (B : Submodule K D.H) (x : D.H) (v : V) :
    v ∈ D.liftRep B x ↔ ∃ b ∈ B, ∃ c : K, (b : V) + c • ((x : V) + D.e) = v := by
  simp only [liftRep, Submodule.mem_sup, Submodule.mem_map, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨b, hb, c, rfl⟩
  · rintro ⟨b, hb, c, rfl⟩
    exact ⟨_, ⟨b, hb, rfl⟩, _, ⟨c, rfl⟩, rfl⟩

theorem add_e_mem_liftRep (D : HypData K V) (B : Submodule K D.H) (x : D.H) :
    (x : V) + D.e ∈ D.liftRep B x :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem map_le_liftRep (D : HypData K V) (B : Submodule K D.H) (x : D.H) :
    B.map D.H.subtype ≤ D.liftRep B x :=
  le_sup_left

theorem liftRep_inf_H (D : HypData K V) (B : Submodule K D.H) (x : D.H) :
    D.liftRep B x ⊓ D.H = B.map D.H.subtype := by
  apply le_antisymm
  · rintro v ⟨hv, hvH⟩
    obtain ⟨b, hb, c, rfl⟩ := (D.mem_liftRep B x v).1 hv
    have hc : c = 0 := by
      have hm : ((b : V) + c • (x : V)) + c • D.e ∈ D.H := by
        rw [smul_add, ← add_assoc] at hvH; exact hvH
      exact (D.add_smul_e_mem_iff (D.H.add_mem b.2 (D.H.smul_mem c x.2)) c).1 hm
    subst hc
    rw [zero_smul, add_zero]
    exact Submodule.mem_map_of_mem hb
  · exact le_inf (D.map_le_liftRep B x) (Submodule.map_subtype_le _ _)

/-- The crossing subspace `U(B, x + B) = (B × {0}) + ⟨x + e⟩`. -/
def lift (D : HypData K V) (B : Submodule K D.H) (x : D.H ⧸ B) : Submodule K V :=
  Quotient.liftOn' x (D.liftRep B) fun _ _ h =>
    D.liftRep_congr B ((Submodule.quotientRel_def B).1 h)

@[simp] theorem lift_mk (D : HypData K V) (B : Submodule K D.H) (x : D.H) :
    D.lift B (Submodule.Quotient.mk x) = D.liftRep B x := rfl

/-- **Lemma 2.1**: `dim U(B, x + B) = dim B + 1`. -/
theorem finrank_lift (D : HypData K V) (B : Submodule K D.H) (x : D.H ⧸ B) :
    finrank K (D.lift B x) = finrank K B + 1 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective B x
  rw [lift_mk]
  have hdisj : Disjoint (B.map D.H.subtype) (K ∙ ((x : V) + D.e)) :=
    (Submodule.disjoint_span_singleton' (D.add_e_ne_zero x)).2 fun hm =>
      D.add_e_not_mem x (Submodule.map_subtype_le _ _ hm)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (B.map D.H.subtype) (K ∙ ((x : V) + D.e))
  rw [hdisj.eq_bot, finrank_bot, add_zero, Submodule.finrank_map_subtype_eq,
    finrank_span_singleton (D.add_e_ne_zero x)] at h1
  exact h1

/-- **Lemma 2.1**: `U(B, x + B) ∩ H = B × {0}`. -/
theorem lift_inf_H (D : HypData K V) (B : Submodule K D.H) (x : D.H ⧸ B) :
    D.lift B x ⊓ D.H = B.map D.H.subtype := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective B x
  rw [lift_mk]
  exact D.liftRep_inf_H B x

theorem not_lift_le_H (D : HypData K V) (B : Submodule K D.H) (x : D.H ⧸ B) :
    ¬ D.lift B x ≤ D.H := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective B x
  rw [lift_mk]
  exact fun hle => D.add_e_not_mem x (hle (D.add_e_mem_liftRep B x))

/-- Existence part of Lemma 2.1: a crossing subspace is `U(U ∩ H, x + (U ∩ H))`. -/
theorem exists_lift (D : HypData K V) (U : Submodule K V) (hU : ¬ U ≤ D.H) :
    ∃ x : D.H, D.liftRep (U.comap D.H.subtype) x = U := by
  obtain ⟨u, huU, huH⟩ := IsConcreteLE.not_le_iff_exists.1 hU
  obtain ⟨h, hh, c, rfl⟩ := D.exists_decomp u
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at huH
    exact huH hh
  refine ⟨⟨c⁻¹ • h, D.H.smul_mem _ hh⟩, ?_⟩
  have hxe : ((⟨c⁻¹ • h, D.H.smul_mem _ hh⟩ : D.H) : V) + D.e = c⁻¹ • (h + c • D.e) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hxU : ((⟨c⁻¹ • h, D.H.smul_mem _ hh⟩ : D.H) : V) + D.e ∈ U := by
    rw [hxe]; exact U.smul_mem _ huU
  apply le_antisymm
  · exact sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hxU)
  · intro v hv
    obtain ⟨h', hh', c', rfl⟩ := D.exists_decomp v
    rw [D.mem_liftRep]
    set x : D.H := ⟨c⁻¹ • h, D.H.smul_mem _ hh⟩
    refine ⟨⟨h' - c' • (x : V), D.H.sub_mem hh' (D.H.smul_mem _ x.2)⟩, ?_, c', ?_⟩
    · show h' - c' • (x : V) ∈ U
      have heq : h' - c' • (x : V) = (h' + c' • D.e) - c' • ((x : V) + D.e) := by
        rw [smul_add]; abel
      rw [heq]
      exact U.sub_mem hv (U.smul_mem _ hxU)
    · show h' - c' • (x : V) + c' • ((x : V) + D.e) = h' + c' • D.e
      rw [smul_add]; abel

/-- The forward direction of `lift_le_lift_iff`. -/
theorem cosetLE_of_lift_le (D : HypData K V) {B₁ B₂ : Submodule K D.H} {x₁ : D.H ⧸ B₁}
    {x₂ : D.H ⧸ B₂} (hle : D.lift B₁ x₁ ≤ D.lift B₂ x₂) : cosetLE B₁ B₂ x₁ x₂ := by
  have hB : B₁ ≤ B₂ := by
    have h1 := inf_le_inf_right D.H hle
    rw [lift_inf_H, lift_inf_H] at h1
    exact (Submodule.map_le_map_iff_of_injective D.H.injective_subtype _ _).1 h1
  obtain ⟨a₁, rfl⟩ := Submodule.Quotient.mk_surjective B₁ x₁
  obtain ⟨a₂, rfl⟩ := Submodule.Quotient.mk_surjective B₂ x₂
  refine ⟨hB, a₁, rfl, ?_⟩
  rw [Submodule.Quotient.eq]
  rw [lift_mk, lift_mk] at hle
  have h1 : ((a₁ - a₂ : D.H) : V) ∈ D.liftRep B₂ a₂ ⊓ D.H := by
    refine ⟨?_, (a₁ - a₂).2⟩
    have heq : ((a₁ - a₂ : D.H) : V) = ((a₁ : V) + D.e) - ((a₂ : V) + D.e) := by
      rw [Submodule.coe_sub]; abel
    rw [heq]
    exact Submodule.sub_mem _ (hle (D.add_e_mem_liftRep B₁ a₁)) (D.add_e_mem_liftRep B₂ a₂)
  rw [D.liftRep_inf_H] at h1
  obtain ⟨b, hb, hbeq⟩ := Submodule.mem_map.1 h1
  have hb' : b = a₁ - a₂ := Subtype.ext hbeq
  rw [← hb']
  exact hb

/-- `U(B, x + B)` determines `(B, x + B)`. -/
theorem lift_inj (D : HypData K V) {B₁ B₂ : Submodule K D.H} {x₁ : D.H ⧸ B₁} {x₂ : D.H ⧸ B₂}
    (h : D.lift B₁ x₁ = D.lift B₂ x₂) :
    (⟨B₁, x₁⟩ : Σ B : Submodule K D.H, D.H ⧸ B) = ⟨B₂, x₂⟩ := by
  obtain ⟨hB₁, w, h₁, h₁'⟩ := D.cosetLE_of_lift_le h.le
  obtain ⟨hB₂, -⟩ := D.cosetLE_of_lift_le h.ge
  obtain rfl := le_antisymm hB₁ hB₂
  subst h₁ h₁'
  rfl

/-- **Lemma 2.1**: every subspace not contained in `H` is `U(B, x + B)` for a unique pair. -/
theorem existsUnique_lift (D : HypData K V) (U : Submodule K V) (hU : ¬ U ≤ D.H) :
    ∃! Bx : Σ B : Submodule K D.H, D.H ⧸ B, D.lift Bx.1 Bx.2 = U := by
  obtain ⟨x, hx⟩ := D.exists_lift U hU
  refine ⟨⟨U.comap D.H.subtype, Submodule.Quotient.mk x⟩, hx, ?_⟩
  rintro ⟨B', x'⟩ hBx
  exact D.lift_inj (hBx.trans hx.symm)

/-- **Lemma 2.1**: `U(B₁, x₁ + B₁) ≤ U(B₂, x₂ + B₂)` iff `B₁ ≤ B₂` and `x₁ - x₂ ∈ B₂`. -/
theorem lift_le_lift_iff (D : HypData K V) {B₁ B₂ : Submodule K D.H} {x₁ : D.H ⧸ B₁}
    {x₂ : D.H ⧸ B₂} : D.lift B₁ x₁ ≤ D.lift B₂ x₂ ↔ cosetLE B₁ B₂ x₁ x₂ := by
  refine ⟨D.cosetLE_of_lift_le, ?_⟩
  rintro ⟨hB, w, rfl, rfl⟩
  rw [lift_mk, lift_mk]
  exact sup_le_sup_right (Submodule.map_mono hB) _

/-- An inside subspace lies in `U(B, x + B)` iff it lies in `B`. -/
theorem map_le_lift_iff (D : HypData K V) {B₁ B₂ : Submodule K D.H} {x₂ : D.H ⧸ B₂} :
    B₁.map D.H.subtype ≤ D.lift B₂ x₂ ↔ B₁ ≤ B₂ := by
  rw [← Submodule.map_le_map_iff_of_injective D.H.injective_subtype B₁ B₂, ← D.lift_inf_H B₂ x₂]
  constructor
  · intro h
    exact le_inf h (Submodule.map_subtype_le _ _)
  · intro h
    exact h.trans inf_le_left

/-- The inverse of the split: inside subspaces and crossing subspaces. -/
def splitInv (D : HypData K V) (P P' : ℕ → Prop) (hP : ∀ d, P (d + 1) ↔ P' d) :
    SubP K D.H P ⊕ (Σ B : SubP K D.H P', D.H ⧸ B.1) → SubP K V P
  | .inl U => ⟨U.1.map D.H.subtype, by rw [Submodule.finrank_map_subtype_eq]; exact U.2⟩
  | .inr Bx => ⟨D.lift Bx.1.1 Bx.2, by rw [D.finrank_lift]; exact (hP _).2 Bx.1.2⟩

theorem splitInv_inl_val (D : HypData K V) (P P' : ℕ → Prop)
    (hP : ∀ d, P (d + 1) ↔ P' d) (U : SubP K D.H P) :
    (D.splitInv P P' hP (.inl U)).1 = U.1.map D.H.subtype := rfl

theorem splitInv_inr_val (D : HypData K V) (P P' : ℕ → Prop)
    (hP : ∀ d, P (d + 1) ↔ P' d) (Bx : Σ B : SubP K D.H P', D.H ⧸ B.1) :
    (D.splitInv P P' hP (.inr Bx)).1 = D.lift Bx.1.1 Bx.2 := rfl

theorem splitInv_injective (D : HypData K V) (P P' : ℕ → Prop) (hP : ∀ d, P (d + 1) ↔ P' d) :
    Function.Injective (D.splitInv P P' hP) := by
  rintro (U | ⟨⟨B, hB⟩, x⟩) (U' | ⟨⟨B', hB'⟩, x'⟩) h
  · have h' : U.1.map D.H.subtype = U'.1.map D.H.subtype := congrArg Subtype.val h
    exact congrArg Sum.inl
      (Subtype.ext (Submodule.map_injective_of_injective D.H.injective_subtype h'))
  · have h' : U.1.map D.H.subtype = D.lift B' x' := congrArg Subtype.val h
    exact (D.not_lift_le_H B' x' (by rw [← h']; exact Submodule.map_subtype_le _ _)).elim
  · have h' : D.lift B x = U'.1.map D.H.subtype := congrArg Subtype.val h
    exact (D.not_lift_le_H B x (by rw [h']; exact Submodule.map_subtype_le _ _)).elim
  · have h' : D.lift B x = D.lift B' x' := congrArg Subtype.val h
    have h'' := D.lift_inj h'
    cases h''
    rfl

theorem splitInv_surjective (D : HypData K V) (P P' : ℕ → Prop) (hP : ∀ d, P (d + 1) ↔ P' d) :
    Function.Surjective (D.splitInv P P' hP) := by
  intro U
  by_cases hU : U.1 ≤ D.H
  · have hmap : (U.1.comap D.H.subtype).map D.H.subtype = U.1 := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hU]
    have hP' : P (finrank K (U.1.comap D.H.subtype)) := by
      rw [← Submodule.finrank_map_subtype_eq, hmap]; exact U.2
    exact ⟨.inl ⟨U.1.comap D.H.subtype, hP'⟩, Subtype.ext hmap⟩
  · obtain ⟨⟨B, x⟩, hBx, -⟩ := D.existsUnique_lift U.1 hU
    have hB : P' (finrank K B) := by
      rw [← hP, ← D.finrank_lift B x, hBx]; exact U.2
    exact ⟨.inr ⟨⟨B, hB⟩, x⟩, Subtype.ext hBx⟩

theorem splitInv_bijective (D : HypData K V) (P P' : ℕ → Prop) (hP : ∀ d, P (d + 1) ↔ P' d) :
    Function.Bijective (D.splitInv P P' hP) := by
  exact ⟨D.splitInv_injective P P' hP, D.splitInv_surjective P P' hP⟩

/-- Subspaces of `V` with dimension in `P`: inside ones, and crossing ones `U(B, x + B)` with
`dim B ∈ P'`. -/
noncomputable def split (D : HypData K V) (P P' : ℕ → Prop) (hP : ∀ d, P (d + 1) ↔ P' d) :
    SubP K V P ≃ SubP K D.H P ⊕ (Σ B : SubP K D.H P', D.H ⧸ B.1) :=
  (Equiv.ofBijective _ (D.splitInv_bijective P P' hP)).symm

@[simp] theorem split_symm_apply (D : HypData K V) (P P' : ℕ → Prop)
    (hP : ∀ d, P (d + 1) ↔ P' d) (z : SubP K D.H P ⊕ (Σ B : SubP K D.H P', D.H ⧸ B.1)) :
    (D.split P P' hP).symm z = D.splitInv P P' hP z := rfl

variable {R : Type*} [CommRing R]

open Classical in
/-- The containment transform at any output, split along `D.split P P' hP` into inside and
crossing inputs. -/
theorem containT_eq_split (D : HypData K V) {P P' Q : ℕ → Prop} (hP : ∀ d, P (d + 1) ↔ P' d)
    (f : SubP K V P → R) (W : SubP K V Q) :
    containT P Q f W =
      ∑ U : SubP K D.H P,
          (if U.1.map D.H.subtype ≤ W.1 then f (D.splitInv P P' hP (.inl U)) else 0) +
      ∑ By : (Σ B : SubP K D.H P', D.H ⧸ B.1),
          (if D.lift By.1.1 By.2 ≤ W.1 then f (D.splitInv P P' hP (.inr By)) else 0) := by
  unfold containT
  rw [Finset.sum_filter, ← (D.split P P' hP).symm.sum_comp, Fintype.sum_sum_type]
  rfl

/-- **Equation (cut)/(rank-cut), inside outputs**: they see only inside inputs. -/
theorem containT_split_inl (D : HypData K V) {P P' Q Q' : ℕ → Prop}
    (hP : ∀ d, P (d + 1) ↔ P' d) (hQ : ∀ d, Q (d + 1) ↔ Q' d) (f : SubP K V P → R)
    (W : SubP K D.H Q) :
    containT P Q f ((D.split Q Q' hQ).symm (Sum.inl W)) =
      containT P Q (fun U => f ((D.split P P' hP).symm (Sum.inl U))) W := by
  classical
  rw [containT_eq_split D hP]
  convert add_zero (containT P Q (fun U => f ((D.split P P' hP).symm (Sum.inl U))) W) using 2
  · unfold containT
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun U _ => ?_
    exact if_congr (Submodule.map_le_map_iff_of_injective D.H.injective_subtype _ _) rfl rfl
  · refine Finset.sum_eq_zero fun By _ => ite_eq_right fun hle => ?_
    exact D.not_lift_le_H By.1.1 By.2 (hle.trans (Submodule.map_subtype_le _ _))

/-- **Equation (cut)/(rank-cut), crossing outputs**: the output at `U(D, x + D)` is the inside
transform at `D` plus the affine sum over crossing inputs. -/
theorem containT_split_inr (D : HypData K V) {P P' Q Q' : ℕ → Prop}
    (hP : ∀ d, P (d + 1) ↔ P' d) (hQ : ∀ d, Q (d + 1) ↔ Q' d) (f : SubP K V P → R)
    (Wx : Σ W : SubP K D.H Q', D.H ⧸ W.1) :
    containT P Q f ((D.split Q Q' hQ).symm (Sum.inr Wx)) =
      containT P Q' (fun U => f ((D.split P P' hP).symm (Sum.inl U))) Wx.1 +
        affineT P' Q' (fun By => f ((D.split P P' hP).symm (Sum.inr By))) Wx := by
  classical
  rw [containT_eq_split D hP]
  congr 1
  · unfold containT
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun U _ => if_congr D.map_le_lift_iff rfl rfl
  · unfold affineT
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun By _ => if_congr D.lift_le_lift_iff rfl rfl

end HypData

end Hyperplane

end SubspaceConvolution
