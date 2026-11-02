/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# Lemma 7.1: compatibility and the parent profile

Let `X₁, X₂` be disjoint vertex sets, `X = X₁ ∪ X₂` and `Y = V \ X`.  Vectors of `W_{X_i}` are
represented as combinations `∑_{x ∈ X_i} a_x A_G[x, V \ X_i]ᵀ` (`combo`).  The paper's bilinear
form `β : W₁ × W₂ → F₂` is `β(u, v) = ∑_{x ∈ X₁, y ∈ X₂} a_x b_y A_G[x, y]` for representations
`u = combo a`, `v = combo b` (`bilin`); `bilin_congr_left`/`bilin_congr_right` show that it does
not depend on the representations ("Changing either representation adds a combination vanishing
on the opposite child, so β is well-defined").

`Compatible G X₁ X₂ U V` says that `β` vanishes on `U × V`.

* `compatible_profile_iff` — classes `C₁ ⊆ X₁`, `C₂ ⊆ X₂` can share a color (no edges between
  them) iff `β(U_{X₁}(C₁), U_{X₂}(C₂)) = {0}`;
* `profile_eq_map` — a class `C ⊆ X₁` has parent profile `π₁(U_{X₁}(C))`, where `π₁` restricts to
  `Y` (`restrictOut X`);
* `profile_union` — the union of two classes has profile `π₁(U) + π₂(V)`.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restriction of a vector of `F₂^V` to the coordinates outside `X` (zero on `X`). -/
def restrictOut (X : Finset V) : (V → F2) →ₗ[F2] (V → F2) where
  toFun v y := if y ∈ X then 0 else v y
  map_add' v w := by
    funext y
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem restrictOut_apply (X : Finset V) (v : V → F2) (y : V) :
    restrictOut X v y = if y ∈ X then 0 else v y := rfl

theorem restrictOut_cutRow {M : Matrix V V F2} {X₁ X : Finset V} (h : X₁ ⊆ X) (x : V) :
    restrictOut X (cutRow M X₁ x) = cutRow M X x := by
  funext y
  simp only [restrictOut_apply, cutRow_apply]
  by_cases hy : y ∈ X
  · simp [hy]
  · have : y ∉ X₁ := fun h' => hy (h h')
    simp [hy, this]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A class `C ⊆ X₁ ⊆ X` has parent profile `π(U_{X₁}(C))`. -/
theorem profile_eq_map {X₁ X C : Finset V} (h : X₁ ⊆ X) :
    profile G X C = (profile G X₁ C).map (restrictOut X) := by
  unfold profile
  rw [Submodule.map_span, ← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro x _
  simp [restrictOut_cutRow h]

/-- The profile of a union of classes is the sum of the profiles. -/
theorem profile_union (X C₁ C₂ : Finset V) :
    profile G X (C₁ ∪ C₂) = profile G X C₁ ⊔ profile G X C₂ := by
  unfold profile
  rw [coe_union, Set.image_union, Submodule.span_union]

theorem profile_empty (X : Finset V) : profile G X ∅ = ⊥ := by
  simp [profile]

/-! ### The bilinear form `β` -/

section Bilinear

variable (X₁ X₂ : Finset V)

/-- The vector `∑_{x ∈ X} a_x A_G[x, V \ X]ᵀ` of `W_X` represented by coefficients `a`. -/
def combo (X : Finset V) (a : V → F2) : V → F2 :=
  ∑ x ∈ X, a x • cutRow (G.adjMatrix F2) X x

/-- `β` on representations: `∑_{x ∈ X₁, y ∈ X₂} a_x b_y A_G[x, y]`. -/
def bilin (a b : V → F2) : F2 :=
  ∑ x ∈ X₁, ∑ y ∈ X₂, a x * b y * G.adjMatrix F2 x y

variable {X₁ X₂}

theorem combo_apply_of_not_mem {X : Finset V} (a : V → F2) {y : V} (hy : y ∉ X) :
    combo G X a y = ∑ x ∈ X, a x * G.adjMatrix F2 x y := by
  simp [combo, Finset.sum_apply, cutRow_apply, hy]

theorem combo_sub (X : Finset V) (a a' : V → F2) :
    combo G X (a - a') = combo G X a - combo G X a' := by
  simp [combo, sub_smul, Finset.sum_sub_distrib]

/-- `β(u, v) = ∑_{y ∈ X₂} b_y u_y` with `u = combo a`. -/
theorem bilin_eq_sum_right (hd : Disjoint X₁ X₂) (a b : V → F2) :
    bilin G X₁ X₂ a b = ∑ y ∈ X₂, b y * combo G X₁ a y := by
  unfold bilin
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y hy => ?_
  rw [combo_apply_of_not_mem G a (disjoint_right.1 hd hy), Finset.mul_sum]
  refine sum_congr rfl fun x _ => ?_
  ring

/-- `β(u, v) = ∑_{x ∈ X₁} a_x v_x` with `v = combo b`. -/
theorem bilin_eq_sum_left (hd : Disjoint X₁ X₂) (a b : V → F2) :
    bilin G X₁ X₂ a b = ∑ x ∈ X₁, a x * combo G X₂ b x := by
  unfold bilin
  refine sum_congr rfl fun x hx => ?_
  rw [combo_apply_of_not_mem G b (disjoint_left.1 hd hx), Finset.mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [G.adjMatrix_apply, G.adjMatrix_apply]
  by_cases hxy : G.Adj x y
  · simp [hxy, hxy.symm]
  · have : ¬ G.Adj y x := fun h => hxy h.symm
    simp [hxy, this]

/-- Well-definedness of `β` in the first argument. -/
theorem bilin_congr_left (hd : Disjoint X₁ X₂) {a a' : V → F2}
    (h : combo G X₁ a = combo G X₁ a') (b : V → F2) :
    bilin G X₁ X₂ a b = bilin G X₁ X₂ a' b := by
  rw [bilin_eq_sum_right G hd, bilin_eq_sum_right G hd, h]

/-- Well-definedness of `β` in the second argument. -/
theorem bilin_congr_right (hd : Disjoint X₁ X₂) (a : V → F2) {b b' : V → F2}
    (h : combo G X₂ b = combo G X₂ b') :
    bilin G X₁ X₂ a b = bilin G X₁ X₂ a b' := by
  rw [bilin_eq_sum_left G hd, bilin_eq_sum_left G hd, h]

variable (X₁ X₂)

/-- `β` vanishes on `U × V`: the compatibility relation between left and right profiles. -/
def Compatible (U W : Submodule F2 (V → F2)) : Prop :=
  ∀ a b : V → F2, combo G X₁ a ∈ U → combo G X₂ b ∈ W → bilin G X₁ X₂ a b = 0

variable {X₁ X₂}

/-- Every vector of a profile `U_X(C)`, `C ⊆ X`, is represented by coefficients supported on
`C`. -/
theorem exists_rep_of_mem_profile {X C : Finset V} (hC : C ⊆ X) {a : V → F2}
    (ha : combo G X a ∈ profile G X C) :
    ∃ a' : V → F2, (∀ x, x ∉ C → a' x = 0) ∧ combo G X a' = combo G X a := by
  unfold profile at ha
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun F2).1 ha
  refine ⟨fun x => if h : x ∈ C then c ⟨x, h⟩ else 0, fun x hx => by simp [hx], ?_⟩
  rw [← hc]
  unfold combo
  rw [← sum_subset hC]
  · rw [← sum_coe_sort C]
    refine Fintype.sum_congr _ _ fun x => ?_
    simp
  · intro x _ hx
    simp [hx]

/-- **Lemma 7.1 (compatibility).** Classes `C₁ ⊆ X₁` and `C₂ ⊆ X₂` have no edges between them
iff `β` vanishes on their profiles. -/
theorem compatible_profile_iff (hd : Disjoint X₁ X₂) {C₁ C₂ : Finset V} (h₁ : C₁ ⊆ X₁)
    (h₂ : C₂ ⊆ X₂) :
    Compatible G X₁ X₂ (profile G X₁ C₁) (profile G X₂ C₂) ↔
      ∀ x ∈ C₁, ∀ y ∈ C₂, ¬ G.Adj x y := by
  constructor
  · intro hc x hx y hy hxy
    have hcx : combo G X₁ (Pi.single x 1) = cutRow (G.adjMatrix F2) X₁ x := by
      unfold combo
      rw [sum_eq_single x]
      · simp
      · intro z _ hz
        simp [hz]
      · intro hx'
        exact absurd (h₁ hx) hx'
    have hcy : combo G X₂ (Pi.single y 1) = cutRow (G.adjMatrix F2) X₂ y := by
      unfold combo
      rw [sum_eq_single y]
      · simp
      · intro z _ hz
        simp [hz]
      · intro hy'
        exact absurd (h₂ hy) hy'
    have := hc (Pi.single x 1) (Pi.single y 1)
      (hcx ▸ Submodule.subset_span ⟨x, hx, rfl⟩) (hcy ▸ Submodule.subset_span ⟨y, hy, rfl⟩)
    unfold bilin at this
    rw [sum_eq_single x, sum_eq_single y] at this
    · simp [hxy] at this
    · intro z _ hz
      simp [hz]
    · intro hy'
      exact absurd (h₂ hy) hy'
    · intro z _ hz
      simp [hz]
    · intro hx'
      exact absurd (h₁ hx) hx'
  · intro hno a b ha hb
    obtain ⟨a', ha'0, ha'⟩ := exists_rep_of_mem_profile G h₁ ha
    obtain ⟨b', hb'0, hb'⟩ := exists_rep_of_mem_profile G h₂ hb
    rw [bilin_congr_left G hd ha'.symm, bilin_congr_right G hd a' hb'.symm]
    unfold bilin
    refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
    by_cases hx : x ∈ C₁
    · by_cases hy : y ∈ C₂
      · simp [hno x hx y hy]
      · simp [hb'0 y hy]
    · simp [ha'0 x hx]

end Bilinear

end SubspaceConvolution
