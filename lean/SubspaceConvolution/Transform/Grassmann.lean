/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Defs

/-!
# The Grassmann graph `J_q(n, k)` (Sections 1.3 and 5.3)

* `finrank_inf_le_of_adj` — along an edge `U ~ U'`, `dim(U ∩ W)` drops by at most one.
* `grassGraph_dist` — **the distance formula** `dist(U, W) = k - dim(U ∩ W) = gDist k U W`;
  also `grassGraph_reachable`, `grassGraph_connected` (for `k ≤ n`).
* `exists_linearEquiv_map_pair` — **`GL(V)` is transitive on pairs** of subspaces with the same
  dimensions and the same intersection dimension (decompose `V = (U∩W) ⊕ U₁ ⊕ W₁ ⊕ R₀`).
* `grassMap g` — the action of `g ∈ GL(V)` on `Gr(V, k)`; `gDist_grassMap`,
  `exists_grassMap_pair` (pairs at equal distance lie in one orbit), `exists_grassMap`,
  `exists_gDist_eq` (every distance `i ≤ d = min(k, n-k)` occurs), `gDist_le_min`.
* `invariant_iff_exists_dist` — **Section 5.3**: the `GL(V)`-invariant matrices on `Gr(V, k)`
  are exactly the intersection kernels `K(U, W) = a_{dist(U, W)}`.
* `kernelApply_grassMap` (kernels commute with `GL(V)`), `kernelLin` (a kernel as a linear map).
-/

open Finset Module

set_option linter.unusedSectionVars false

universe u v w

namespace SubspaceConvolution

section Dim

variable {K : Type w} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_grass {k : ℕ} (U : Grass K V k) : finrank K U.1 = k := U.2

theorem grass_eq_of_le {k : ℕ} {U W : Grass K V k} (h : U.1 ≤ W.1) : U = W :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [finrank_grass, finrank_grass]))

theorem finrank_inf_grass_le {k : ℕ} (U : Grass K V k) (W : Submodule K V) :
    finrank K ↥(U.1 ⊓ W) ≤ k := by
  have := Submodule.finrank_mono (inf_le_left : U.1 ⊓ W ≤ U.1)
  rwa [finrank_grass] at this

theorem gDist_self {k : ℕ} (U : Grass K V k) : gDist k U U = 0 := by
  unfold gDist; rw [inf_idem, finrank_grass, Nat.sub_self]

theorem gDist_comm {k : ℕ} (U W : Grass K V k) : gDist k U W = gDist k W U := by
  unfold gDist; rw [inf_comm]

theorem gDist_eq_zero_iff {k : ℕ} {U W : Grass K V k} : gDist k U W = 0 ↔ U = W := by
  constructor
  · intro h
    have h1 := finrank_inf_grass_le U W.1
    unfold gDist at h
    have h2 : finrank K ↥(U.1 ⊓ W.1) = finrank K U.1 := by rw [finrank_grass]; omega
    exact grass_eq_of_le (inf_eq_left.1
      (Submodule.eq_of_le_of_finrank_eq (inf_le_left : U.1 ⊓ W.1 ≤ U.1) h2))
  · rintro rfl; exact gDist_self U

theorem gDist_eq_one_iff {k : ℕ} {U W : Grass K V k} :
    gDist k U W = 1 ↔ (grassGraph k).Adj U W := by
  constructor
  · intro h
    have h1 := finrank_inf_grass_le U W.1
    refine ⟨fun hUW => ?_, by unfold gDist at h; omega⟩
    subst hUW
    rw [gDist_self] at h
    exact absurd h (by decide)
  · rintro ⟨-, h⟩; unfold gDist; omega

/-- Intermediate subspaces of every dimension. -/
theorem exists_between_finrank {A B : Submodule K V} (hAB : A ≤ B) {m : ℕ}
    (h1 : finrank K A ≤ m) (h2 : m ≤ finrank K B) :
    ∃ C : Submodule K V, A ≤ C ∧ C ≤ B ∧ finrank K C = m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
  induction t with
  | zero => exact ⟨A, le_rfl, hAB, rfl⟩
  | succ t ih =>
    obtain ⟨C, hAC, hCB, hC⟩ := ih (by omega) (by omega)
    have hlt : C < B := lt_of_le_of_ne hCB (fun h => by rw [h] at hC; omega)
    obtain ⟨x, hxB, hxC⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨C ⊔ K ∙ x, le_sup_of_le_left hAC,
      sup_le hCB ((Submodule.span_singleton_le_iff_mem _ _).2 hxB), ?_⟩
    rw [Submodule.finrank_sup_span_singleton hxC, hC, add_assoc]

theorem nonempty_grass {k : ℕ} (hk : k ≤ finrank K V) : Nonempty (Grass K V k) := by
  obtain ⟨C, -, -, hC⟩ := exists_between_finrank (bot_le : (⊥ : Submodule K V) ≤ ⊤) (m := k)
    (by simp) (by simpa using hk)
  exact ⟨⟨C, hC⟩⟩

theorem le_finrank_of_grass {k : ℕ} (U : Grass K V k) : k ≤ finrank K V := by
  rw [← finrank_grass U]; exact Submodule.finrank_le _

end Dim

/-! ### The distance formula -/

section Distance

variable {K : Type w} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Along an edge, the intersection dimension with a fixed subspace drops by at most one. -/
theorem finrank_inf_le_of_adj {k : ℕ} {U U' : Grass K V k} (h : (grassGraph k).Adj U U')
    (W : Submodule K V) :
    finrank K ↥(U.1 ⊓ W) ≤ finrank K ↥(U'.1 ⊓ W) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U.1 ⊓ W) (U.1 ⊓ U'.1)
  have h2 : finrank K ↥((U.1 ⊓ W) ⊔ (U.1 ⊓ U'.1)) ≤ k := by
    have := Submodule.finrank_mono (sup_le inf_le_left inf_le_left :
      (U.1 ⊓ W) ⊔ (U.1 ⊓ U'.1) ≤ U.1)
    rwa [finrank_grass] at this
  have h3 : finrank K ↥((U.1 ⊓ W) ⊓ (U.1 ⊓ U'.1)) ≤ finrank K ↥(U'.1 ⊓ W) :=
    Submodule.finrank_mono
      (le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right))
  have h4 := h.2
  omega

/-- Lower bound: every walk from `U` to `W` has length at least `k - dim(U ∩ W)`. -/
theorem le_finrank_inf_add_length {k : ℕ} {U W : Grass K V k} (p : (grassGraph k).Walk U W) :
    k ≤ finrank K ↥(U.1 ⊓ W.1) + p.length := by
  induction p with
  | nil => rw [SimpleGraph.Walk.length_nil, inf_idem, finrank_grass]; omega
  | @cons U U' W h p ih =>
    have := finrank_inf_le_of_adj h.symm W.1
    rw [SimpleGraph.Walk.length_cons]
    omega

theorem gDist_le_length {k : ℕ} {U W : Grass K V k} (p : (grassGraph k).Walk U W) :
    gDist k U W ≤ p.length := by
  have := le_finrank_inf_add_length p
  unfold gDist; omega

/-- One step towards `W`: replace a vector of `U` outside `U ∩ W` by a vector of `W`. -/
theorem exists_adj_step {k : ℕ} {U W : Grass K V k} (hUW : U ≠ W) :
    ∃ U' : Grass K V k, (grassGraph k).Adj U U' ∧
      finrank K ↥(U'.1 ⊓ W.1) = finrank K ↥(U.1 ⊓ W.1) + 1 := by
  have hWU : ¬ W.1 ≤ U.1 := fun h => hUW (grass_eq_of_le h).symm
  obtain ⟨x, hxW, hxU⟩ := IsConcreteLE.not_le_iff_exists.1 hWU
  have hlt : U.1 ⊓ W.1 < U.1 :=
    lt_of_le_of_ne inf_le_left fun h => hUW (grass_eq_of_le (inf_eq_left.1 h))
  have hrk := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_grass] at hrk
  obtain ⟨H, hIH, hHU, hH⟩ := exists_between_finrank hlt.le (m := k - 1) (by omega)
    (by rw [finrank_grass]; omega)
  have hxH : x ∉ H := fun h => hxU (hHU h)
  have hU'k : finrank K ↥(H ⊔ K ∙ x) = k := by
    rw [Submodule.finrank_sup_span_singleton hxH, hH]; omega
  let U' : Grass K V k := ⟨H ⊔ K ∙ x, hU'k⟩
  have hxU' : x ∈ U'.1 := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hadj : (grassGraph k).Adj U U' := by
    refine ⟨fun h => hxU (by rw [h]; exact hxU'), ?_⟩
    have h1 : H ≤ U.1 ⊓ U'.1 := le_inf hHU le_sup_left
    have h2 : U.1 ⊓ U'.1 < U'.1 :=
      lt_of_le_of_ne inf_le_right fun h => hxU ((inf_eq_right.1 h) hxU')
    have h3 := Submodule.finrank_mono h1
    have h4 := Submodule.finrank_lt_finrank_of_lt h2
    rw [hH] at h3
    rw [show finrank K U'.1 = k from hU'k] at h4
    omega
  refine ⟨U', hadj, le_antisymm (finrank_inf_le_of_adj hadj.symm W.1) ?_⟩
  have hx' : x ∉ U.1 ⊓ W.1 := fun h => hxU (Submodule.mem_inf.1 h).1
  rw [← Submodule.finrank_sup_span_singleton hx']
  refine Submodule.finrank_mono (sup_le (le_inf (hIH.trans le_sup_left) inf_le_right) ?_)
  rw [Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_inf.2 ⟨hxU', hxW⟩

/-- Upper bound: a walk of length `k - dim(U ∩ W)`. -/
theorem exists_walk_length_eq_gDist {k : ℕ} (U W : Grass K V k) :
    ∃ p : (grassGraph k).Walk U W, p.length = gDist k U W := by
  induction' h : gDist k U W using Nat.strong_induction_on with m ih generalizing U
  by_cases hUW : U = W
  · subst hUW
    exact ⟨SimpleGraph.Walk.nil, by rw [← h, gDist_self]; rfl⟩
  · obtain ⟨U', hadj, hU'⟩ := exists_adj_step hUW
    have hd : gDist k U' W + 1 = m := by
      have h2 := finrank_inf_grass_le U' W.1
      rw [← h]; unfold gDist; omega
    obtain ⟨p, hp⟩ := ih (gDist k U' W) (by omega) U' rfl
    exact ⟨SimpleGraph.Walk.cons hadj p, by rw [SimpleGraph.Walk.length_cons, hp, hd]⟩

theorem grassGraph_reachable {k : ℕ} (U W : Grass K V k) : (grassGraph k).Reachable U W :=
  (exists_walk_length_eq_gDist U W).elim fun p _ => ⟨p⟩

/-- **The distance formula**: `dist(U, W) = k - dim(U ∩ W)`. -/
theorem grassGraph_dist {k : ℕ} (U W : Grass K V k) :
    (grassGraph k).dist U W = gDist k U W := by
  obtain ⟨p, hp⟩ := exists_walk_length_eq_gDist U W
  refine le_antisymm (hp ▸ SimpleGraph.dist_le p) ?_
  obtain ⟨q, hq⟩ := (grassGraph_reachable U W).exists_walk_length_eq_dist
  exact hq ▸ gDist_le_length q

theorem grassGraph_preconnected (k : ℕ) : (grassGraph (K := K) (V := V) k).Preconnected :=
  grassGraph_reachable

theorem grassGraph_connected {k : ℕ} (hk : k ≤ finrank K V) :
    (grassGraph (K := K) (V := V) k).Connected := by
  have := nonempty_grass (K := K) (V := V) hk
  exact ⟨grassGraph_preconnected k⟩

/-- The diameter: `dist(U, W) ≤ d = min(k, n - k)`. -/
theorem gDist_le_min {k : ℕ} (U W : Grass K V k) : gDist k U W ≤ min k (finrank K V - k) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U.1 W.1
  have h2 := Submodule.finrank_le (U.1 ⊔ W.1)
  rw [finrank_grass, finrank_grass] at h1
  unfold gDist
  omega

end Distance

/-! ### Transitivity of `GL(V)` on pairs -/

section Transitive

variable {K : Type w} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A complement of `I` inside `U ≥ I`. -/
theorem exists_relCompl {I U : Submodule K V} (h : I ≤ U) :
    ∃ U₁ : Submodule K V, I ⊔ U₁ = U ∧ finrank K I + finrank K U₁ = finrank K U := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl I
  have h1 : I ⊔ C ⊓ U = U := by rw [← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]
  have h2 : I ⊓ (C ⊓ U) = ⊥ := by
    rw [eq_bot_iff, ← hC.inf_eq_bot]; exact inf_le_inf_left I inf_le_left
  refine ⟨C ⊓ U, h1, ?_⟩
  have := Submodule.finrank_sup_add_finrank_inf_eq I (C ⊓ U)
  rw [h1, h2, finrank_bot] at this
  omega

/-- `V = (U ∩ W) ⊕ U₁ ⊕ W₁ ⊕ R₀` with `U = (U ∩ W) ⊕ U₁`, `W = (U ∩ W) ⊕ W₁`. -/
theorem exists_pair_decomp (U W : Submodule K V) :
    ∃ U₁ W₁ R₀ : Submodule K V, (U ⊓ W) ⊔ U₁ = U ∧ (U ⊓ W) ⊔ W₁ = W ∧ (U ⊔ W) ⊔ R₀ = ⊤ ∧
      finrank K ↥(U ⊓ W) + finrank K U₁ = finrank K U ∧
      finrank K ↥(U ⊓ W) + finrank K W₁ = finrank K W ∧
      finrank K ↥(U ⊔ W) + finrank K R₀ = finrank K V := by
  obtain ⟨U₁, h1, h2⟩ := exists_relCompl (inf_le_left : U ⊓ W ≤ U)
  obtain ⟨W₁, h3, h4⟩ := exists_relCompl (inf_le_right : U ⊓ W ≤ W)
  obtain ⟨R₀, hR⟩ := Submodule.exists_isCompl (U ⊔ W)
  exact ⟨U₁, W₁, R₀, h1, h3, hR.sup_eq_top, h2, h4, Submodule.finrank_add_eq_of_isCompl hR⟩

theorem pair_decomp_sup_eq_top {U W U₁ W₁ R₀ : Submodule K V} (h1 : (U ⊓ W) ⊔ U₁ = U)
    (h2 : (U ⊓ W) ⊔ W₁ = W) (h3 : (U ⊔ W) ⊔ R₀ = ⊤) :
    (U ⊓ W) ⊔ (U₁ ⊔ (W₁ ⊔ R₀)) = ⊤ := by
  rw [eq_top_iff, ← h3]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (le_of_eq h1.symm).trans (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  · exact (le_of_eq h2.symm).trans
      (sup_le le_sup_left (le_sup_left.trans (le_sup_right.trans le_sup_right)))
  · exact le_sup_right.trans (le_sup_right.trans le_sup_right)

/-- The sum map `A × B × C × D → V` is an isomorphism when the pieces span and the dimensions
add up. -/
noncomputable def sumEquiv4 (A B C D : Submodule K V) (htop : A ⊔ (B ⊔ (C ⊔ D)) = ⊤)
    (hdim : finrank K A + (finrank K B + (finrank K C + finrank K D)) = finrank K V) :
    (A × B × C × D) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (A.subtype.coprod (B.subtype.coprod (C.subtype.coprod D.subtype))) (by
    have hsurj : Function.Surjective
        (A.subtype.coprod (B.subtype.coprod (C.subtype.coprod D.subtype))) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_coprod, LinearMap.range_coprod,
        LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
        Submodule.range_subtype, Submodule.range_subtype, htop]
    refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj, hsurj⟩
    simp only [Module.finrank_prod, hdim])

theorem sumEquiv4_apply (A B C D : Submodule K V) (htop : A ⊔ (B ⊔ (C ⊔ D)) = ⊤)
    (hdim : finrank K A + (finrank K B + (finrank K C + finrank K D)) = finrank K V)
    (p : A × B × C × D) :
    sumEquiv4 A B C D htop hdim p =
      (p.1 : V) + ((p.2.1 : V) + ((p.2.2.1 : V) + (p.2.2.2 : V))) := rfl

/-- **Transitivity of `GL(V)` on pairs**: pairs of subspaces with the same dimensions and the
same intersection dimension are in one orbit. -/
theorem exists_linearEquiv_map_pair {U W U' W' : Submodule K V}
    (hU : finrank K U = finrank K U') (hW : finrank K W = finrank K W')
    (hI : finrank K ↥(U ⊓ W) = finrank K ↥(U' ⊓ W')) :
    ∃ g : V ≃ₗ[K] V, U.map (g : V →ₗ[K] V) = U' ∧ W.map (g : V →ₗ[K] V) = W' := by
  obtain ⟨U₁, W₁, R₀, hU₁, hW₁, hR₀, dU₁, dW₁, dR₀⟩ := exists_pair_decomp U W
  obtain ⟨U₁', W₁', R₀', hU₁', hW₁', hR₀', dU₁', dW₁', dR₀'⟩ := exists_pair_decomp U' W'
  have hS := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hS' := Submodule.finrank_sup_add_finrank_inf_eq U' W'
  let φ := sumEquiv4 (U ⊓ W) U₁ W₁ R₀ (pair_decomp_sup_eq_top hU₁ hW₁ hR₀) (by omega)
  let φ' := sumEquiv4 (U' ⊓ W') U₁' W₁' R₀' (pair_decomp_sup_eq_top hU₁' hW₁' hR₀') (by omega)
  have d₂ : finrank K U₁ = finrank K U₁' := by omega
  have d₃ : finrank K W₁ = finrank K W₁' := by omega
  have d₄ : finrank K R₀ = finrank K R₀' := by omega
  let e₁ := LinearEquiv.ofFinrankEq _ _ hI
  let e₂ := LinearEquiv.ofFinrankEq U₁ U₁' d₂
  let e₃ := LinearEquiv.ofFinrankEq W₁ W₁' d₃
  let e₄ := LinearEquiv.ofFinrankEq R₀ R₀' d₄
  let g : V ≃ₗ[K] V := φ.symm ≪≫ₗ (e₁.prodCongr (e₂.prodCongr (e₃.prodCongr e₄))) ≪≫ₗ φ'
  have hg : ∀ p, g (φ p) = φ' (e₁ p.1, e₂ p.2.1, e₃ p.2.2.1, e₄ p.2.2.2) := by
    intro p
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hUle : U.map (g : V →ₗ[K] V) ≤ U' := by
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [← hU₁] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hx' : y + z = φ (⟨y, hy⟩, ⟨z, hz⟩, 0, 0) := by
      rw [sumEquiv4_apply]; simp
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, hx', hg, sumEquiv4_apply]
    simp only [map_zero, ZeroMemClass.coe_zero, add_zero]
    refine add_mem ?_ ?_
    · exact (Submodule.mem_inf.1 (e₁ ⟨y, hy⟩).2).1
    · rw [← hU₁']; exact Submodule.mem_sup_right (e₂ ⟨z, hz⟩).2
  have hWle : W.map (g : V →ₗ[K] V) ≤ W' := by
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [← hW₁] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hx' : y + z = φ (⟨y, hy⟩, 0, ⟨z, hz⟩, 0) := by
      rw [sumEquiv4_apply]; simp
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, hx', hg, sumEquiv4_apply]
    simp only [map_zero, ZeroMemClass.coe_zero, add_zero, zero_add]
    refine add_mem ?_ ?_
    · exact (Submodule.mem_inf.1 (e₁ ⟨y, hy⟩).2).2
    · rw [← hW₁']; exact Submodule.mem_sup_right (e₃ ⟨z, hz⟩).2
  exact ⟨g, Submodule.eq_of_le_of_finrank_eq hUle (by rw [LinearEquiv.finrank_map_eq, hU]),
    Submodule.eq_of_le_of_finrank_eq hWle (by rw [LinearEquiv.finrank_map_eq, hW])⟩

end Transitive

/-! ### The action on `Gr(V, k)` -/

section Action

variable {K : Type w} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The action of `g ∈ GL(V)` on `Gr(V, k)`. -/
def grassMap {k : ℕ} (g : V ≃ₗ[K] V) (U : Grass K V k) : Grass K V k :=
  ⟨U.1.map (g : V →ₗ[K] V), by
    show finrank K _ = k
    rw [LinearEquiv.finrank_map_eq]; exact U.2⟩

@[simp] theorem grassMap_val {k : ℕ} (g : V ≃ₗ[K] V) (U : Grass K V k) :
    (grassMap g U).1 = U.1.map (g : V →ₗ[K] V) := rfl

theorem grassMap_symm_grassMap {k : ℕ} (g : V ≃ₗ[K] V) (U : Grass K V k) :
    grassMap g.symm (grassMap g U) = U := by
  apply Subtype.ext
  ext x
  simp [Submodule.mem_map_equiv]

/-- `grassMap g` as a permutation of `Gr(V, k)`. -/
def grassMapEquiv {k : ℕ} (g : V ≃ₗ[K] V) : Grass K V k ≃ Grass K V k where
  toFun := grassMap g
  invFun := grassMap g.symm
  left_inv := grassMap_symm_grassMap g
  right_inv U := by simpa using grassMap_symm_grassMap g.symm U

@[simp] theorem grassMapEquiv_apply {k : ℕ} (g : V ≃ₗ[K] V) (U : Grass K V k) :
    grassMapEquiv g U = grassMap g U := rfl

/-- Distances are `GL(V)`-invariant. -/
theorem gDist_grassMap {k : ℕ} (g : V ≃ₗ[K] V) (U W : Grass K V k) :
    gDist k (grassMap g U) (grassMap g W) = gDist k U W := by
  unfold gDist
  rw [grassMap_val, grassMap_val, ← Submodule.map_inf _ g.injective, LinearEquiv.finrank_map_eq]

theorem finrank_inf_eq_of_gDist_eq {k : ℕ} {U W U' W' : Grass K V k}
    (h : gDist k U W = gDist k U' W') :
    finrank K ↥(U.1 ⊓ W.1) = finrank K ↥(U'.1 ⊓ W'.1) := by
  have h1 := finrank_inf_grass_le U W.1
  have h2 := finrank_inf_grass_le U' W'.1
  unfold gDist at h; omega

/-- Pairs at the same distance lie in one `GL(V)`-orbit. -/
theorem exists_grassMap_pair {k : ℕ} {U W U' W' : Grass K V k}
    (h : gDist k U W = gDist k U' W') :
    ∃ g : V ≃ₗ[K] V, grassMap g U = U' ∧ grassMap g W = W' := by
  obtain ⟨g, hgU, hgW⟩ := exists_linearEquiv_map_pair
    (by rw [finrank_grass U, finrank_grass U']) (by rw [finrank_grass W, finrank_grass W'])
    (finrank_inf_eq_of_gDist_eq h)
  exact ⟨g, Subtype.ext hgU, Subtype.ext hgW⟩

/-- `GL(V)` is transitive on `Gr(V, k)`. -/
theorem exists_grassMap {k : ℕ} (U U' : Grass K V k) : ∃ g : V ≃ₗ[K] V, grassMap g U = U' := by
  obtain ⟨g, h, -⟩ := exists_grassMap_pair (U := U) (W := U) (U' := U') (W' := U')
    (by rw [gDist_self, gDist_self])
  exact ⟨g, h⟩

/-- Every distance `i ≤ min(k, n - k)` from a fixed `E` occurs. -/
theorem exists_gDist_eq {k : ℕ} (E : Grass K V k) {i : ℕ} (hi : i ≤ min k (finrank K V - k)) :
    ∃ U : Grass K V k, gDist k U E = i := by
  have hE := finrank_grass E
  obtain ⟨E₀, -, hE₀E, hE₀⟩ := exists_between_finrank (bot_le : ⊥ ≤ E.1) (m := k - i)
    (by simp) (by omega)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl E.1
  have hCdim := Submodule.finrank_add_eq_of_isCompl hC
  obtain ⟨C₀, -, hC₀C, hC₀⟩ := exists_between_finrank (bot_le : ⊥ ≤ C) (m := i)
    (by simp) (by omega)
  have hdisj : E₀ ⊓ C₀ = ⊥ := by
    rw [eq_bot_iff, ← hC.inf_eq_bot]; exact inf_le_inf hE₀E hC₀C
  have hinf : (E₀ ⊔ C₀) ⊓ E.1 = E₀ := by
    rw [sup_inf_assoc_of_le C₀ hE₀E]
    have : C₀ ⊓ E.1 = ⊥ := by
      rw [eq_bot_iff, ← hC.inf_eq_bot, inf_comm]; exact inf_le_inf_left E.1 hC₀C
    rw [this, sup_bot_eq]
  have hdim : finrank K ↥(E₀ ⊔ C₀) = k := by
    have := Submodule.finrank_sup_add_finrank_inf_eq E₀ C₀
    rw [hdisj, finrank_bot] at this
    omega
  refine ⟨⟨E₀ ⊔ C₀, hdim⟩, ?_⟩
  unfold gDist
  rw [show ((⟨E₀ ⊔ C₀, hdim⟩ : Grass K V k).1 ⊓ E.1) = E₀ from hinf, hE₀]
  omega

/-- **Section 5.3**: the `GL(V)`-invariant matrices on `Gr(V, k)` are exactly the intersection
kernels. -/
theorem invariant_iff_exists_dist {R : Type u} [Nonempty R] {k : ℕ}
    (A : Grass K V k → Grass K V k → R) :
    (∀ (g : V ≃ₗ[K] V) (U W : Grass K V k), A (grassMap g U) (grassMap g W) = A U W) ↔
      ∃ a : ℕ → R, ∀ U W, A U W = a (gDist k U W) := by
  classical
  constructor
  · intro hA
    refine ⟨fun j => if h : ∃ p : Grass K V k × Grass K V k, gDist k p.1 p.2 = j then
      A h.choose.1 h.choose.2 else Classical.arbitrary R, fun U W => ?_⟩
    have h : ∃ p : Grass K V k × Grass K V k, gDist k p.1 p.2 = gDist k U W := ⟨(U, W), rfl⟩
    beta_reduce
    rw [dite_eq_left h]
    obtain ⟨g, hgU, hgW⟩ := exists_grassMap_pair h.choose_spec
    calc A U W = A (grassMap g h.choose.1) (grassMap g h.choose.2) := by rw [hgU, hgW]
      _ = A h.choose.1 h.choose.2 := hA g _ _
  · rintro ⟨a, ha⟩ g U W
    rw [ha, ha, gDist_grassMap]

end Action

/-! ### Kernels: invariance and linearity -/

section Kernel

variable {K : Type w} [Field K] [Fintype K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {R : Type u} [CommRing R]

/-- Intersection kernels commute with `GL(V)`. -/
theorem kernelApply_grassMap (k : ℕ) (a : ℕ → R) (f : Grass K V k → R) (g : V ≃ₗ[K] V)
    (U : Grass K V k) :
    kernelApply k a f (grassMap g U) = kernelApply k a (fun W => f (grassMap g W)) U := by
  unfold kernelApply
  rw [← (grassMapEquiv g).sum_comp]
  refine Fintype.sum_congr _ _ fun W => ?_
  rw [grassMapEquiv_apply, gDist_grassMap]

theorem kernelApply_add (k : ℕ) (a : ℕ → R) (f f' : Grass K V k → R) :
    kernelApply k a (f + f') = kernelApply k a f + kernelApply k a f' := by
  funext U
  simp [kernelApply, mul_add, Finset.sum_add_distrib]

theorem kernelApply_smul (k : ℕ) (a : ℕ → R) (c : R) (f : Grass K V k → R) :
    kernelApply k a (c • f) = c • kernelApply k a f := by
  funext U
  simp [kernelApply, Finset.mul_sum, mul_left_comm]

variable (K V) in
/-- An intersection kernel as a linear endomorphism of `R^{Gr(V, k)}`. -/
noncomputable def kernelLin (k : ℕ) (a : ℕ → R) : Module.End R (Grass K V k → R) where
  toFun := kernelApply k a
  map_add' := kernelApply_add k a
  map_smul' := kernelApply_smul k a

@[simp] theorem kernelLin_apply (k : ℕ) (a : ℕ → R) (f : Grass K V k → R) :
    kernelLin K V k a f = kernelApply k a f := rfl

end Kernel

end SubspaceConvolution
