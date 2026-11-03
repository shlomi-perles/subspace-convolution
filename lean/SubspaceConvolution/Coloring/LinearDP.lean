/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.ChromaticPolynomial

/-!
# Corollary 1: the dynamic program on a linear layout

On a linear layout, adding one vertex `x` to a prefix `X` updates one histogram at a time.  With
`R = V \ (X ∪ {x})`, `π` the restriction to `R`, `b = A_G[x, R]ᵀ` and `ℓ` evaluating the
`x`-coordinate, the paper's transitions are

* (eq. 21)  `h ↦ π_* h + δ_{span b}`, weight `1`;
* (eq. 22)  `h ↦ π_*(h - δ_U) + δ_{π(U) + span b}` if `h(U) > 0` and `ℓ(U) = {0}`, weight `h(U)`.

`linStep` implements one step, `linDP` the whole layout.  We prove (`hists_insert`) that one step
maps the histograms of all color partitions of `G[X]` to those of `G[X ∪ {x}]`, by specializing the
merge recurrence of Theorem 6 to a singleton right child (`MergeData.run_single`), and hence
(`linDP_eq_hists`) that the dynamic program along any linear layout returns the histograms of all
color partitions of `G`.  The outputs (chromatic polynomial, chromatic number) follow as in
Theorem 6 (`chromaticPolynomial_eq_linDP`, `chromaticNumber_eq_linDP`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

/-! ### The merge recurrence with a single right class -/

namespace MergeData

variable {P₁ P₂ Q : Type*} (D : MergeData P₁ P₂ Q) [DecidableEq P₂] [DecidableRel D.compat]

theorem run_zero (us : List P₁) (H : Multiset Q) :
    D.run us 0 H = {H + (us : Multiset P₁).map D.left} := by
  induction us generalizing H with
  | nil => simp
  | cons u us ih =>
    rw [run_cons, ih]
    simp only [Multiset.toFinset_zero, filter_empty, sum_empty, add_zero]
    congr 1
    rw [← Multiset.cons_coe, Multiset.map_cons, Multiset.add_cons, Multiset.cons_add]

variable [DecidableEq P₁]

/-- With a single right class of profile `W`, the merge recurrence either leaves every left class
separate, or pairs `W` with one compatible left class, chosen with multiplicity. -/
theorem run_single (L : List P₁) (W : P₂) (H : Multiset Q) :
    D.run L {W} H = {H + (L : Multiset P₁).map D.left + {D.right W}} +
      ∑ U ∈ (L : Multiset P₁).toFinset.filter (fun U => D.compat U W),
        (L : Multiset P₁).count U •
          {H + ((L : Multiset P₁).erase U).map D.left + {D.pair U W}} := by
  induction L generalizing H with
  | nil => simp
  | cons u L ih =>
    rw [run_cons, ih]
    -- the pairing sum over the single right class
    have hsum : ∑ v ∈ ({W} : Multiset P₂).toFinset.filter (D.compat u),
        ({W} : Multiset P₂).count v • D.run L (({W} : Multiset P₂).erase v) (D.pair u v ::ₘ H) =
        if D.compat u W then {D.pair u W ::ₘ H + (L : Multiset P₁).map D.left} else 0 := by
      rw [Multiset.toFinset_singleton, filter_singleton]
      split_ifs with h
      · rw [sum_singleton, Multiset.count_singleton_self, Multiset.erase_singleton, one_smul,
          run_zero]
      · rfl
    rw [hsum]
    set Lm : Multiset P₁ := (L : Multiset P₁) with hLm
    have hcoe : ((u :: L : List P₁) : Multiset P₁) = u ::ₘ Lm := rfl
    rw [hcoe]
    set S : P₁ → Multiset (Multiset Q) :=
      fun U => {H + ((u ::ₘ Lm).erase U).map D.left + {D.pair U W}} with hS
    have hST : ∀ U ∈ Lm, ({D.left u ::ₘ H + (Lm.erase U).map D.left + {D.pair U W}} :
        Multiset (Multiset Q)) = S U := by
      intro U hU
      simp only [hS]
      by_cases hUu : U = u
      · subst hUu
        rw [Multiset.erase_cons_head]
        congr 1
        conv_rhs => rw [← Multiset.cons_erase hU, Multiset.map_cons]
        simp only [← Multiset.singleton_add]
        abel
      · rw [Multiset.erase_cons_tail Lm (Ne.symm hUu), Multiset.map_cons]
        congr 1
        simp only [← Multiset.singleton_add]
        abel
    have hsub : Lm.toFinset.filter (fun U => D.compat U W) ⊆
        (u ::ₘ Lm).toFinset.filter (fun U => D.compat U W) := by
      intro U hU
      rw [mem_filter, Multiset.mem_toFinset] at hU ⊢
      exact ⟨Multiset.mem_cons_of_mem hU.1, hU.2⟩
    have hsum1 : ∑ U ∈ Lm.toFinset.filter (fun U => D.compat U W), Lm.count U •
        ({D.left u ::ₘ H + (Lm.erase U).map D.left + {D.pair U W}} : Multiset (Multiset Q)) =
        ∑ U ∈ (u ::ₘ Lm).toFinset.filter (fun U => D.compat U W), Lm.count U • S U := by
      rw [← sum_subset hsub]
      · refine sum_congr rfl fun U hU => ?_
        rw [hST U (Multiset.mem_toFinset.1 (mem_filter.1 hU).1)]
      · intro U hU hU'
        have hUL : U ∉ Lm := by
          intro h
          exact hU' (mem_filter.2 ⟨Multiset.mem_toFinset.2 h, (mem_filter.1 hU).2⟩)
        rw [Multiset.count_eq_zero.2 hUL, zero_smul]
    have hsum2 : (if D.compat u W then
        ({D.pair u W ::ₘ H + Lm.map D.left} : Multiset (Multiset Q)) else 0) =
        ∑ U ∈ (u ::ₘ Lm).toFinset.filter (fun U => D.compat U W),
          (if U = u then 1 else 0) • S U := by
      have hite : ∀ U, (if U = u then 1 else 0 : ℕ) • S U = if U = u then S U else 0 := by
        intro U
        split_ifs <;> simp
      simp_rw [hite]
      rw [sum_ite_eq']
      have hmem : u ∈ (u ::ₘ Lm).toFinset.filter (fun U => D.compat U W) ↔ D.compat u W := by
        simp
      by_cases hc : D.compat u W
      · rw [ite_eq_left hc, ite_eq_left (hmem.2 hc)]
        simp only [hS, Multiset.erase_cons_head]
        congr 1
        simp only [← Multiset.singleton_add]
        abel
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hmem.1 h))]
    rw [hsum1, hsum2, add_assoc, ← sum_add_distrib]
    congr 1
    · congr 1
      simp only [← Multiset.singleton_add, Multiset.map_add, Multiset.map_singleton]
      abel
    · refine sum_congr rfl fun U _ => ?_
      rw [← add_smul, Multiset.count_cons]

end MergeData

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Compatibility with a single vertex is the test `ℓ(U) = {0}` -/

theorem bilin_singleton {X : Finset V} {x : V} (hx : x ∉ X) (a b : V → F2) :
    bilin G X {x} a b = b x * combo G X a x := by
  rw [bilin_eq_sum_right G (disjoint_singleton_right.2 hx), sum_singleton]

theorem combo_mem_profile_singleton (x : V) (b : V → F2) :
    combo G {x} b ∈ profile G {x} {x} := by
  unfold combo profile
  rw [sum_singleton]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, mem_singleton_self x, rfl⟩)

/-- For `U ≤ W_X` and `x ∉ X`, a class with profile `U` can absorb `x` iff `ℓ(U) = {0}`, i.e.
every vector of `U` vanishes at `x`. -/
theorem compatible_singleton_iff {X : Finset V} {x : V} (hx : x ∉ X)
    {U : Submodule F2 (V → F2)} (hU : U ≤ cutSpace (G.adjMatrix F2) X) :
    Compatible G X {x} U (profile G {x} {x}) ↔ ∀ u ∈ U, u x = 0 := by
  constructor
  · intro h u hu
    have hu' := hU hu
    unfold cutSpace at hu'
    obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun F2).1 hu'
    set a : V → F2 := fun y => if hy : y ∈ X then c ⟨y, hy⟩ else 0 with ha
    have hca : combo G X a = u := by
      rw [← hc]
      unfold combo
      rw [← sum_coe_sort X]
      refine Fintype.sum_congr _ _ fun y => ?_
      simp [ha]
    have := h a (Pi.single x 1) (hca ▸ hu) (combo_mem_profile_singleton G x _)
    rw [bilin_singleton G hx, hca] at this
    simpa using this
  · intro h a b ha _
    rw [bilin_singleton G hx, h _ ha, mul_zero]

/-! ### One step of the linear dynamic program -/

/-- The empty vertex set has exactly one color partition, with empty histogram. -/
theorem hists_empty : hists G ∅ = {0} := by
  have hpart : ∀ P : Finpartition (∅ : Finset V), P.parts = ∅ := fun P =>
    P.parts_eq_empty_iff.2 rfl
  have huniv : (univ : Finset (Finpartition (∅ : Finset V))) = {Finpartition.empty (Finset V)} := by
    ext P
    simp only [mem_univ, mem_singleton, true_iff]
    exact Finpartition.ext (by rw [hpart P, hpart])
  have hcp : colorParts G ∅ = univ := by
    ext P
    simp only [mem_univ, iff_true, mem_colorParts]
    intro C hC
    rw [hpart P] at hC
    exact absurd hC (notMem_empty C)
  unfold hists
  rw [hcp, huniv]
  simp [hist, hpart]

open Classical in
/-- **One step of the linear dynamic program (Corollary 1).**  From a histogram `h` at the
prefix `X`, adding the vertex `x`: open a new class (eq. 21), or let `x` join a class of a
profile `U` with `ℓ(U) = {0}`, with multiplicity `h(U)` (eq. 22). -/
noncomputable def linStep (X : Finset V) (x : V) (h : Multiset (Submodule F2 (V → F2))) :
    Multiset (Multiset (Submodule F2 (V → F2))) :=
  {h.map (Submodule.map (restrictOut (X ∪ {x}))) +
      {Submodule.span F2 {cutRow (G.adjMatrix F2) (X ∪ {x}) x}}} +
    ∑ U ∈ h.toFinset.filter (fun U => ∀ u ∈ U, u x = 0),
      h.count U • {(h.erase U).map (Submodule.map (restrictOut (X ∪ {x}))) +
        {U.map (restrictOut (X ∪ {x})) ⊔ Submodule.span F2 {cutRow (G.adjMatrix F2) (X ∪ {x}) x}}}

theorem profile_singleton_map {X : Finset V} (x : V) :
    (profile G {x} {x}).map (restrictOut (X ∪ {x})) =
      Submodule.span F2 {cutRow (G.adjMatrix F2) (X ∪ {x}) x} := by
  rw [← profile_eq_map G (show ({x} : Finset V) ⊆ X ∪ {x} from subset_union_right)]
  simp [profile, Set.image_singleton]

theorem hist_le_cutSpace {X : Finset V} (P : Finpartition X) :
    ∀ U ∈ hist G P, U ≤ cutSpace (G.adjMatrix F2) X := by
  intro U hU
  obtain ⟨C, hC, rfl⟩ := Multiset.mem_map.1 hU
  exact profile_le_cutSpace G (P.subset hC)

open Classical in
/-- **Correctness of one step (Corollary 1).** -/
theorem hists_insert {X : Finset V} {x : V} (hx : x ∉ X) :
    hists G (X ∪ {x}) = (hists G X).bind (linStep G X x) := by
  rw [hists_union G (disjoint_singleton_right.2 hx), hists_singleton, mergeHists]
  simp only [Multiset.singleton_bind]
  unfold hists
  rw [Multiset.bind_map, Multiset.bind_map]
  refine Multiset.bind_congr fun P hP => ?_
  have hle := hist_le_cutSpace G P
  have hleft : (mergeData G X {x}).left = Submodule.map (restrictOut (X ∪ {x})) := rfl
  have hright : (mergeData G X {x}).right (profile G {x} {x}) =
      Submodule.span F2 {cutRow (G.adjMatrix F2) (X ∪ {x}) x} := profile_singleton_map G x
  have hpair : ∀ U, (mergeData G X {x}).pair U (profile G {x} {x}) =
      U.map (restrictOut (X ∪ {x})) ⊔ Submodule.span F2 {cutRow (G.adjMatrix F2) (X ∪ {x}) x} :=
    fun U => by
      show U.map _ ⊔ (profile G {x} {x}).map _ = _
      rw [profile_singleton_map]
  rw [MergeData.run_single, Multiset.coe_toList, linStep, hleft, hright]
  simp_rw [hpair]
  simp only [zero_add]
  congr 1
  apply sum_congr
  · ext U
    simp only [mem_filter, Multiset.mem_toFinset]
    constructor
    · rintro ⟨hU, hc⟩
      exact ⟨hU, (compatible_singleton_iff G hx (hle U hU)).1 hc⟩
    · rintro ⟨hU, hc⟩
      exact ⟨hU, (compatible_singleton_iff G hx (hle U hU)).2 hc⟩
  · intro U _
    rfl

/-- **The dynamic program along a list of vertices**: starting from the histograms at `X`, add the
vertices one at a time. -/
noncomputable def linDP : List V → Finset V → Multiset (Multiset (Submodule F2 (V → F2))) →
    Multiset (Multiset (Submodule F2 (V → F2)))
  | [], _, A => A
  | x :: xs, X, A => linDP xs (X ∪ {x}) (A.bind (linStep G X x))

theorem linDP_eq_hists : ∀ (l : List V) (X : Finset V), l.Nodup → (∀ x ∈ l, x ∉ X) →
    linDP G l X (hists G X) = hists G (X ∪ l.toFinset)
  | [], X, _, _ => by simp [linDP]
  | x :: xs, X, hnd, hdis => by
    obtain ⟨hx, hnd⟩ := List.nodup_cons.1 hnd
    rw [linDP, ← hists_insert G (hdis x (List.mem_cons_self ..)),
      linDP_eq_hists xs (X ∪ {x}) hnd]
    · congr 1
      ext v
      simp only [mem_union, mem_singleton, List.toFinset_cons, mem_insert, List.mem_toFinset]
      tauto
    · intro y hy
      simp only [mem_union, mem_singleton, not_or]
      exact ⟨hdis y (List.mem_cons_of_mem _ hy), fun h => hx (h ▸ hy)⟩

/-- **Corollary 1 (correctness).**  Along any linear layout, the dynamic program started from
the empty histogram returns the histograms of all color partitions of `G`. -/
theorem linDP_layout (π : LinearLayout V) : linDP G π.order ∅ {0} = hists G univ := by
  rw [← hists_empty G, linDP_eq_hists G π.order ∅ π.nodup (fun _ _ => notMem_empty _)]
  congr 1
  ext v
  simp [π.mem_order v]

theorem count_linDP_layout (π : LinearLayout V) (t : ℕ) :
    (linDP G π.order ∅ {0}).count (Multiset.replicate t ⊥) = numColorPartitions G t := by
  rw [linDP_layout, count_hists_univ]

/-- **Corollary 1 (chromatic polynomial).** -/
theorem chromaticPolynomial_eq_linDP (π : LinearLayout V) :
    chromaticPolynomial G = ∑ t ∈ range (Fintype.card V + 1),
      (((linDP G π.order ∅ {0}).count (Multiset.replicate t ⊥) : ℕ) : ℤ) •
        descPochhammer ℤ t := by
  simp only [chromaticPolynomial, count_linDP_layout]

/-- **Corollary 1 (chromatic number).** -/
theorem chromaticNumber_eq_linDP (π : LinearLayout V) :
    G.chromaticNumber =
      ((sInf {t | 0 < (linDP G π.order ∅ {0}).count (Multiset.replicate t ⊥)} : ℕ) : ℕ∞) := by
  simp only [count_linDP_layout, chromaticNumber_eq_sInf]

end SubspaceConvolution
