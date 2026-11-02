/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.MergeBijection

/-!
# Theorem 7.1: correctness of the dynamic program on a rank-decomposition

* `hists_union` — **the merge step**: for disjoint children `X₁, X₂`, the histograms of all color
  partitions of `G[X₁ ∪ X₂]` (with multiplicity) are obtained from the child histograms by the
  paper's recurrence (process the left classes one at a time, eqs. (hist-row), (hist-weight)).
* `treeDP` — the dynamic program over a rooted rank-decomposition; `treeDP_eq_hists` — it
  computes the histograms of all color partitions of the vertex set below each node.
* `count_treeDP_root` — at the root all profiles vanish, and the count of the histogram
  `t · δ_{0}` is `a_t`, the number of partitions of `V(G)` into `t` nonempty independent sets.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Any list enumerating the multiset `s.map f` is the image of an enumeration of `s`. -/
theorem exists_list_of_coe_eq_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ (L : List β) (s : Finset α), (L : Multiset β) = s.val.map f →
      ∃ l : List α, l.Nodup ∧ l.toFinset = s ∧ l.map f = L
  | [], s, h => by
    refine ⟨[], List.nodup_nil, ?_, rfl⟩
    have : s.val.map f = 0 := h.symm
    rw [Multiset.map_eq_zero, val_eq_zero] at this
    simp [this]
  | b :: L, s, h => by
    have hb : b ∈ s.val.map f := by rw [← h]; simp
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    have h' : (L : Multiset β) = (s.erase a).val.map f := by
      rw [erase_val, Multiset.map_erase_of_mem _ _ ha, ← h]
      simp
    obtain ⟨l, hl, hls, hlm⟩ := exists_list_of_coe_eq_map f L (s.erase a) h'
    refine ⟨a :: l, List.nodup_cons.2 ⟨?_, hl⟩, ?_, by simp [hlm]⟩
    · rw [← List.mem_toFinset, hls]
      simp
    · rw [List.toFinset_cons, hls, insert_erase ha]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
/-- One merge of histogram multisets: for every pair of child histograms, run the merge
recurrence (processing the left histogram in the order `h₁.toList`). -/
noncomputable def mergeHists (X₁ X₂ : Finset V) (A B : Multiset (Multiset (Submodule F2 (V → F2)))) :
    Multiset (Multiset (Submodule F2 (V → F2))) :=
  A.bind fun h₁ => B.bind fun h₂ => (mergeData G X₁ X₂).run h₁.toList h₂ 0

open Classical in
/-- **The merge step of Theorem 7.1.**  The histograms (with multiplicity) of all color
partitions of `G[X₁ ∪ X₂]` are computed from those of the children by the merge recurrence. -/
theorem hists_union {X₁ X₂ : Finset V} (hd : Disjoint X₁ X₂) :
    hists G (X₁ ∪ X₂) = mergeHists G X₁ X₂ (hists G X₁) (hists G X₂) := by
  -- rewrite the right-hand side as a sum over triples (P₁, P₂, M)
  have hR : mergeHists G X₁ X₂ (hists G X₁) (hists G X₂) =
      ∑ x ∈ (colorParts G X₁ ×ˢ colorParts G X₂).sigma
          (fun PP => (mergeData G X₁ X₂).matchings (profile G X₁) (profile G X₂) PP.1.parts
            PP.2.parts),
        (singleton ((mergeData G X₁ X₂).parentHist (profile G X₁) (profile G X₂) x.1.1.parts
          x.1.2.parts x.2) : Multiset (Multiset (Submodule F2 (V → F2)))) := by
    rw [sum_sigma, sum_product]
    unfold mergeHists hists
    rw [Multiset.bind_map]
    simp only [Multiset.bind_map]
    rw [Multiset.bind, Multiset.join, ← sum_eq_multiset_sum]
    refine sum_congr rfl fun P₁ _ => ?_
    rw [Multiset.bind, Multiset.join, ← sum_eq_multiset_sum]
    refine sum_congr rfl fun P₂ _ => ?_
    obtain ⟨l, hl, hls, hlm⟩ :=
      exists_list_of_coe_eq_map (profile G X₁) (hist G P₁).toList P₁.parts (by
        rw [Multiset.coe_toList]; rfl)
    rw [← hlm, show hist G P₂ = P₂.parts.val.map (profile G X₂) from rfl,
      ← (mergeData G X₁ X₂).run_spec (profile G X₁) (profile G X₂) l hl P₂.parts 0, hls]
    simp only [zero_add]
  rw [hR]
  unfold hists
  rw [← Multiset.sum_map_singleton (Multiset.map (hist G) (colorParts G (X₁ ∪ X₂)).val),
    Multiset.map_map, ← sum_eq_multiset_sum]
  refine sum_bij' (fun P _ => ⟨(restrictL P, restrictR P), matchOf X₁ X₂ P.parts⟩)
    (fun x hx => ofTriple hd x.1.1 x.1.2
      (by
        obtain ⟨-, hM⟩ := mem_sigma.1 hx
        obtain ⟨h1, h2, h3, -⟩ := ((mergeData G X₁ X₂).mem_matchings).1 hM
        exact ⟨h1, h2, h3⟩))
    ?_ ?_ ?_ ?_ ?_
  · -- the forward map lands in the triples
    intro P hP
    have hP' := (mem_colorParts G).1 hP
    refine mem_sigma.2 ⟨mem_product.2 ⟨(mem_colorParts G).2
      (isColorPartition_restrict G subset_union_left hP'), (mem_colorParts G).2
      (isColorPartition_restrict G subset_union_right hP')⟩,
      ((mergeData G X₁ X₂).mem_matchings).2 ?_⟩
    obtain ⟨h1, h2, h3⟩ := isPM_matchOf hd P
    exact ⟨h1, h2, h3, compat_matchOf G hd hP'⟩
  · -- the backward map lands in the color partitions
    intro x hx
    obtain ⟨hPP, hM⟩ := mem_sigma.1 hx
    obtain ⟨hP₁, hP₂⟩ := mem_product.1 hPP
    obtain ⟨-, -, -, hc⟩ := ((mergeData G X₁ X₂).mem_matchings).1 hM
    exact (mem_colorParts G).2 (isColorPartition_ofTriple G hd _ ((mem_colorParts G).1 hP₁)
      ((mem_colorParts G).1 hP₂) hc)
  · intro P hP
    exact ofTriple_restrict hd P
  · intro x hx
    obtain ⟨⟨P₁, P₂⟩, M⟩ := x
    have hM : IsPM P₁.parts P₂.parts M := by
      obtain ⟨-, hM⟩ := mem_sigma.1 hx
      obtain ⟨h1, h2, h3, -⟩ := ((mergeData G X₁ X₂).mem_matchings).1 hM
      exact ⟨h1, h2, h3⟩
    dsimp only
    rw [restrictL_ofTriple, restrictR_ofTriple, ofTriple_parts, matchOf_parentParts hd P₁ P₂ hM]
  · intro P hP
    dsimp only [Function.comp_apply]
    congr 1
    conv_lhs => rw [← ofTriple_restrict hd P]
    rw [hist_ofTriple]

/-! ### Leaves and the whole tree -/

theorem hists_singleton (v : V) : hists G {v} = {{profile G {v} {v}}} := by
  have hpart : ∀ P : Finpartition ({v} : Finset V), P.parts = {{v}} := by
    intro P
    ext C
    rw [mem_singleton]
    constructor
    · intro hC
      have hsub := P.subset hC
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hC
      have hxv := hsub hx
      rw [mem_singleton] at hxv
      subst hxv
      exact subset_antisymm hsub (singleton_subset_iff.2 hx)
    · rintro rfl
      obtain ⟨C, hC, hvC⟩ := P.exists_mem (mem_singleton_self v)
      have : C = {v} := subset_antisymm (P.subset hC) (singleton_subset_iff.2 hvC)
      rwa [this] at hC
  have huniv : (univ : Finset (Finpartition ({v} : Finset V))) =
      {Finpartition.indiscrete (singleton_ne_empty v)} := by
    ext P
    simp only [mem_univ, mem_singleton, true_iff]
    exact Finpartition.ext (by rw [hpart P, hpart])
  have hcp : colorParts G {v} = univ := by
    ext P
    simp only [mem_univ, iff_true]
    rw [mem_colorParts]
    intro C hC x hx y hy
    rw [hpart P, mem_singleton] at hC
    subst hC
    rw [mem_singleton] at hx hy
    rw [hx, hy]
    exact G.irrefl
  unfold hists
  rw [hcp, huniv]
  simp [hist, hpart]

open Classical in
/-- **The dynamic program of Theorem 7.1** on a rooted rank-decomposition: a leaf `v` has the
single histogram `{U_{{v}}({v})}`; a node merges the histogram multisets of its children. -/
noncomputable def treeDP : DTree V → Multiset (Multiset (Submodule F2 (V → F2)))
  | .leaf v => {{profile G {v} {v}}}
  | .node l r => mergeHists G l.leafSet r.leafSet (treeDP l) (treeDP r)

/-- **Correctness of the dynamic program**: at every node, `treeDP` is the multiset of histograms
of all color partitions of the vertices below that node. -/
theorem treeDP_eq_hists : ∀ t : DTree V, t.leaves.Nodup → treeDP G t = hists G t.leafSet
  | .leaf v, _ => by
    simp [treeDP, DTree.leafSet, DTree.leaves, hists_singleton]
  | .node l r, h => by
    have h' : (l.leaves ++ r.leaves).Nodup := h
    have hl := List.Nodup.of_append_left h'
    have hr := List.Nodup.of_append_right h'
    have hd : Disjoint l.leafSet r.leafSet := by
      rw [disjoint_left]
      intro x hxl hxr
      exact List.disjoint_of_nodup_append h' (List.mem_toFinset.1 hxl) (List.mem_toFinset.1 hxr)
    have hls : (DTree.node l r).leafSet = l.leafSet ∪ r.leafSet := by
      simp [DTree.leafSet, DTree.leaves, List.toFinset_append]
    rw [treeDP, treeDP_eq_hists l hl, treeDP_eq_hists r hr, hls, hists_union G hd]

/-! ### The root -/

/-- `a_t`: the number of partitions of `V(G)` into exactly `t` nonempty independent sets. -/
noncomputable def numColorPartitions (t : ℕ) : ℕ :=
  #((colorParts G univ).filter fun P => #P.parts = t)

theorem profile_univ (C : Finset V) : profile G univ C = ⊥ := by
  rw [eq_bot_iff, profile, Submodule.span_le]
  rintro _ ⟨x, -, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_bot]
  funext y
  simp

theorem hist_univ (P : Finpartition (univ : Finset V)) :
    hist G P = Multiset.replicate #P.parts ⊥ := by
  rw [hist, Multiset.eq_replicate]
  refine ⟨by simp, fun U hU => ?_⟩
  obtain ⟨C, -, rfl⟩ := Multiset.mem_map.1 hU
  exact profile_univ G C

/-- At the root, the multiplicity of the histogram `t · δ_{0}` is `a_t`. -/
theorem count_hists_univ (t : ℕ) :
    (hists G univ).count (Multiset.replicate t ⊥) = numColorPartitions G t := by
  classical
  rw [hists, Multiset.count_map, numColorPartitions, card_def, filter_val]
  congr 1
  apply Multiset.filter_congr
  intro P _
  rw [hist_univ, eq_comm]
  constructor
  · intro h
    have := congrArg Multiset.card h
    simpa using this
  · intro h
    rw [h]

/-- **Theorem 7.1 (correctness).**  For a rank-decomposition `D` of `G`, the dynamic program
returns at the root, for every `t`, exactly `a_t` copies of the histogram `t · δ_{0}`. -/
theorem count_treeDP_root (D : RankDecomposition V) (t : ℕ) :
    (treeDP G D.tree).count (Multiset.replicate t ⊥) = numColorPartitions G t := by
  have hroot : D.tree.leafSet = univ := by
    ext v
    simp [DTree.leafSet, D.mem_leaves v]
  rw [treeDP_eq_hists G D.tree D.nodup, hroot, count_hists_univ]

end SubspaceConvolution
