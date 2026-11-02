/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.ChromaticPolynomial

/-!
# Theorem 7.1: recovering an optimal coloring by backtracking

The paper recovers an optimal coloring by backtracking through the dynamic program: at every node
it recovers a left and a right histogram and the pairing choices that produced the parent histogram,
recursively recovers child partitions with these histograms, and follows the pairing choices using
available classes of the recorded profiles; Lemma 7.1 makes each pairing valid.

`realize` implements this recursion: for every histogram `h` produced by the dynamic program at a
node, it returns a color partition of the vertices below the node with histogram exactly `h`, built
from the realizations of child histograms and a compatible matching.  At the root, realizing the
histogram `χ(G) · δ_{0}` gives an optimal coloring (`exists_optimal_of_treeDP`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Following the pairing choices: every parent histogram produced by the merge recurrence from the
histograms of `P₁` and `P₂` is the parent histogram of some compatible matching between the classes
of `P₁` and `P₂`. -/
theorem exists_matching_of_mem_run {X₁ X₂ : Finset V} (P₁ : Finpartition X₁)
    (P₂ : Finpartition X₂) {h : Multiset (Submodule F2 (V → F2))}
    (hh : h ∈ (letI := Classical.decEq (Submodule F2 (V → F2));
      letI := Classical.decRel (mergeData G X₁ X₂).compat;
      (mergeData G X₁ X₂).run (hist G P₁).toList (hist G P₂) 0)) :
    ∃ M : Finset (Finset V × Finset V), IsPM P₁.parts P₂.parts M ∧
      (∀ e ∈ M, Compatible G X₁ X₂ (profile G X₁ e.1) (profile G X₂ e.2)) ∧
      (mergeData G X₁ X₂).parentHist (profile G X₁) (profile G X₂) P₁.parts P₂.parts M = h := by
  classical
  obtain ⟨l, hl, hls, hlm⟩ :=
    exists_list_of_coe_eq_map (profile G X₁) (hist G P₁).toList P₁.parts (by
      rw [Multiset.coe_toList]; rfl)
  have hrun := (mergeData G X₁ X₂).run_spec' (profile G X₁) (profile G X₂) l hl P₂.parts
  rw [hlm, hls] at hrun
  have hh' : h ∈ (mergeData G X₁ X₂).run (hist G P₁).toList (P₂.parts.val.map (profile G X₂)) 0 := by
    convert hh using 2; rfl
  rw [← hrun] at hh'
  obtain ⟨M, hM, rfl⟩ := Multiset.mem_map.1 hh'
  obtain ⟨h1, h2, h3, h4⟩ := ((mergeData G X₁ X₂).mem_matchings).1 hM
  exact ⟨M, ⟨h1, h2, h3⟩, h4, rfl⟩

theorem leafSet_node (l r : DTree V) : (DTree.node l r).leafSet = l.leafSet ∪ r.leafSet := by
  simp [DTree.leafSet, DTree.leaves, List.toFinset_append]

theorem hist_copy {a b : Finset V} (P : Finpartition a) (h : a = b) :
    hist G (P.copy h) = hist G P := by
  subst h
  rfl

/-- The partition `{{v}}` of the leaf `{v}`. -/
def leafPartition (v : V) : Finpartition (DTree.leaf v).leafSet :=
  (Finpartition.indiscrete (singleton_ne_empty v)).copy (by simp [DTree.leafSet, DTree.leaves])

open Classical in
/-- **Backtracking (Theorem 7.1).**  For a histogram `h` produced by the dynamic program at the
node `t`, a color partition of the vertices below `t` with histogram `h`. -/
noncomputable def realize : (t : DTree V) → t.leaves.Nodup → (h : Multiset (Submodule F2 (V → F2))) →
    h ∈ treeDP G t → {P : Finpartition t.leafSet // IsColorPartition G P ∧ hist G P = h}
  | .leaf v, _, h, hh =>
    ⟨leafPartition v, by
      constructor
      · intro C hC x hx y hy hxy
        simp only [leafPartition, Finpartition.copy_parts, Finpartition.indiscrete_parts,
          mem_singleton] at hC
        subst hC
        simp only [mem_singleton] at hx hy
        rw [hx, hy] at hxy
        exact G.irrefl hxy
      · simp only [treeDP, Multiset.mem_singleton] at hh
        subst hh
        rw [leafPartition, hist_copy]
        simp [hist]⟩
  | .node l r, hnd, h, hh => by
    have h' : (l.leaves ++ r.leaves).Nodup := hnd
    have hl := List.Nodup.of_append_left h'
    have hr := List.Nodup.of_append_right h'
    have hd : Disjoint l.leafSet r.leafSet := by
      rw [disjoint_left]
      intro x hxl hxr
      exact List.disjoint_of_nodup_append h' (List.mem_toFinset.1 hxl) (List.mem_toFinset.1 hxr)
    -- recover a left and a right histogram
    have ex : ∃ h₁ ∈ treeDP G l, ∃ h₂ ∈ treeDP G r,
        h ∈ (mergeData G l.leafSet r.leafSet).run h₁.toList h₂ 0 := by
      have hh' : h ∈ mergeHists G l.leafSet r.leafSet (treeDP G l) (treeDP G r) := hh
      unfold mergeHists at hh'
      obtain ⟨h₁, hh₁, hh₂⟩ := Multiset.mem_bind.1 hh'
      obtain ⟨h₂, hh₂, hh₃⟩ := Multiset.mem_bind.1 hh₂
      exact ⟨h₁, hh₁, h₂, hh₂, hh₃⟩
    let h₁ := ex.choose
    have hh₁ := ex.choose_spec.1
    let h₂ := ex.choose_spec.2.choose
    have hh₂ := ex.choose_spec.2.choose_spec.1
    have hh₃ := ex.choose_spec.2.choose_spec.2
    -- recursively recover child partitions
    let P₁ := realize l hl h₁ hh₁
    let P₂ := realize r hr h₂ hh₂
    -- follow the pairing choices
    have exM := exists_matching_of_mem_run G P₁.1 P₂.1 (h := h) (by
      rw [P₁.2.2, P₂.2.2]
      convert hh₃ using 2)
    let M := exM.choose
    have hM := exM.choose_spec
    exact ⟨(ofTriple hd P₁.1 P₂.1 hM.1).copy (leafSet_node l r).symm, by
      constructor
      · intro C hC
        rw [Finpartition.copy_parts] at hC
        exact isColorPartition_ofTriple G hd hM.1 P₁.2.1 P₂.2.1 hM.2.1 C hC
      · rw [hist_copy, hist_ofTriple, hM.2.2]⟩

/-- **Theorem 7.1 (optimal coloring).**  Realizing the root histogram `χ(G) · δ_{0}` by
backtracking gives a color partition of `G` into exactly `χ(G)` classes. -/
theorem exists_optimal_of_treeDP (D : RankDecomposition V) :
    ∃ (t : ℕ) (P : Finpartition D.tree.leafSet), G.chromaticNumber = t ∧
      IsColorPartition G P ∧ #P.parts = t := by
  classical
  set t := sInf {t | 0 < (treeDP G D.tree).count (Multiset.replicate t ⊥)} with ht
  have hne : {t | 0 < (treeDP G D.tree).count (Multiset.replicate t ⊥)}.Nonempty := by
    obtain ⟨t₀, ht₀⟩ := exists_numColorPartitions_pos G
    exact ⟨t₀, by simpa [count_treeDP_root] using ht₀⟩
  have hpos : 0 < (treeDP G D.tree).count (Multiset.replicate t ⊥) := Nat.sInf_mem hne
  have hmem : Multiset.replicate t ⊥ ∈ treeDP G D.tree := Multiset.count_pos.1 hpos
  obtain ⟨P, hP, hPh⟩ := realize G D.tree D.nodup _ hmem
  refine ⟨t, P, chromaticNumber_eq_treeDP G D, hP, ?_⟩
  have := congrArg Multiset.card hPh
  simpa [hist] using this

end SubspaceConvolution
