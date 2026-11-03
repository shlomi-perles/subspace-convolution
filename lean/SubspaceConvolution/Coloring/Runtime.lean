/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LinearDP
import SubspaceConvolution.Coloring.SubspaceCount

/-!
# Running time of Theorem 6 and Corollary 1

The paper's algorithm aggregates the merge recurrence: for a fixed left histogram, it keeps the set
of *distinct* states `(b, H)` (available right histogram, formed parent histogram), adding counts at
equal states.  We model its work by the number of transitions it performs:

* `MergeData.stepStates` — the distinct states after processing one more left class;
* `MergeData.stepCost` — the transitions of that step: per state, one "separate" transition and one
  pairing transition per compatible available right profile;
* `MergeData.runCost` — all steps, plus one final operation per state;
* `mergeCost`, `treeCost` — summed over all left histograms and over all nodes of the tree;
* `linCost` — the transitions of the linear-layout dynamic program.

Main results (with `L = N₂(r)` and `N = |V(G)|`):

* `treeCost_le` — on a rank-decomposition of width at most `r`,
  `treeCost ≤ 2N · (N+1)^L · (N+1) · (L+1) · (N+1)^{2L}`  (the paper's `(N+1)^{3L} poly(N, L)`);
* `treeCost_le_pow` — hence `treeCost ≤ N^{11 L} ≤ N^{2^{⌊r²/4⌋+8}}` for `N ≥ 2`
  (the paper's `N^{O(N₂(r))} = N^{2^{r²/4+O(1)}}`);
* `linCost_le` — on a linear layout of width at most `r`,
  `linCost ≤ N · (N+1)^{N₂(r)} · (2^{⌊r²/4⌋+4} + 1)` (the paper's
  `(N+1)^{N₂(r)} 2^{O(r²)} N^{O(1)}`).

Bit complexity (counts have `O(N log N)` bits) is not modelled: we count arithmetic operations.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

/-! ### Counting bounded multisets -/

/-- Multisets supported in `T` with at most `N` elements number at most `(N+1)^{|T|}`. -/
theorem card_le_of_bounded_multisets {α : Type*} [DecidableEq α] (T : Finset α) (N : ℕ)
    (M : Finset (Multiset α)) (hM : ∀ m ∈ M, (∀ x ∈ m, x ∈ T) ∧ Multiset.card m ≤ N) :
    #M ≤ (N + 1) ^ #T := by
  classical
  let f : Multiset α → (T → Fin (N + 1)) :=
    fun m t => ⟨min (m.count (t : α)) N, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hinj : Set.InjOn f M := by
    intro m hm m' hm' hmm
    ext a
    by_cases ha : a ∈ T
    · have h1 := congrArg Fin.val (congrFun hmm ⟨a, ha⟩)
      simp only [f] at h1
      have hc : m.count a ≤ N := (Multiset.count_le_card a m).trans (hM m hm).2
      have hc' : m'.count a ≤ N := (Multiset.count_le_card a m').trans (hM m' hm').2
      rwa [min_eq_left hc, min_eq_left hc'] at h1
    · have h1 : a ∉ m := fun h => ha ((hM m hm).1 a h)
      have h2 : a ∉ m' := fun h => ha ((hM m' hm').1 a h)
      rw [Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]
  have h := card_le_card_of_injOn f (t := univ) (fun _ _ => mem_coe.2 (mem_univ _)) hinj
  simpa [Fintype.card_fun, Fintype.card_coe] using h

theorem card_le_mul_of_pairs {α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset (α × β)) :
    #S ≤ #(S.image Prod.fst) * #(S.image Prod.snd) := by
  rw [← card_product]
  exact card_le_card fun s hs => mem_product.2 ⟨mem_image_of_mem _ hs, mem_image_of_mem _ hs⟩

/-! ### The aggregated merge and its cost -/

namespace MergeData

variable {P₁ P₂ Q : Type*} (D : MergeData P₁ P₂ Q) [DecidableEq P₂] [DecidableEq Q]
  [DecidableRel D.compat]

/-- The distinct states after processing the left class `u` from the states `S`. -/
def stepStates (u : P₁) (S : Finset (Multiset P₂ × Multiset Q)) :
    Finset (Multiset P₂ × Multiset Q) :=
  S.biUnion fun s => insert (s.1, D.left u ::ₘ s.2)
    ((s.1.toFinset.filter (D.compat u)).image fun v => (s.1.erase v, D.pair u v ::ₘ s.2))

/-- The transitions performed when processing `u`. -/
def stepCost (u : P₁) (S : Finset (Multiset P₂ × Multiset Q)) : ℕ :=
  ∑ s ∈ S, (1 + #(s.1.toFinset.filter (D.compat u)))

/-- The cost of the aggregated merge: all transitions, plus one final operation per state. -/
def runCost : List P₁ → Finset (Multiset P₂ × Multiset Q) → ℕ
  | [], S => #S
  | u :: us, S => D.stepCost u S + runCost us (D.stepStates u S)

/-- States with available histogram in `T₂` (at most `N` classes) and formed histogram in `T`
(at most `k` classes). -/
def InRegion (T₂ : Finset P₂) (T : Finset Q) (N k : ℕ) (s : Multiset P₂ × Multiset Q) : Prop :=
  (∀ v ∈ s.1, v ∈ T₂) ∧ Multiset.card s.1 ≤ N ∧ (∀ w ∈ s.2, w ∈ T) ∧ Multiset.card s.2 ≤ k

variable {D}

theorem stepStates_inRegion {T₂ : Finset P₂} {T : Finset Q} {N k : ℕ} {u : P₁}
    {S : Finset (Multiset P₂ × Multiset Q)} (hu : D.left u ∈ T ∧ ∀ v ∈ T₂, D.pair u v ∈ T)
    (hS : ∀ s ∈ S, InRegion T₂ T N k s) : ∀ s ∈ D.stepStates u S, InRegion T₂ T N (k + 1) s := by
  intro s' hs'
  obtain ⟨s, hs, hs'⟩ := mem_biUnion.1 hs'
  obtain ⟨h1, h2, h3, h4⟩ := hS s hs
  rcases mem_insert.1 hs' with rfl | hs'
  · refine ⟨h1, h2, fun w hw => ?_, by simp [h4]⟩
    rcases Multiset.mem_cons.1 hw with rfl | hw
    · exact hu.1
    · exact h3 w hw
  · obtain ⟨v, hv, rfl⟩ := mem_image.1 hs'
    have hvs : v ∈ s.1 := Multiset.mem_toFinset.1 (mem_filter.1 hv).1
    refine ⟨fun x hx => h1 x (Multiset.mem_of_mem_erase hx),
      (Multiset.card_erase_le).trans h2, fun w hw => ?_, by simp [h4]⟩
    rcases Multiset.mem_cons.1 hw with rfl | hw
    · exact hu.2 v (h1 v hvs)
    · exact h3 w hw

theorem card_le_of_inRegion {T₂ : Finset P₂} {T : Finset Q} {N k : ℕ}
    (hk : k ≤ N) {S : Finset (Multiset P₂ × Multiset Q)} (hS : ∀ s ∈ S, InRegion T₂ T N k s) :
    #S ≤ (N + 1) ^ #T₂ * (N + 1) ^ #T := by
  refine (card_le_mul_of_pairs S).trans (Nat.mul_le_mul ?_ ?_)
  · apply card_le_of_bounded_multisets
    intro m hm
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hm
    exact ⟨(hS s hs).1, (hS s hs).2.1⟩
  · apply card_le_of_bounded_multisets
    intro m hm
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hm
    exact ⟨(hS s hs).2.2.1, (hS s hs).2.2.2.trans hk⟩

theorem stepCost_le {T₂ : Finset P₂} {u : P₁} {S : Finset (Multiset P₂ × Multiset Q)}
    (hS : ∀ s ∈ S, ∀ v ∈ s.1, v ∈ T₂) : D.stepCost u S ≤ #S * (#T₂ + 1) := by
  unfold stepCost
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun s hs => ?_
  have : #(s.1.toFinset.filter (D.compat u)) ≤ #T₂ :=
    (card_filter_le _ _).trans (card_le_card fun v hv => hS s hs v (Multiset.mem_toFinset.1 hv))
  omega

theorem runCost_le {T₂ : Finset P₂} {T : Finset Q} {N : ℕ} :
    ∀ (us : List P₁) (S : Finset (Multiset P₂ × Multiset Q)) (k : ℕ),
      (∀ u ∈ us, D.left u ∈ T ∧ ∀ v ∈ T₂, D.pair u v ∈ T) → k + us.length ≤ N →
      (∀ s ∈ S, InRegion T₂ T N k s) →
      D.runCost us S ≤ (us.length + 1) * ((#T₂ + 1) * ((N + 1) ^ #T₂ * (N + 1) ^ #T))
  | [], S, k, _, hk, hS => by
    simp only [runCost, List.length_nil, zero_add, one_mul]
    exact (card_le_of_inRegion (by omega) hS).trans (Nat.le_mul_of_pos_left _ (by omega))
  | u :: us, S, k, hu, hk, hS => by
    simp only [runCost, List.length_cons]
    have h1 := stepCost_le (D := D) (u := u) (T₂ := T₂) (S := S) fun s hs => (hS s hs).1
    have h2 := card_le_of_inRegion (by simp at hk; omega) hS
    have h3 := runCost_le us (D.stepStates u S) (k + 1)
      (fun u' hu' => hu u' (List.mem_cons_of_mem _ hu')) (by simp at hk; omega)
      (stepStates_inRegion (hu u List.mem_cons_self) hS)
    calc D.stepCost u S + D.runCost us (D.stepStates u S)
        ≤ #S * (#T₂ + 1) + (us.length + 1) * ((#T₂ + 1) * ((N + 1) ^ #T₂ * (N + 1) ^ #T)) :=
          Nat.add_le_add h1 h3
      _ ≤ (N + 1) ^ #T₂ * (N + 1) ^ #T * (#T₂ + 1) +
            (us.length + 1) * ((#T₂ + 1) * ((N + 1) ^ #T₂ * (N + 1) ^ #T)) := by
          gcongr
      _ = (us.length + 1 + 1) * ((#T₂ + 1) * ((N + 1) ^ #T₂ * (N + 1) ^ #T)) := by ring

end MergeData

/-! ### Profile spaces have at most `N₂(r)` subspaces -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable instance instFintypeSubmoduleV : Fintype (Submodule F2 (V → F2)) :=
  Fintype.ofFinite _

open Classical in
/-- The subspaces of the profile space `W_X`. -/
noncomputable def subspacesOf (X : Finset V) : Finset (Submodule F2 (V → F2)) :=
  univ.filter (· ≤ cutSpace (G.adjMatrix F2) X)

theorem mem_subspacesOf {X : Finset V} {U : Submodule F2 (V → F2)} :
    U ∈ subspacesOf G X ↔ U ≤ cutSpace (G.adjMatrix F2) X := by
  classical
  simp [subspacesOf]

theorem card_subspacesOf_le {X : Finset V} {r : ℕ} (h : cutRank G X ≤ r) :
    #(subspacesOf G X) ≤ numSubspaces r := by
  classical
  have := card_submodules_le_of_finrank_le (cutSpace (G.adjMatrix F2) X) h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  refine Eq.trans_le ?_ this
  congr 1

theorem cutSpace_map_le {X₁ X : Finset V} (h : X₁ ⊆ X) :
    (cutSpace (G.adjMatrix F2) X₁).map (restrictOut X) ≤ cutSpace (G.adjMatrix F2) X := by
  unfold cutSpace
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [restrictOut_cutRow h]
  exact Submodule.subset_span ⟨x, h hx, rfl⟩

theorem hists_bounded {X : Finset V} :
    ∀ h ∈ hists G X, (∀ U ∈ h, U ∈ subspacesOf G X) ∧ Multiset.card h ≤ #X := by
  intro h hh
  obtain ⟨P, -, rfl⟩ := Multiset.mem_map.1 hh
  refine ⟨fun U hU => (mem_subspacesOf G).2 (hist_le_cutSpace G P U hU), ?_⟩
  simp only [hist, Multiset.card_map, card_val]
  exact P.card_parts_le_card

/-! ### Cost of the tree dynamic program -/

open Classical in
/-- The cost of one merge: run the aggregated merge for every distinct left histogram, starting from
the states `(h₂, 0)` for all right histograms `h₂`. -/
noncomputable def mergeCost (X₁ X₂ : Finset V) (A B : Multiset (Multiset (Submodule F2 (V → F2)))) :
    ℕ :=
  ∑ h₁ ∈ A.toFinset, (mergeData G X₁ X₂).runCost h₁.toList (B.toFinset.image fun h₂ => (h₂, 0))

/-- The per-node bound `(N+1)^L · (N+1) · (L+1) · (N+1)^{2L}`. -/
def nodeBound (N L : ℕ) : ℕ := (N + 1) ^ L * ((N + 1) * ((L + 1) * ((N + 1) ^ L * (N + 1) ^ L)))

theorem mergeCost_le {X₁ X₂ : Finset V} (hd : Disjoint X₁ X₂) {r : ℕ}
    (h₁ : cutRank G X₁ ≤ r) (h₂ : cutRank G X₂ ≤ r) (h : cutRank G (X₁ ∪ X₂) ≤ r) :
    mergeCost G X₁ X₂ (hists G X₁) (hists G X₂) ≤ nodeBound (Fintype.card V) (numSubspaces r) := by
  classical
  set N := Fintype.card V
  set L := numSubspaces r
  have hT₁ := card_subspacesOf_le G h₁
  have hT₂ := card_subspacesOf_le G h₂
  have hT := card_subspacesOf_le G h
  have hX₁ : #X₁ ≤ N := card_le_univ X₁
  have hX₂ : #X₂ ≤ N := card_le_univ X₂
  have hX : #X₁ + #X₂ ≤ N := by rw [← card_union_of_disjoint hd]; exact card_le_univ _
  -- number of distinct left histograms
  have hA : #(hists G X₁).toFinset ≤ (N + 1) ^ L := by
    refine (card_le_of_bounded_multisets (subspacesOf G X₁) N _ fun m hm => ?_).trans
      (Nat.pow_le_pow_right (by omega) hT₁)
    obtain ⟨h1, h2⟩ := hists_bounded G m (Multiset.mem_toFinset.1 hm)
    exact ⟨h1, h2.trans hX₁⟩
  unfold mergeCost nodeBound
  set B := (N + 1) * ((L + 1) * ((N + 1) ^ L * (N + 1) ^ L)) with hB
  calc ∑ h₁ ∈ (hists G X₁).toFinset, (mergeData G X₁ X₂).runCost h₁.toList
        ((hists G X₂).toFinset.image fun h₂ => (h₂, 0))
      ≤ ∑ h₁ ∈ (hists G X₁).toFinset, B := sum_le_sum fun h₁ hh₁ => ?_
    _ = #(hists G X₁).toFinset * B := by rw [sum_const, smul_eq_mul]
    _ ≤ (N + 1) ^ L * B := Nat.mul_le_mul_right _ hA
  -- one left histogram
  obtain ⟨hU₁, hcard₁⟩ := hists_bounded G h₁ (Multiset.mem_toFinset.1 hh₁)
  have hrun := (mergeData G X₁ X₂).runCost_le (T₂ := subspacesOf G X₂)
    (T := subspacesOf G (X₁ ∪ X₂)) (N := N) h₁.toList
    ((hists G X₂).toFinset.image fun h₂ => (h₂, 0)) 0
    (by
      intro u hu
      have hu₁ := (mem_subspacesOf G).1 (hU₁ u (Multiset.mem_toList.1 hu))
      refine ⟨(mem_subspacesOf G).2 ?_, fun v hv => (mem_subspacesOf G).2 ?_⟩
      · exact (Submodule.map_mono hu₁).trans (cutSpace_map_le G subset_union_left)
      · exact sup_le ((Submodule.map_mono hu₁).trans (cutSpace_map_le G subset_union_left))
          ((Submodule.map_mono ((mem_subspacesOf G).1 hv)).trans
            (cutSpace_map_le G subset_union_right)))
    (by rw [Multiset.length_toList]; omega)
    (by
      intro s hs
      obtain ⟨h₂, hh₂, rfl⟩ := mem_image.1 hs
      obtain ⟨h1, h2⟩ := hists_bounded G h₂ (Multiset.mem_toFinset.1 hh₂)
      exact ⟨h1, h2.trans hX₂, by simp, by simp⟩)
  refine hrun.trans ?_
  rw [Multiset.length_toList, hB]
  have hlen : Multiset.card h₁ + 1 ≤ N + 1 := by omega
  gcongr

/-- The cost of the whole dynamic program: one operation per leaf, plus the merges. -/
noncomputable def treeCost : DTree V → ℕ
  | .leaf _ => 1
  | .node l r => treeCost l + treeCost r + mergeCost G l.leafSet r.leafSet (treeDP G l) (treeDP G r)

theorem length_subtrees : ∀ t : DTree V, t.subtrees.length + 1 = 2 * t.leaves.length
  | .leaf _ => by simp [DTree.subtrees, DTree.leaves]
  | .node l r => by
    have hl := length_subtrees l
    have hr := length_subtrees r
    simp only [DTree.subtrees, DTree.leaves, List.length_cons, List.length_append]
    omega

theorem mem_subtrees_of_mem_left {l r t : DTree V} (h : t ∈ l.subtrees) :
    t ∈ (DTree.node l r).subtrees := by
  simp [DTree.subtrees, h]

theorem mem_subtrees_of_mem_right {l r t : DTree V} (h : t ∈ r.subtrees) :
    t ∈ (DTree.node l r).subtrees := by
  simp [DTree.subtrees, h]

theorem treeCost_le_aux {r : ℕ} :
    ∀ t : DTree V, t.leaves.Nodup → (∀ s ∈ t.subtrees, cutRank G s.leafSet ≤ r) →
      treeCost G t ≤ t.subtrees.length * nodeBound (Fintype.card V) (numSubspaces r)
  | .leaf v, _, _ => by
    simp only [treeCost, DTree.subtrees, List.length_singleton, one_mul, nodeBound]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  | .node l r', hnd, hw => by
    have h' : (l.leaves ++ r'.leaves).Nodup := hnd
    have hl := List.Nodup.of_append_left h'
    have hr := List.Nodup.of_append_right h'
    have hd : Disjoint l.leafSet r'.leafSet := by
      rw [disjoint_left]
      intro x hxl hxr
      exact List.disjoint_of_nodup_append h' (List.mem_toFinset.1 hxl) (List.mem_toFinset.1 hxr)
    have ihl := treeCost_le_aux l hl fun s hs => hw s (mem_subtrees_of_mem_left hs)
    have ihr := treeCost_le_aux r' hr fun s hs => hw s (mem_subtrees_of_mem_right hs)
    have hls : (DTree.node l r').leafSet = l.leafSet ∪ r'.leafSet := by
      simp [DTree.leafSet, DTree.leaves, List.toFinset_append]
    have hm := mergeCost_le G hd (hw l (mem_subtrees_of_mem_left l.self_mem_subtrees))
      (hw r' (mem_subtrees_of_mem_right r'.self_mem_subtrees))
      (hls ▸ hw _ (DTree.node l r').self_mem_subtrees)
    simp only [treeCost, DTree.subtrees, List.length_cons, List.length_append]
    rw [treeDP_eq_hists G l hl, treeDP_eq_hists G r' hr]
    have e : (l.subtrees.length + r'.subtrees.length + 1) *
        nodeBound (Fintype.card V) (numSubspaces r) =
        l.subtrees.length * nodeBound (Fintype.card V) (numSubspaces r) +
          r'.subtrees.length * nodeBound (Fintype.card V) (numSubspaces r) +
            nodeBound (Fintype.card V) (numSubspaces r) := by ring
    rw [e]
    linarith [ihl, ihr, hm]

/-- **Running time of Theorem 6** (number of arithmetic operations): on a rank-decomposition
of width at most `r`, the dynamic program performs at most
`2N · (N+1)^L · (N+1) · (L+1) · (N+1)^{2L}` operations, `L = N₂(r)`. -/
theorem treeCost_le (D : RankDecomposition V) {r : ℕ} (hw : D.width G ≤ r) :
    treeCost G D.tree ≤ 2 * Fintype.card V * nodeBound (Fintype.card V) (numSubspaces r) := by
  have hlen : D.tree.leaves.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup D.nodup]
    congr
    ext v
    simp [D.mem_leaves v]
  have := treeCost_le_aux G D.tree D.nodup ((D.width_le_iff G).1 hw)
  have hsub := length_subtrees D.tree
  calc treeCost G D.tree ≤ D.tree.subtrees.length * nodeBound (Fintype.card V) (numSubspaces r) :=
        this
    _ ≤ 2 * Fintype.card V * nodeBound (Fintype.card V) (numSubspaces r) := by
        gcongr
        omega

/-- Arithmetic: `2N · nodeBound N L ≤ N^{11 L}` for `N ≥ 2`, `L ≥ 1`. -/
theorem two_mul_nodeBound_le {N L : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    2 * N * nodeBound N L ≤ N ^ (11 * L) := by
  unfold nodeBound
  have h1 : N + 1 ≤ N ^ 2 := by nlinarith
  have h2 : 2 * N ≤ N ^ 2 := by nlinarith
  have h3 : L + 1 ≤ N ^ L := by
    calc L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
      _ ≤ N ^ L := Nat.pow_le_pow_left hN L
  calc 2 * N * ((N + 1) ^ L * ((N + 1) * ((L + 1) * ((N + 1) ^ L * (N + 1) ^ L))))
      = 2 * N * (L + 1) * (N + 1) ^ (3 * L + 1) := by ring
    _ ≤ N ^ 2 * N ^ L * (N ^ 2) ^ (3 * L + 1) := by gcongr
    _ = N ^ (7 * L + 4) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
    _ ≤ N ^ (11 * L) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **Theorem 6 (running time):** `N^{O(N₂(r))} = N^{2^{r²/4+O(1)}}` operations; explicitly
at most `N^{11 · N₂(r)} ≤ N^{2^{⌊r²/4⌋ + 8}}` for `N ≥ 2`. -/
theorem treeCost_le_pow (D : RankDecomposition V) {r : ℕ} (hw : D.width G ≤ r)
    (hN : 2 ≤ Fintype.card V) :
    treeCost G D.tree ≤ Fintype.card V ^ (11 * numSubspaces r) ∧
      treeCost G D.tree ≤ Fintype.card V ^ (2 ^ (r * r / 4 + 8)) := by
  have h1 := (treeCost_le G D hw).trans (two_mul_nodeBound_le hN (numSubspaces_pos r))
  refine ⟨h1, h1.trans (Nat.pow_le_pow_right (by omega) ?_)⟩
  calc 11 * numSubspaces r ≤ 16 * 2 ^ (r * r / 4 + 4) := by
        have := numSubspaces_le r
        omega
    _ = 2 ^ (r * r / 4 + 8) := by ring

/-! ### Cost of the linear dynamic program -/

open Classical in
/-- The transitions of one linear step: per histogram, one "open" and one "join" per profile `U`
with `ℓ(U) = {0}`. -/
noncomputable def linStepCost (x : V) (A : Multiset (Multiset (Submodule F2 (V → F2)))) : ℕ :=
  ∑ h ∈ A.toFinset, (1 + #(h.toFinset.filter fun U => ∀ u ∈ U, u x = 0))

/-- The cost of the linear dynamic program along a list of vertices. -/
noncomputable def linCost : List V → Finset V → Multiset (Multiset (Submodule F2 (V → F2))) → ℕ
  | [], _, _ => 0
  | x :: xs, X, A => linStepCost x A + linCost xs (X ∪ {x}) (A.bind (linStep G X x))

theorem linStepCost_le {X : Finset V} {r : ℕ} (hX : cutRank G X ≤ r) (x : V) :
    linStepCost x (hists G X) ≤
      (Fintype.card V + 1) ^ numSubspaces r * (numSubspaces r + 1) := by
  classical
  unfold linStepCost
  have hT := card_subspacesOf_le G hX
  have hA : #(hists G X).toFinset ≤ (Fintype.card V + 1) ^ numSubspaces r := by
    refine (card_le_of_bounded_multisets (subspacesOf G X) (Fintype.card V) _ fun m hm => ?_).trans
      (Nat.pow_le_pow_right (by omega) hT)
    obtain ⟨h1, h2⟩ := hists_bounded G m (Multiset.mem_toFinset.1 hm)
    exact ⟨h1, h2.trans (card_le_univ X)⟩
  calc ∑ h ∈ (hists G X).toFinset, (1 + #(h.toFinset.filter fun U => ∀ u ∈ U, u x = 0))
      ≤ ∑ h ∈ (hists G X).toFinset, (numSubspaces r + 1) := by
        refine sum_le_sum fun h hh => ?_
        have hb := (hists_bounded G h (Multiset.mem_toFinset.1 hh)).1
        have : #(h.toFinset.filter fun U => ∀ u ∈ U, u x = 0) ≤ numSubspaces r :=
          ((card_filter_le _ _).trans (card_le_card fun U hU =>
            hb U (Multiset.mem_toFinset.1 hU))).trans hT
        omega
    _ = #(hists G X).toFinset * (numSubspaces r + 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hA

theorem linCost_le_aux {r : ℕ} :
    ∀ (l : List V) (X : Finset V), l.Nodup → (∀ x ∈ l, x ∉ X) →
      (∀ i ≤ l.length, cutRank G (X ∪ (l.take i).toFinset) ≤ r) →
      linCost G l X (hists G X) ≤
        l.length * ((Fintype.card V + 1) ^ numSubspaces r * (numSubspaces r + 1))
  | [], _, _, _, _ => by simp [linCost]
  | x :: xs, X, hnd, hdis, hw => by
    obtain ⟨hx, hnd⟩ := List.nodup_cons.1 hnd
    have hX : cutRank G X ≤ r := by simpa using hw 0 (by simp)
    rw [linCost, ← hists_insert G (hdis x List.mem_cons_self)]
    have ih := linCost_le_aux xs (X ∪ {x}) hnd
      (by
        intro y hy
        simp only [mem_union, mem_singleton, not_or]
        exact ⟨hdis y (List.mem_cons_of_mem _ hy), fun h => hx (h ▸ hy)⟩)
      (by
        intro i hi
        have := hw (i + 1) (by simp; omega)
        simp only [List.take_succ_cons, List.toFinset_cons] at this
        convert this using 2
        ext v
        simp)
    have hstep := linStepCost_le G hX x
    simp only [List.length_cons]
    nlinarith [ih, hstep]

/-- **Corollary 1 (running time):** along a linear layout of width at most `r`, the dynamic
program performs at most `N · (N+1)^{N₂(r)} · (N₂(r) + 1)` operations, and
`N₂(r) + 1 ≤ 2^{⌊r²/4⌋+4} + 1 = 2^{O(r²)}`. -/
theorem linCost_le (π : LinearLayout V) {r : ℕ} (hw : π.width G ≤ r) :
    linCost G π.order ∅ (hists G ∅) ≤
      Fintype.card V * ((Fintype.card V + 1) ^ numSubspaces r * (2 ^ (r * r / 4 + 4) + 1)) := by
  have hlen : π.order.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup π.nodup]
    congr
    ext v
    simp [π.mem_order v]
  have := linCost_le_aux G π.order ∅ π.nodup (fun _ _ => notMem_empty _)
    (fun i _ => by
      simpa [LinearLayout.prefixSet] using (π.width_le_iff G).1 hw i)
  rw [hlen] at this
  refine this.trans ?_
  gcongr
  exact numSubspaces_le r

end SubspaceConvolution
