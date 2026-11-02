/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# Common infrastructure for the lower bounds

* `LinearLayout.toRankDecomposition` — the caterpillar rank-decomposition of a linear layout; its
  nonleaf cuts are the prefixes of the layout and its leaf cuts are singletons of cut-rank at most
  one, so its width is at most `max (width) 1` (paper: "The layout's caterpillar
  rank-decomposition has the same nonleaf cuts and singleton cuts of rank at most one").
* `LayoutGraph` — a uniform type of graphs on `Fin N` with a supplied linear layout, the input type
  of the decision and counting problems; `LayoutGraph.ofGraph` relabels any graph with a layout,
  preserving colorings (`card_coloring_ofGraph`, `colorable_ofGraph_iff`) and the width
  (`width_ofGraph`).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Caterpillars -/

namespace DTree

/-- Append the leaves `ws` to `t` one at a time, as right children. -/
def cat : DTree V → List V → DTree V
  | t, [] => t
  | t, w :: ws => cat (node t (leaf w)) ws

theorem leaves_cat : ∀ (t : DTree V) (ws : List V), (cat t ws).leaves = t.leaves ++ ws
  | t, [] => by simp [cat]
  | t, w :: ws => by
    rw [cat, leaves_cat]
    simp [leaves]

theorem subtrees_cat : ∀ (t : DTree V) (ws : List V), ∀ s ∈ (cat t ws).subtrees,
    s ∈ t.subtrees ∨ (∃ w ∈ ws, s = leaf w) ∨ ∃ i, s.leaves = t.leaves ++ ws.take i
  | t, [], s, hs => Or.inl hs
  | t, w :: ws, s, hs => by
    rw [cat] at hs
    rcases subtrees_cat _ ws s hs with h | ⟨w', hw', rfl⟩ | ⟨i, hi⟩
    · simp only [subtrees, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
      rcases h with rfl | h | rfl
      · exact Or.inr (Or.inr ⟨1, by simp [leaves]⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨w, List.mem_cons_self .., rfl⟩)
    · exact Or.inr (Or.inl ⟨w', List.mem_cons_of_mem _ hw', rfl⟩)
    · refine Or.inr (Or.inr ⟨i + 1, ?_⟩)
      rw [hi]
      simp [leaves]

end DTree

namespace LinearLayout

/-- The caterpillar rank-decomposition of a linear layout (of a nonempty vertex set). -/
def toRankDecomposition (π : LinearLayout V) (v : V) (vs : List V) (h : π.order = v :: vs) :
    RankDecomposition V where
  tree := DTree.cat (.leaf v) vs
  nodup := by
    rw [DTree.leaves_cat]
    simpa [DTree.leaves, ← h] using π.nodup
  mem_leaves w := by
    rw [DTree.leaves_cat]
    have := π.mem_order w
    rw [h] at this
    simpa [DTree.leaves] using this

theorem cutRank_singleton_le (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    cutRank G {v} ≤ 1 :=
  le_of_le_of_eq (matCutRank_le_card (G.adjMatrix F2) {v}) (card_singleton v)

/-- **The caterpillar has width at most `max (layout width) 1`.** -/
theorem width_toRankDecomposition_le (π : LinearLayout V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (vs : List V) (h : π.order = v :: vs) :
    (π.toRankDecomposition v vs h).width G ≤ max (π.width G) 1 := by
  rw [RankDecomposition.width_le_iff]
  intro s hs
  rcases DTree.subtrees_cat _ vs s hs with h1 | ⟨w, -, rfl⟩ | ⟨i, hi⟩
  · simp only [DTree.subtrees, List.mem_singleton] at h1
    subst h1
    exact (cutRank_singleton_le G v).trans (le_max_right _ _)
  · exact (cutRank_singleton_le G w).trans (le_max_right _ _)
  · have : s.leafSet = π.prefixSet (i + 1) := by
      rw [DTree.leafSet, hi, prefixSet, h]
      simp [DTree.leaves]
    rw [this]
    exact (π.cutRank_prefixSet_le_width G _).trans (le_max_left _ _)

end LinearLayout

/-! ### Relabelling onto `Fin N` -/

/-- A graph on `Fin N` together with a supplied linear layout: the input of the coloring problems
in the lower bounds. -/
structure LayoutGraph where
  /-- the number of vertices -/
  N : ℕ
  /-- the graph -/
  G : SimpleGraph (Fin N)
  /-- decidable adjacency -/
  dec : DecidableRel G.Adj
  /-- the supplied linear layout -/
  layout : LinearLayout (Fin N)

namespace LayoutGraph

attribute [instance] LayoutGraph.dec

/-- The width of the supplied layout. -/
noncomputable def width (I : LayoutGraph) : ℕ := I.layout.width I.G

/-- The image of a layout under a bijection. -/
def mapLayout {W : Type*} [Fintype W] (e : V ≃ W) (π : LinearLayout V) : LinearLayout W where
  order := π.order.map e
  nodup := π.nodup.map e.injective
  mem_order w := List.mem_map.2 ⟨e.symm w, π.mem_order _, e.apply_symm_apply w⟩

/-- Relabel a graph with a layout onto `Fin N` (`N = |V|`). -/
noncomputable def ofGraph (G : SimpleGraph V) [DecidableRel G.Adj] (π : LinearLayout V) :
    LayoutGraph where
  N := Fintype.card V
  G := G.comap (Fintype.equivFin V).symm
  dec i j := inferInstanceAs (Decidable (G.Adj ((Fintype.equivFin V).symm i)
    ((Fintype.equivFin V).symm j)))
  layout := mapLayout (Fintype.equivFin V) π

variable (G : SimpleGraph V) [DecidableRel G.Adj] (π : LinearLayout V)

/-- Relabelling preserves the number of proper colorings. -/
theorem card_coloring_ofGraph (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card ((ofGraph G π).G.Coloring α) = Fintype.card (G.Coloring α) := by
  classical
  show Fintype.card ((G.comap (Fintype.equivFin V).symm).Coloring α) = _
  rw [Fintype.card_congr (coloringEquivFun _ α), Fintype.card_congr (coloringEquivFun G α)]
  let e := Fintype.equivFin V
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e.symm (Equiv.refl α)) ?_)
  intro f
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_apply,
    id_eq, SimpleGraph.comap_adj]
  constructor
  · intro hf x y hxy
    have := hf (x := e x) (y := e y) (by simpa [e] using hxy)
    simpa [e] using this
  · intro hf i j hij
    simpa [e] using hf hij

theorem colorable_ofGraph_iff (c : ℕ) : (ofGraph G π).G.Colorable c ↔ G.Colorable c := by
  classical
  rw [SimpleGraph.Colorable, SimpleGraph.Colorable, ← Fintype.card_pos_iff,
    ← Fintype.card_pos_iff, card_coloring_ofGraph]

/-- Relabelling preserves cut-ranks. -/
theorem cutRank_map {W : Type*} [Fintype W] [DecidableEq W] (e : V ≃ W) (H : SimpleGraph W)
    [DecidableRel H.Adj] (hH : ∀ x y, H.Adj (e x) (e y) ↔ G.Adj x y) (X : Finset V) :
    cutRank H (X.map e.toEmbedding) = cutRank G X := by
  unfold cutRank matCutRank
  -- the linear equivalence `F₂^V ≃ F₂^W` induced by `e`
  let Φ : (V → F2) ≃ₗ[F2] (W → F2) := LinearEquiv.funCongrLeft F2 F2 e.symm
  have hΦ : ∀ (v : V → F2) (w : W), Φ v w = v (e.symm w) := fun v w => rfl
  have hrow : ∀ x, Φ (cutRow (G.adjMatrix F2) X x) =
      cutRow (H.adjMatrix F2) (X.map e.toEmbedding) (e x) := by
    intro x
    funext w
    rw [hΦ]
    simp only [cutRow_apply, mem_map_equiv, SimpleGraph.adjMatrix_apply]
    obtain ⟨y, rfl⟩ := e.surjective w
    simp [hH]
  have hspace : cutSpace (H.adjMatrix F2) (X.map e.toEmbedding) =
      (cutSpace (G.adjMatrix F2) X).map (Φ : (V → F2) →ₗ[F2] (W → F2)) := by
    unfold cutSpace
    rw [Submodule.map_span, ← Set.image_comp]
    congr 1
    ext u
    simp only [Set.mem_image, mem_coe, mem_map_equiv, Function.comp_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨e.symm w, hw, by rw [LinearEquiv.coe_coe, hrow]; simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, by simpa using hx, by rw [LinearEquiv.coe_coe, hrow]⟩
  rw [hspace, LinearEquiv.finrank_map_eq]

/-- Relabelling preserves the width of the layout. -/
theorem width_ofGraph : (ofGraph G π).width = π.width G := by
  let eN : V ≃ Fin (ofGraph G π).N := Fintype.equivFin V
  have hpre : ∀ i, (ofGraph G π).layout.prefixSet i = (π.prefixSet i).map eN.toEmbedding := by
    intro i
    ext j
    show j ∈ (List.take i (List.map eN π.order)).toFinset ↔ _
    rw [← List.map_take]
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_map, Equiv.coe_toEmbedding,
      LinearLayout.prefixSet]
  have hcut : ∀ X : Finset V, cutRank (ofGraph G π).G (X.map eN.toEmbedding) = cutRank G X :=
    fun X => cutRank_map G eN (ofGraph G π).G
      (fun x y => by
        have h1 : ∀ z, (Fintype.equivFin V).symm (eN z) = z := fun z =>
          (Fintype.equivFin V).symm_apply_apply z
        show G.Adj ((Fintype.equivFin V).symm (eN x)) ((Fintype.equivFin V).symm (eN y)) ↔
          G.Adj x y
        rw [h1, h1]) X
  apply le_antisymm
  · rw [width, LinearLayout.width_le_iff]
    intro i
    calc cutRank (ofGraph G π).G ((ofGraph G π).layout.prefixSet i)
        = cutRank G (π.prefixSet i) := by rw [hpre]; exact hcut _
      _ ≤ π.width G := π.cutRank_prefixSet_le_width G i
  · rw [LinearLayout.width_le_iff]
    intro i
    calc cutRank G (π.prefixSet i)
        = cutRank (ofGraph G π).G ((ofGraph G π).layout.prefixSet i) := by
          rw [hpre]; exact (hcut _).symm
      _ ≤ (ofGraph G π).width :=
          (ofGraph G π).layout.cutRank_prefixSet_le_width (ofGraph G π).G i

end LayoutGraph

end SubspaceConvolution
