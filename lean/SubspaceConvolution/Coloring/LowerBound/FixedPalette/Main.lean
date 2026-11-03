/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Count
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Width
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Clique
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Padding

/-!
# Appendix H: fixed-palette decision and counting lower bounds

Summary of the formalization of the reduction of Appendix H ("Fixed-palette decision and counting
lower bounds"):

* `Defs`: 3-CNF formulas over the `k × k` grid (`GridCNF`), the graph `graph φ = G_φ` on the
  vertex type `Vtx k m`;
* `Layout`: the supplied layout `layout φ`;
* `Count`: `card_vtx` (number of vertices), `card_coloring` (the counting identity
  `#3-Color(G_φ) = 6 · 2^g · 16^m · #SAT(φ)` with `g = 2k + 3m`) and `colorable_iff` (decision);
* `Width`: `layout_width` (the layout has width at most `2k + 19`);
* `Clique`: the universal clique for palettes with `c > 3` colors;
* `Padding`: placing a general 3-CNF formula on the grid.

The statements below restate the main results.
-/

namespace SubspaceConvolution.FixedPalette

example (k m : ℕ) :
    Fintype.card (Vtx k m) = 3 + (2 * k + 3 * m) * (2 ^ (k + 1) + 1) + 20 * m :=
  card_vtx k m

example {k : ℕ} (hk : 1 ≤ k) (φ : GridCNF k) :
    Fintype.card ((graph φ).Coloring (Fin 3)) =
      6 * 2 ^ (2 * k + 3 * φ.m) * 16 ^ φ.m * φ.numSat :=
  card_coloring hk φ

example {k : ℕ} (hk : 1 ≤ k) (φ : GridCNF k) : (graph φ).Colorable 3 ↔ ∃ α, φ.Satisfies α :=
  colorable_iff hk φ

example {k : ℕ} (φ : GridCNF k) : (layout φ).width (graph φ) ≤ 2 * k + 19 :=
  layout_width φ

example {V : Type*} [Fintype V] (G : SimpleGraph V) (t c : ℕ) :
    Fintype.card ((joinClique G t).Coloring (Fin (t + c))) =
      (t + c).descFactorial t * Fintype.card (G.Coloring (Fin c)) :=
  card_coloring_joinClique G t c

example {V : Type*} (G : SimpleGraph V) (t c : ℕ) :
    (joinClique G t).Colorable (t + c) ↔ G.Colorable c :=
  colorable_joinClique_iff G t c

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (π : LinearLayout V) (t : ℕ) :
    (joinCliqueLayout π t).width (joinClique G t) ≤ π.width G + t :=
  width_joinCliqueLayout G π t

example {n : ℕ} (φ : CNF n) (k : ℕ) (h : n ≤ k * k) :
    (φ.toGrid k h).numSat = 2 ^ (k * k - n) * φ.numSat :=
  numSat_toGrid φ k h

example {n : ℕ} (φ : CNF n) (k : ℕ) (h : n ≤ k * k) :
    (∃ α, (φ.toGrid k h).Satisfies α) ↔ ∃ β, φ.Satisfies β :=
  satisfiable_toGrid_iff φ k h

/-- The reduction for a palette of `c = t + 3 ≥ 3` colors: the graph `G_φ` with a universal
`t`-clique, laid out with the clique first, has width at most `2k + 19 + t`; its `(t + 3)`-colorings
number `(t + 3)!/3! · 6 · 2^g · 16^m · #SAT(φ)` (with `g = 2k + 3m`), and it is `(t + 3)`-colorable
iff `φ` is satisfiable. -/
theorem fixedPalette_reduction {k : ℕ} (hk : 1 ≤ k) (φ : GridCNF k) (t : ℕ) :
    Fintype.card ((joinClique (graph φ) t).Coloring (Fin (t + 3))) =
        (t + 3).descFactorial t * (6 * 2 ^ (2 * k + 3 * φ.m) * 16 ^ φ.m * φ.numSat) ∧
      ((joinClique (graph φ) t).Colorable (t + 3) ↔ ∃ α, φ.Satisfies α) ∧
      (joinCliqueLayout (layout φ) t).width (joinClique (graph φ) t) ≤ 2 * k + 19 + t := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_coloring_joinClique, card_coloring hk]
  · rw [colorable_joinClique_iff, colorable_iff hk]
  · exact (width_joinCliqueLayout _ _ _).trans (Nat.add_le_add_right (layout_width φ) _)

end SubspaceConvolution.FixedPalette
