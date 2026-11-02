/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.WidthRestC

/-!
# Lemma C.4 (`xp:width`): the width of the layout

The layout `layout I` (rows, then `B_*`, then for each constraint `C`: `s_C`, its palette blocks,
its mini-constraints) has width at most `2d + 12`:

* the register edges have cut-rank at most `2d` (`matCutRank_Mreg_le`);
* at most one test clique is split (`matCutRank_Mtest_le`, `+1`);
* at most one palette block is split; its crossing private edges form a complete bipartite
  graph (`matCutRank_Mpriv_le`, `+1`);
* the remaining edges have at most ten distinct nonzero future neighborhoods
  (`matCutRank_Mrest_le_caseC`; at most one in the initial cuts, cases A and B).
-/

open Finset

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

/-- Every cut of the layout has cut-rank at most `2d + 12`. -/
theorem cutRank_le_of_isCut (hI : I.Normalized) {X : Finset (Vtx I)} (hX : IsCut X) :
    cutRank (graph I) X ≤ 2 * d I + 12 := by
  have hreg := matCutRank_Mreg_le hX
  have htest := matCutRank_Mtest_le hX
  have hpriv := matCutRank_Mpriv_le hX
  have hrest : matCutRank (Mpart I .rest) X ≤ 10 := by
    by_cases hC : ∃ C, Vtx.sel C ∈ X
    · -- a cut in the constraint part: `C₀` is the last constraint whose selector is processed
      have hne : (univ.filter fun C => Vtx.sel C ∈ X).Nonempty := by
        obtain ⟨C, hC⟩ := hC
        exact ⟨C, by simp [hC]⟩
      set C₀ := (univ.filter fun C => Vtx.sel C ∈ X).max' hne with hC₀
      have hsel : Vtx.sel C₀ ∈ X := by
        have := (univ.filter fun C => Vtx.sel C ∈ X).max'_mem hne
        simpa [hC₀] using this
      have hmax : ∀ C, Vtx.sel C ∈ X → C ≤ C₀ := fun C h =>
        (univ.filter fun C => Vtx.sel C ∈ X).le_max' C (by simp [h])
      exact matCutRank_Mrest_le_caseC hX hsel hmax hI
    · push Not at hC
      by_cases hA : ∀ v ∈ X, v.isRow = true
      · -- a cut inside the register
        exact (matCutRank_Mrest_le_caseA hX hA).trans (by norm_num)
      · -- a cut inside `B_*`
        push Not at hA
        obtain ⟨v₀, hv₀, hv₀r⟩ := hA
        exact (matCutRank_Mrest_le_caseB hX hv₀ (by simpa using hv₀r) hC).trans (by norm_num)
  have := cutRank_le_parts X
  omega

/-- **Lemma C.4.** The layout of the construction has width at most `2d + 12`. -/
theorem layout_width (I : MinCSP) (hI : I.Normalized) :
    (layout I).width (graph I) ≤ 2 * d I + 12 :=
  ((layout I).width_le_iff (graph I)).2 fun i => cutRank_le_of_isCut hI (isCut_prefixSet i)

end SubspaceConvolution.Counter
