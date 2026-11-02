/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Correct
import SubspaceConvolution.Coloring.LowerBound.Counter.Size
import SubspaceConvolution.Coloring.LowerBound.Counter.Width

/-!
# Appendix C: the counter reduction

Main results (namespace `SubspaceConvolution.Counter`):

* `colorable_iff (I : MinCSP) (hI : I.Normalized) :
    (graph I).Colorable (eta I) ↔ I.Satisfiable` — Lemma C.3 (`xp:correct`);
* `card_Vtx (I : MinCSP) : Fintype.card (Vtx I) = d I * Q I + (Q I - I.W) + (I.p + numI I) +
    numA I * (d I * I.n) + numI I + numA I * (eta I - I.n)` and the bound `card_Vtx_le`;
  `card_row_label`: each row `B_i` has `Q/h` vertices of each label `(e_i, a)`;
* `eta_le (I : MinCSP) : eta I ≤ Q I + I.p + ∑ C, ∑ R, ∑ x ∈ I.scope C, (I.n - I.thr C R x)`
  (with equality, `eta_eq`);
* `layout_width (I : MinCSP) (hI : I.Normalized) : (layout I).width (graph I) ≤ 2 * d I + 12`
  — Lemma C.4 (`xp:width`).

Files:
* `Defs` — the source problem, the parameters, the graph, `eta` and the layout;
* `Lemmas` — parameters, cardinalities, the entry test, adjacency;
* `Forward`, `Backward`, `Correct` — Lemma C.3;
* `Size` — the vertex count;
* `WidthSetup`, `WidthRest`, `WidthRestC`, `Width` — Lemma C.4.
-/
