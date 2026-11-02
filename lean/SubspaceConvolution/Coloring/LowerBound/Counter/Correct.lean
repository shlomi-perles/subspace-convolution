/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Forward
import SubspaceConvolution.Coloring.LowerBound.Counter.Backward

/-!
# Lemma C.3 (`xp:correct`): correctness of the counter reduction

The graph `graph I` is `η`-colorable if and only if the (normalized) source instance `I` of
4-Monotone min-CSP is satisfiable.
-/

namespace SubspaceConvolution.Counter

/-- **Lemma C.3.** The graph is `η`-colorable if and only if the source instance is
satisfiable. -/
theorem colorable_iff (I : MinCSP) (hI : I.Normalized) :
    (graph I).Colorable (eta I) ↔ I.Satisfiable :=
  ⟨satisfiable_of_colorable hI, colorable_of_satisfiable hI⟩

end SubspaceConvolution.Counter
