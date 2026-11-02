/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic
import SubspaceConvolution.Coloring.MatchingDP
import SubspaceConvolution.Coloring.Profiles
import SubspaceConvolution.Coloring.MergeBijection
import SubspaceConvolution.Coloring.TreeDP
import SubspaceConvolution.Coloring.ChromaticPolynomial
import SubspaceConvolution.Coloring.LinearDP
import SubspaceConvolution.Coloring.Reconstruct
import SubspaceConvolution.Coloring.SubspaceCount
import SubspaceConvolution.Coloring.Runtime
import SubspaceConvolution.Coloring.Completion
import SubspaceConvolution.Coloring.LowerBound.Common
import SubspaceConvolution.Coloring.LowerBound.Complexity
import SubspaceConvolution.Coloring.LowerBound.Arith
import SubspaceConvolution.Coloring.LowerBound.LittleO
import SubspaceConvolution.Coloring.LowerBound.Counter.Main
import SubspaceConvolution.Coloring.LowerBound.CounterSize
import SubspaceConvolution.Coloring.LowerBound.TheoremC1
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Main
import SubspaceConvolution.Coloring.LowerBound.TheoremD
import SubspaceConvolution.Circuit.SLP
import SubspaceConvolution.Circuit.Arith
import SubspaceConvolution.Circuit.Morgenstern
import SubspaceConvolution.Transform.Defs
import SubspaceConvolution.Transform.Crossing
import SubspaceConvolution.Transform.Fourier
import SubspaceConvolution.Transform.Count
import SubspaceConvolution.Transform.Step
import SubspaceConvolution.Transform.Algorithm
import SubspaceConvolution.Transform.Incidence
import SubspaceConvolution.Transform.Kernel
import SubspaceConvolution.Transform.Applications
import SubspaceConvolution.Transform.Rectangular
import SubspaceConvolution.Transform.Grassmann
import SubspaceConvolution.Transform.Spectral
import SubspaceConvolution.Transform.Invariant
import SubspaceConvolution.Transform.AppECost
import SubspaceConvolution.Transform.Mobius
import SubspaceConvolution.Transform.Integer
import SubspaceConvolution.Transform.LowerBound
import SubspaceConvolution.Transform.Misc
import SubspaceConvolution.Coloring.CompletionCost

/-!
# SubspaceConvolution

Lean verification of "A Fast Algorithm for Subspace Convolution" (S. A. Perles and
O. Weinstein):
* `Circuit/` — the cost model (straight-line programs);
* `Transform/` — the fast subspace transforms and their applications (Part I);
* `Coloring/` — graph coloring by subspace profiles and its lower bounds (Part II).

See `README.md` for the map from the paper's statements to the Lean declarations.
-/
