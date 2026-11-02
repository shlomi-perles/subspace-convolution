# Lean 4 formalization

This directory is a complete formalization, in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of the paper

> Shlomo A. Perles and Omri Weinstein. **A Fast Algorithm for Subspace Convolution.**

Every numbered result of the paper is stated and proved in Lean:

| Part | Results |
|---|---|
| Fast transforms (Sections 1–5) | Theorems 1.1, 1.2, 1.4, 5.1; Lemmas 2.1, 3.1 |
| Appendices | Corollary F.1; Theorem G.1; the estimates of Appendices A and B; the applications of Appendix E |
| Graph coloring (Section 7) | Lemma 7.1; Theorem 7.1; Corollary 7.2; Proposition 7.3 |
| Lower bounds (Appendices C, D) | Lemmas C.3, C.4; Theorems C.1, D.1, D.2 (as running-time transfers from their hardness hypotheses) |

The unnumbered claims of Sections 1–5 and of the appendices (equations, counting estimates,
applications, the footnote of Section 1) are formalized as well.
[`docs/unverified.tex`](docs/unverified.tex) lists precisely what is *not* covered: modelling
choices, the claims about index construction and bit costs that concern a machine model rather
than operation counts, and the hypotheses of the conditional lower bounds.

## Checking the proofs

Install [elan](https://github.com/leanprover/elan), then run, in this directory (`lean/`):

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake env lean Audit.lean | tee audit.log
```

```bash
python3 scripts/check_axioms.py audit.log Audit.lean
```

* The toolchain is pinned by `lean-toolchain` (Lean `v4.36.0-rc2`). Mathlib is pinned to commit
  `dd67281f` by `lakefile.toml` and `lake-manifest.json`.
* `lake exe cache get` downloads the compiled Mathlib. Building the project on top of it takes a
  few minutes.
* `Audit.lean` prints the axioms of 132 main declarations, and `scripts/check_axioms.py` checks
  that each uses only Lean's three standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
* The sources contain no `sorry`, `admit`, `native_decide` or added `axiom`.
* [GitHub Actions](../.github/workflows/lean.yml) runs the build, this source check and the
  axiom audit on every pull request and every push to `main` that changes `lean/`.

## Where to start reading

* `SubspaceConvolution/Transform/Defs.lean` defines the objects of the paper: subspace tables,
  the zeta transform `Z_{n,k}` and its inverse and transposes, the incidence transform
  `I^{a,b}`, intersection kernels, span convolution, `M_q(n,k)`, `|Gr(n,j)|`.
* `SubspaceConvolution/Circuit/Defs.lean` and `Circuit/SLP.lean` define the cost model:
  straight-line programs, and `LinCost C M s`.
* The tables below give, for each statement of the paper, its Lean name and file. Paths are
  relative to `SubspaceConvolution/`.
* Every file has a module docstring relating it to the paper.

## Part I — the transforms (Sections 1–5, Appendices A, B, E, F, G)

### How costs are counted

The paper counts arithmetic operations (ring additions, subtractions, multiplications). Lean counts
**gates of straight-line programs** (`Circuit/SLP.lean`, `Circuit/Arith.lean`):

* `LinCost C M s` — the map `M : (I → R) → (O → R)` is computed by a *linear* straight-line program
  with at most `s` gates `z = a·x + b·y`, where `x, y` are inputs or earlier gates and the constants
  `a, b` lie in `C`.
  - One gate is at most three ring operations, so gate counts are operation counts up to a factor 3.
  - With `C = {c ∈ ℂ : |c| ≤ 1}` this is exactly the bounded-coefficient model of Theorem G.1.
  - All transforms of the paper are linear, and their algorithms are linear programs of this kind.
* `ArithCost M s` — a general arithmetic program, which may also multiply two computed values.
  It is used where the paper's computation is bilinear: span convolution, kernels whose
  coefficients are inputs, and the count `∑ f(U) B_g(U)` of Proposition 7.3.
* Programs are non-uniform. One program is built for each `n`, `k` (and coefficient ring), as in
  the paper's operation counts. The paper's separate claim that *constructing* the index tables
  takes table size times `poly(n)` time (Appendix F, first paragraph) concerns a machine model and
  is not formalized.
* Constants of the `O_q(·)` bounds are explicit and depend only on `q` (on `K`), never on the
  coefficient ring, `n`, `k`, `a`, `b`.

### Map from the paper to Lean

| Paper | Lean declaration | File |
|---|---|---|
| Truncated zeta transform `Z_{n,k}`, its inverse and transposes; incidence transform `I^{a,b}`; intersection kernels; span convolution | `zeta`, `zetaInv`, `zetaT`, `zetaTInv` (+ inverse identities), `incid`, `incidT`, `kernelApply`, `gDist`, `grassGraph`, `spanConv`, `containT` | `Transform/Defs.lean` |
| **Lemma 2.1** (crossing subspaces) | `HypData.existsUnique_lift`, `lift_inf_H`, `finrank_lift`, `lift_le_lift_iff`, `map_le_lift_iff`, `HypData.split` | `Transform/Crossing.lean` |
| Equations (cut) and (rank-cut) | `HypData.containT_split_inl`, `HypData.containT_split_inr` | `Transform/Crossing.lean` |
| Fourier transform on `H/B`, equations (fft), (ifft), character orthogonality | `fourierQ`, `fourierQInv`, `fourierQInv_fourierQ`, `fourierQ_fourierQInv`, `sum_freq_psi` | `Transform/Fourier.lean` |
| Length-`q` row–column FFT, `O_q((d+1)|H/B|)` operations | `Circuit.dft_cost`, `Circuit.idft_cost`, `fourierQ_eq_dft` | `Circuit/SLP.lean`, `Transform/Fourier.lean` |
| **Lemma 3.1** (affine Fourier identity), equation (block) | `fourier_affineT`, `affineT_eq` | `Transform/Fourier.lean` |
| Section 3.4: `R[t]/(1+t+⋯+t^{p-1})`, `ψ(x) = ζ^{Tr x}`; over `ℂ`, `ψ(t) = exp(2πi Tr(t)/p)` | `ExtRing`, `ExtRing.basis`, `ExtRing.basis_repr_algebraMap`, `FourierData.ext`, `FourierData.complex`, `FourierData.complex_consts` | `Transform/Fourier.lean` |
| One step of the recursion as a circuit; equation (inverse) | `containT_step`, `zetaInv_step` | `Transform/Step.lean` |
| Transposition principle (Section 3.3) | `Circuit.LinCost.transpose` | `Circuit/SLP.lean` |
| Base change from `R[t]/(…)` to `R` | `Circuit.LinCost.baseChange` | `Circuit/SLP.lean` |
| **Theorem 1.1** (Fast Subspace Summation), `O_q(nk M_q(n,k))` and `O_q(M log M)` | `fast_subspace_summation`, `fast_subspace_summation_log` (over a Fourier ring: `zeta_linCost`, `zetaInv_linCost`) | `Transform/Algorithm.lean` |
| **Theorem 1.2** (incidence), `O_q(S log S)` | `fast_incidence` (over a Fourier ring: `incid_linCost`) | `Transform/Incidence.lean` |
| Appendix A: (gaussian), (pascal), annihilator symmetry, `|Gr(n,r)| = Θ_q(q^{r(n-r)})`, `N_q(n) = Θ_q(q^{⌊n²/4⌋})`, (truncated-size), (cover-pairs) | `gr_mul_prod`, `gr_succ_succ`, `gr_symm`, `pow_le_gr`, `gr_le`, `pow_le_numLE_self`, `numLE_self_le`, `numLE_le_two_mul_gr`, `pow_le_coverPairs`, `coverPairs_le` | `Transform/Count.lean` |
| Section 3.3: (count), `M_q(n,k) - 2M_q(n-1,k) ≥ 0`, `nk = O(log M_q(n,k))` | `numLE_count`, `two_mul_numLE_le`, `mul_le_log_numLE` | `Transform/Count.lean` |
| Appendix B: budget, (slack), `n min(a,n-b) ≤ 2 log_q S` | `incidBound`, `slack`, `incid_budget_step`, `incidBound_le` | `Transform/Count.lean` |
| Introduction: cover pairs `Θ(N_q(n) q^{n/2}) = Θ(N^{1+1/√log_q N})`; Section 1 footnote `‖x_U − x_W‖² = 2(q^k − q^{dim(U∩W)})/(q−1)`; Section 5.3 count `∑_j |Gr(n,j)|[j] = Θ_q(q^k N)` | `coverPairs_theta`, `rpow_inv_sqrt_logb_theta`, `coverPairs_theta_rpow`, `sqDist_lineIndicator`, `intersectionKernel_radial`, `card_inclusions`, `card_inclusions_theta` | `Transform/Misc.lean` |
| Corollary (Fast Subspace Convolution) and the variants of Section 5.1 | `zetaAll_spanConv`, `fast_spanConv`, `zetaAllT_interConv`, `fast_interConv`, `directConv_eq_coeff` | `Transform/Applications.lean` |
| **Theorem 5.1** (counting exact spans), equation (exact-span) | `spanTable`, `zetaAll_spanTable`, `two_pow_card_eq_sum_spanCount`, `spanCount_eq_zetaAllInv`, `fast_span_count` | `Transform/Applications.lean` |
| Section 5.3: equations (moments), (kernel-coefficients), (two-transforms); annihilators preserve distance | `moments`, `kernelCoeff_spec`, `kernelApply_eq_zeta`, `finrank_dualAnnihilator_inf`, `kernelApply_dual` | `Transform/Kernel.lean` |
| **Theorem 1.4** (fast multiplication on the Grassmann graph) | `fast_kernel` (coefficients fixed), `fast_kernel_arith` (coefficients as inputs) | `Transform/Kernel.lean` |
| Section 5.3: distance formula in `J_q(n,k)`; intersection kernels = `GL(n,q)`-invariant matrices | `grassGraph_dist`, `grassGraph_connected`, `exists_linearEquiv_map_pair`, `invariant_iff_exists_dist` | `Transform/Grassmann.lean` |
| Appendix E: distance sums, equation (profile); distances to codes; rectangular kernels (rect-moments) | `distSum`, `moment_profile`, `interSum_backsubst`, `fast_distance_sums`, `isLeast_distSum_pos`, `isLeast_minDist`, `rect_moments` | `Transform/Applications.lean` |
| Appendix E: rectangular kernels (different input and output dimensions): back-substitution, annihilators, `S poly(n)` cost (`C (n+1)³ S`); unions of dimensions `O_q((n+1)³ N_q(n))` | `rectKernel`, `rectKernel_eq_sum_incid`, `rectKernel_dual`, `fast_rectKernel`, `fast_rectInterSum`, `allKernel`, `allKernel_eq_zetaAll`, `fast_allKernel` | `Transform/Rectangular.lean` |
| Appendix E: spectral projections: eigenvalues `θ_j = q[k][n-k] - [j][n-j+1]` of `D₁` (proved, not cited), `θ_j - θ_{j+1} = q^j[n-2j]`, `∏_j (D₁ - θ_j) = 0`, projections `P_j(D₁)`, cost `O_q((d+1)N log N)` | `eigZ_sub_succ`, `eigval_injOn`, `adjEnd_incid_succ`, `aeval_adjEnd_eq_zero`, `specProj`, `sum_specProj`, `adjEnd_mul_specProj`, `specProj_mul_specProj`, `specProj_decomp`, `specComponents_linCost` | `Transform/Spectral.lean`, `Transform/AppECost.lean` |
| Appendix E: invariant linear systems, equation (small-system): `K` invertible iff `det B ≠ 0`; `Bc = e₀` gives `K⁻¹`; costs | `smallSystem`, `kernelApply_orbitInd`, `bijective_kernelApply_iff`, `kernelApply_inverse`, `smallSystem_linCost`, `kernelInverse_linCost` | `Transform/Invariant.lean`, `Transform/AppECost.lean` |
| Möbius values `(-1)^j q^{j(j-1)/2}` (proof of Corollary F.1) | `zetaInv_apply`, `zetaTInv_apply`, `mobius_sum` | `Transform/Mobius.lean` |
| **Corollary F.1** (exact integer and modular evaluation) | `exact_integer_zeta`, `exact_integer_zetaInv`, `exact_integer_zetaT`, `exact_integer_zetaTInv`, `exact_integer_incid`, `exact_integer_incidT` | `Transform/Integer.lean` |
| **Theorem G.1** (matching lower bound), Morgenstern's argument | `incidence_lower_bound`, `incidence_lower_bound_attained`, `LowerBoundAux.abs_det_incMat_ge`, `Circuit.morgenstern` | `Transform/LowerBound.lean`, `Circuit/Morgenstern.lean` |

## Part II — graph coloring (Section 7, Appendices C, D)

### Map from the paper to Lean

| Paper | Lean declaration | File |
|---|---|---|
| Binary cut-rank `ρ_G(X)`, `W_X`, linear layouts, rank-decompositions and their widths | `cutRank`, `cutSpace`, `LinearLayout.width`, `RankDecomposition.width` | `Coloring/Basic.lean` |
| Color partitions, profiles `U_X(C)` | `IsColorPartition`, `profile` | `Coloring/Basic.lean` |
| **Lemma 7.1**: β is well defined; classes are compatible iff β(U,V)=0; parent profiles are π₁(U)+π₂(V) | `bilin_congr_left/right`, `compatible_profile_iff`, `profile_eq_map`, `profile_union` | `Coloring/Profiles.lean` |
| Parent partitions ↔ (child partitions, compatible partial matching) | `ofTriple`, `ofTriple_restrict`, `restrictL_ofTriple`, `matchOf_parentParts`, `hist_ofTriple` | `Coloring/MergeBijection.lean` |
| Merge recurrence (hist-row)/(hist-weight) with weights `b(V)` | `MergeData.run`, `MergeData.run_spec` | `Coloring/MatchingDP.lean` |
| **Theorem 7.1**, correctness of the merge and of the whole DP | `hists_union`, `treeDP`, `treeDP_eq_hists`, `count_treeDP_root` | `Coloring/TreeDP.lean` |
| (chromatic-falling) `P_G(z) = Σ a_t (z)_t`, chromatic number = least `t` with `a_t > 0` | `card_coloring_eq_sum`, `chromaticPolynomial`, `eval_chromaticPolynomial`, `eq_chromaticPolynomial_of_eval`, `chromaticNumber_eq_sInf` | `Coloring/ChromaticPolynomial.lean` |
| **Theorem 7.1**, outputs: chromatic polynomial and chromatic number read off the DP | `chromaticPolynomial_eq_treeDP`, `chromaticNumber_eq_treeDP` | `Coloring/ChromaticPolynomial.lean` |
| **Theorem 7.1**, an optimal coloring by backtracking | `realize`, `exists_optimal_of_treeDP` | `Coloring/Reconstruct.lean` |
| **Theorem 7.1**, running time `N^{O(N₂(r))} = N^{2^{r²/4+O(1)}}` | `treeCost_le`, `treeCost_le_pow` (`≤ N^{11·N₂(r)} ≤ N^{2^{⌊r²/4⌋+8}}`) | `Coloring/Runtime.lean` |
| **Corollary 7.2**, transitions (lin:fresh)/(lin:reuse) and correctness | `linStep`, `hists_insert`, `linDP_layout`, `chromaticPolynomial_eq_linDP`, `chromaticNumber_eq_linDP` | `Coloring/LinearDP.lean` |
| **Corollary 7.2**, running time `(N+1)^{N₂(r)} 2^{O(r²)} N^{O(1)}` | `linCost_le` | `Coloring/Runtime.lean` |
| **Proposition 7.3**: labels `p_x, q_y`; colorings combine iff profiles are orthogonal; `Σ_U f(U) B_g(U)` counts colorings; `B_g = (Z^{⊗c} g)(U^⊥)`; coordinatewise evaluation; cost `O(S log S)` | `exists_cutLabels`, `proper_iff_profiles`, `card_coloring_eq_completionSum`, `completionSum_eq_zetaOn`, `zetaOn_univ_eq_foldr`; cost: `fast_completionSum`, `fast_completion_count` | `Coloring/Completion.lean`, `Coloring/CompletionCost.lean` |
| **Appendix A**: `|Gr(n,j)|·∏(q^j−q^i) = ∏(q^n−q^i)`, `2^{⌊r²/4⌋} ≤ N₂(r) ≤ 2^{⌊r²/4⌋+4}` | `card_finrank_eq_mul_prod`, `numSubspaces_le`, `le_numSubspaces`, `card_submodules_le_of_finrank_le` | `Coloring/SubspaceCount.lean` |
| **Lemma C.3**: `G_I` is η-colorable iff the min-CSP instance is satisfiable | `Counter.colorable_iff` | `Coloring/LowerBound/Counter/Correct.lean` |
| **Lemma C.4**: the layout has cut-rank at most `2d+12` | `Counter.layout_width` | `Coloring/LowerBound/Counter/Width.lean` |
| Size of the counter reduction, `N ≤ g(k)(n+1)^6` | `Counter.card_Vtx`, `Counter.card_Vtx_le_poly` | `Coloring/LowerBound/Counter/Size.lean`, `Coloring/LowerBound/CounterSize.lean` |
| Exponent arithmetic `2^{r²/4−17r} ≤ max{1, k·2^{−20s−189}}` | `two_rpow_b_le`, `d_le_sqrt_log`, `tendsto_ratio_zero` | `Coloring/LowerBound/Arith.lean` |
| **Theorem C.1** | `Counter.reduction_spec`, `Counter.chromatic_lower_bound` | `Coloring/LowerBound/TheoremC1.lean` |
| **Theorem 1.3 (informal)** | the Theorem 7.1 rows (algorithm) together with Theorem C.1 (optimality of `1/4`) | — |
| (cnt:identity) `#3-Color(G_φ) = 6·2^g·16^m·#SAT(φ)` | `FixedPalette.card_coloring` | `Coloring/LowerBound/FixedPalette/Count.lean` |
| Cut-rank `≤ 2k+19`, vertex count `3+g(2^{k+1}+1)+20m` | `FixedPalette.layout_width`, `FixedPalette.card_vtx` | `Coloring/LowerBound/FixedPalette/Width.lean`, `Coloring/LowerBound/FixedPalette/Count.lean` |
| `c > 3`: universal `(c−3)`-clique (factor `c!/3!`, width `+ (c−3)`); padding to `k²` variables (factor `2^{k²−n}`) | `card_coloring_joinClique`, `colorable_joinClique_iff`, `width_joinCliqueLayout`, `numSat_toGrid` | `Coloring/LowerBound/FixedPalette/Clique.lean`, `Coloring/LowerBound/FixedPalette/Padding.lean` |
| **Theorems D.1, D.2** | `FixedPalette.reduction_spec`, `fixed_palette_lower_bound`, `fixed_palette_counting_lower_bound`, `caterpillar_width` | `Coloring/LowerBound/TheoremD.lean` |
| Linear layout → caterpillar rank-decomposition of the same width | `LinearLayout.toRankDecomposition`, `width_toRankDecomposition_le` | `Coloring/LowerBound/Common.lean` |

### Modelling decisions (read before relying on the statements)

1. **Rank-decompositions are rooted binary trees** whose leaves are the vertices (`RankDecomposition`).
   - Each subtree's leaf set is a cut, and the width is the maximum cut-rank over subtrees.
   - This is exactly what the paper uses after "suppress degree-two vertices of the decomposition
     and subdivide an edge to root it", and the set of cuts is the same.
   - The conversion from unrooted subcubic trees is not formalized.
2. **Running time is counted in arithmetic operations of an explicit model of the aggregated DP**,
   not in bit operations.
   - The model keeps the sets of distinct states `(b, H)` (`MergeData.stepStates`) and counts one
     transition per state and choice.
   - The paper's remark that counts have `O(N log N)` bits is not formalized.
3. **Proposition 7.3** is proved with the cost of Theorem 1.1 (Part I) plugged in:
   `fast_completionSum` (the sums `B_g`) and `fast_completion_count` (the count `∑_U f(U) B_g(U)`)
   give `O(S log S)` gates over any commutative ring in which 2 is invertible. The identity
   `B_g = (Z^{⊗c} g)(U^⊥)`, the coordinatewise evaluation and the counting identity are in
   `Completion.lean`.
4. **The ETH lower bounds are proved as running-time transfers in an abstract cost model**
   (`CostModel`: `Runs f t`, monotone in `t` and closed under composition).
   - Every machine model is such a cost model.
   - The theorems assume, in the model, the paper's hardness hypothesis: ETH for D.1, #ETH for
     D.2, and Lemma C.2 of FGLSZ19 for C.1.
   - They also assume that the explicit reduction is computable within the stated time:
     `2^{O(k)} poly(m)` for Appendix D, and `G(k)(n+1)^{C}` for Appendix C. For D.2 they assume in
     addition that dividing by the known factor of the counting identity takes no more than that.
   - Everything else is proved: correctness, exact counts, widths, sizes, and the asymptotic
     arithmetic (`o(r²)` to `o(n)`, the `2^{r²/4−17r}` bound, `n^{o(k)}`).
   - Time bounds are arbitrary real functions `f`. The paper's "computable `f`" restriction is
     dropped on both sides, so hypothesis and conclusion stay in the same form.
5. **Appendix D construction.** The clause-local A-groups are created once per literal occurrence
   instead of once per pair `(i, j ∈ J_i)`. So the number of groups is `g = 2k + 3m`, where the
   paper has `g = 2k + Σ_i |J_i| ≤ 2k + 3m`. The counting identity, the vertex count
   `3 + g(2^{k+1}+1) + 20m` and the width bound `2k + 19` are proved for this graph in exactly the
   paper's form. Here `k = max(1, ⌈√n⌉)`.
6. **Appendix C construction.** This is exactly the paper's graph, up to naming vertices. The
   `Q/h` register vertices of label `(e_i, a)` are indexed by the pairs (matrix `A` with row `i`
   equal to `a`, copy `< n`).

## A note on ETH

In October 2026 Anthropic published a Lean-checked proof that ETH is false
(`github.com/anthropics/formal-math`, folder `eth/`). It is an unreviewed research artifact.
- If it holds, the conditional statements of Theorems C.1, D.1 and D.2 are vacuously true.
- The reductions formalized here still give unconditional running-time transfers, which is how
  the paper itself frames them ("The reduction therefore remains a relationship between running
  times even if the assumed lower bound for SAT changes").
- The `reduction_spec` theorems and `CostModel.Runs.reduce` state exactly these transfers.

## Layout

```
SubspaceConvolution.lean      imports the whole library
SubspaceConvolution/
  Circuit/                    the cost model
    Defs.lean, Run.lean         straight-line programs, evaluation, combinators
    SLP.lean                    LinCost: composition, block sums, dense maps, FFT, base change
    Transpose.lean              the transposition principle
    Arith.lean                  arithmetic programs with product gates (ArithCost)
    Morgenstern.lean            Morgenstern's bounded-coefficient bound
  Transform/                  Part I
    Defs.lean                   subspace tables, the transforms, kernels, Fourier data, counts
    Crossing.lean               Lemma 2.1, the hyperplane split, equations (cut)/(rank-cut)
    Fourier*.lean               Fourier on quotients, Lemma 3.1, eq. (block), coefficient rings
    Count*.lean                 Appendix A for general q, eq. (count), Appendix B budget
    Step*.lean                  one recursion step as a circuit, equation (inverse)
    Algorithm.lean, AlgAux.lean Theorem 1.1
    Incidence.lean              Theorem 1.2
    Kernel*.lean                Theorem 1.4
    Applications.lean           convolutions, Theorem 5.1, distance sums, codes
    Rectangular.lean, RectAux.lean  rectangular kernels, unions of dimensions (Appendix E)
    Grassmann.lean, GrAux.lean  distance formula, GL-transitivity, invariant kernels
    Spectral.lean, Invariant.lean, AppECost.lean  spectral projections, invariant systems
    Mobius.lean, Integer.lean   Möbius coefficients, Corollary F.1
    LBAux.lean, LowerBound.lean Theorem G.1
    Misc.lean                   footnote of Section 1, Section 5.3 count, cover-pair asymptotics
  Coloring/                   Part II
    Basic.lean                  cut-rank, layouts, rank-decompositions, color partitions, profiles
    Profiles.lean               Lemma 7.1
    MatchingDP.lean, MergeBijection.lean, TreeDP.lean   Theorem 7.1 (correctness)
    ChromaticPolynomial.lean, Reconstruct.lean          outputs of Theorem 7.1
    LinearDP.lean               Corollary 7.2
    SubspaceCount.lean          Appendix A for q = 2: N₂(r)
    Runtime.lean                running times of Theorem 7.1 and Corollary 7.2
    Completion.lean, CompletionCost.lean                Proposition 7.3
    LowerBound/                 Appendices C and D, Theorems C.1, D.1, D.2
Audit.lean                    axiom audit of the main declarations
scripts/check_axioms.py       checks the audit output
docs/unverified.tex           what the formalization does not cover
```
