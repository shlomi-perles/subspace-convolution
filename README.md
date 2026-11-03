# A Fast Algorithm for Subspace Convolution

[![Experiments](https://github.com/shlomi-perles/subspace-convolution/actions/workflows/experiments.yml/badge.svg)](https://github.com/shlomi-perles/subspace-convolution/actions/workflows/experiments.yml)
[![Lean](https://github.com/shlomi-perles/subspace-convolution/actions/workflows/lean.yml/badge.svg)](https://github.com/shlomi-perles/subspace-convolution/actions/workflows/lean.yml)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache_2.0-blue.svg)](LICENSE)

Code accompanying the paper

> Shlomo A. Perles and Omri Weinstein. **[A Fast Algorithm for Subspace Convolution](paper/subspace-convolution.pdf).** 2026.

The paper sums a function over all subspaces of each subspace of $\mathbb F_q^n$, the analogue
of the subset-zeta transform, in $O_q(N\log N)$ operations for $N$ subspaces; the lattice-based
algorithms need $\Theta_q(Nq^{n/2})$ additions. It extends the recursion to the inverse, to
incidence between two dimensions and to span convolution, and applies it to kernels on the
Grassmann graph and to coloring graphs of low binary cut-rank.

The repository holds the paper and two independent parts of code:

| directory | contents | requires |
|---|---|---|
| [`paper/`](paper) | the paper, [`subspace-convolution.pdf`](paper/subspace-convolution.pdf) | a PDF viewer |
| [`experiments/`](experiments) | a header-only C++17 implementation of the transforms and of the algorithms they are compared against; the benchmark drivers and campaign scripts; every measurement behind the paper's experiments; the scripts that turn them into its tables and figure | Linux, a C++17 compiler with OpenMP, CMake ≥ 3.20, Python ≥ 3.8 |
| [`lean/`](lean) | a Lean 4 formalization, on Mathlib, of every numbered result of the paper, with an axiom audit | [elan](https://github.com/leanprover/elan) (the toolchain is pinned) |

## Quick start

Build and test the C++ engine, then check that the paper's tables and figure data follow from
the committed measurements:

```bash
cd experiments
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j
ctest --test-dir build --output-on-failure
python analysis/paper_assets.py --check
```

Check the proofs: download the compiled Mathlib, build, and audit the axioms:

```bash
cd lean
lake exe cache get
lake build
lake env lean Audit.lean > audit.log
python3 scripts/check_axioms.py audit.log Audit.lean
```

[`experiments/README.md`](experiments/README.md) gives the results, the methodology, how to
measure again (a server with at least 600 GB of memory) and where every result file comes from.
[`lean/README.md`](lean/README.md) maps each statement of the paper to its Lean declaration and
states the modelling decisions; [`lean/docs/unverified.tex`](lean/docs/unverified.tex) lists
what the formalization does not cover.

## Citation

If you use this code, these measurements or the formalization, please cite the paper (also in
[`CITATION.cff`](CITATION.cff); GitHub shows it under "Cite this repository"):

```bibtex
@unpublished{PerlesWeinstein2026,
  author = {Shlomo A. Perles and Omri Weinstein},
  title  = {A Fast Algorithm for Subspace Convolution},
  year   = {2026},
  note   = {Manuscript}
}
```

## License

[Apache License 2.0](LICENSE), the license of Mathlib.

## Acknowledgements

The Lean formalization was developed with the assistance of Claude Code (Anthropic).
