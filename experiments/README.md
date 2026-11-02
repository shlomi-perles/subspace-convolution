# Implementation and experiments

Code, measurements and analysis behind the experiments of *A Fast Algorithm for Subspace
Convolution* by Shlomo A. Perles and Omri Weinstein. Each of the paper's three algorithms is
run against the alternatives that compute the same sums:

* **Zeta and Möbius transforms** on the $N$ subspaces of $\mathbb F_q^n$ (Theorem 1): our
  Fourier recursion, $O_q(N\log N)$ operations, and a hybrid that hands subproblems of
  dimension at most $t$ to the covering-pair algorithm; against the covering-pair algorithm
  of [BHK+16, KKW16], $\Theta_q(Nq^{n/2})$ additions, which Kennes [Ken92] proved optimal
  for algorithms that only add.
* **Incidence transform** $\mathsf I_n^{a,b}$ from the $a$- to the $b$-dimensional subspaces,
  $a<n/2<b$ (Theorem 2); against the covering-pair algorithm through the layers between $a$
  and $b$, Poisson summation over $t$-tuples of vectors, $t=\min(a,n-b)$, and direct summation.
* **Kernels on the Grassmann graph** $J_q(n,k)$, $K(U,W)=a_{d(U,W)}$ (Theorem 3); against the
  three-term recurrence for the distance matrices, with the adjacency matrix factored through
  the $(k-1)$-dimensional subspaces as in Maslen, Orrison, and Rockmore [MOR04], or explicit.

Every number in the paper's experiments section and its appendix comes from
[`results/`](results), measured on one server rented on vast.ai on 1–2 November 2026: two
28-core Intel Xeon Platinum 8273CL processors (2.2 GHz) and 2 TB of memory available to the
container. Every timed run uses one core.

All paths and commands below are relative to this directory, `experiments/`.

**Contents:** [Layout](#layout) ·
[Build and test](#build-and-test) · [Reproducing the paper](#reproducing-the-paper) ·
[Results](#results) · [Methodology](#methodology) · [Provenance](#provenance)

## Layout

```
include/fsc/         header-only C++17 engine
  gf.hpp               GF(q) for q = p^e <= 16 (32 with -DFSC_COORD_BITS=5)
  grassmann.hpp        echelon bases, ranking in the recursive table order
  arith.hpp            real, complex and exact mod-P arithmetic, batched radix-p DFTs
  zeta.hpp             Theorem 1: the recursion, the covering-pair algorithm, the hybrid
  incidence.hpp        Theorem 2: incidence between two dimensions
  grassmann_apps.hpp   Theorem 3: kernels on the Grassmann graph, recurrence baselines
  naive.hpp            direct summation
  hugevec.hpp          huge-page-backed buffers
tests/               exact (mod P) and floating-point checks against direct summation
bench/               the drivers behind the paper, CSV output
  bench_paired         full transform in paired rounds (--sample f for the covering pairs)
  bench_incidence_hard incidence: ours, counted alternatives, covering pairs where they fit
  bench_poisson        incidence: Poisson summation over t-tuples, run
  bench_grassmann      kernels on the Grassmann graph (--part kernel)
  verify_large         direct summation at random positions of the largest outputs; with
                       --zeta and --kernel, also the covering-pair variants against ours
                       on all entries
scripts/             the measurement campaigns (run_*.sh; launch_phase5.sh starts
                     run_phase5.sh as four jobs); each header says what it runs
results/             one folder per campaign: CSV files, logs and environment
analysis/            zeta_model.py, incidence_model.py: exact operation counts;
                     paper_assets.py: regenerates or checks everything below from results/
                     (figure_data.py, incidence_table.py, readme_tables.py, max_error.py)
figures/             zeta_fields.tex (pgfplots), its data and the built PDF
```

## Build and test

Requirements: Linux, a C++17 compiler with OpenMP (tested with GCC 11), CMake ≥ 3.20 and
Python ≥ 3.8 (standard library only). The campaigns also need `numactl`, and the figure
`pdflatex` with pgfplots.

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
```

```bash
cmake --build build -j
```

```bash
ctest --test-dir build --output-on-failure
```

Options: `-DFSC_COORD_BITS=5` packs coordinates in 5 bits, for $q=32$ (at most $n=12$); the
default 4 covers $q\le16$, $n\le16$. `-DFSC_NATIVE=OFF` drops `-march=native`.
[CI](../.github/workflows/experiments.yml) builds and tests both widths without
`-march=native` and runs the check below on every push.

## Reproducing the paper

**From the committed measurements** (seconds, any machine with Python): regenerate the
figure data and the rows of the incidence table from `results/`, and print the README
tables and the largest error:

```bash
python analysis/paper_assets.py
```

With `--check` it changes nothing and fails if anything committed differs from what
`results/` gives, or if an error reaches $10^{-13}$. Then rebuild the figure:

```bash
cd figures && pdflatex zeta_fields.tex
```

**Measuring again** needs a Linux server with at least 600 GB of memory (the largest
campaign peaks at 569 GB); we ran two campaigns at a time, one per socket, on 2 TB. Each
script's header gives its command line; each writes `results_<campaign>/` in this
directory, with `progress.log` as it goes. On our machine:

| script | measures | peak memory | wall time | here |
|---|---|---|---|---|
| `run_bigmem.sh` | full transform for $q\le16$, incidence, Grassmann kernels | 135 GB | 5.4 h | `results/bigmem` |
| `run_phase2.sh` | incidence: large instances; Poisson summation wherever its table fits | 569 GB | 3.9 h | `results/phase2` |
| `run_phase2b.sh`, one copy per socket | $\mathbb F_9^6$ and $\mathbb F_5^7$ with all covering pairs; Grassmann kernels with larger $[k]_q$; Poisson summation on $\mathbb F_8^6$ | 522 GB | 7.1 h | `results/phase2b`, `results/phase2b_n1` |
| `run_phase3.sh` | $q=32$ (5-bit build), covering pairs of $\mathbb F_{32}^5$ on a sample; check of the sampled estimate | 179 GB | 4.1 h | `results/phase3` |
| `run_phase4.sh` | $q=7,11,13$ with the paired length-$p$ DFT kernel | 38 GB | 0.5 h | `results/phase4` |
| `run_phase5.sh`, four jobs (`launch_phase5.sh`) | correctness of every timed table and of the Grassmann kernels | 486 GB | 1.4 h | `results/phase5_a` to `results/phase5_d` |

In all, the measurements took about 14 hours of the rented server.

## Results

### Incidence transform (Theorem 2)

Operations of each alternative divided by ours, smallest in bold; then the time of every
alternative that fits in 2 TB divided by ours (–: it does not fit). Direct: one addition per
incident pair. Covering: one addition per covering pair between dimensions $a$ and $b$.
Poisson: its Fourier transform on $\mathbb F_q^{tn}$ only, $tne\,q^{tn}$ operations for
$q=p^e$. $S$: entries of input and output. †: the family $(4r,r,3r)$ of the paper's lower
bound.

| $t$ | $q$ | $(n,a,b)$ | $S$ | ours | direct | covering | Poisson | covering, time | Poisson, time |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 2 | (16,1,15) | 1.3·10^5 | 1.9 ms | 1600 | 3.0·10^16 | **0.76** | – | 0.68 |
| 2 | 2 | (14,2,12) | 8.9·10^7 | 2.1 s | 7.1·10^4 | 3.5·10^8 | **4.3** | – | 4.5 |
| 2 | 3 | (8,2,6)† | 1.8·10^6 | 32 ms | 120 | 82 | **8.4** | 550 | 42 |
| 2 | 4 | (8,2,6)† | 4.8·10^7 | 1.0 s | 2700 | 1400 | **170** | – | 130 |
| 2 | 4 | (9,2,7) | 7.6·10^8 | 20 s | 3.9·10^4 | 5.6·10^4 | **170** | – | 190 |
| 2 | 8 | (6,2,4) | 3.9·10^7 | 810 ms | 140 | **34** | 3700 | 140 | 5300 |
| 2 | 8 | (7,2,5) | 2.5·10^9 | 80 s | 7500 | **1100** | 3600 | – | – |
| 3 | 2 | (10,3,7) | 1.3·10^7 | 260 ms | 300 | **33** | 130 | 84 | 140 |
| 3 | 2 | (11,3,8) | 1.0·10^8 | 2.9 s | 2200 | 210 | **130** | – | 130 |
| 3 | 2 | (12,3,9)† | 8.2·10^8 | 28 s | 1.6·10^4 | 1900 | **130** | – | 160 |

* On the 2- and 5-dimensional subspaces of $\mathbb F_8^7$, $S=2.5\cdot10^9$, ours takes
  80 s and 70 GB. The covering-pair algorithm needs 1100 times as many operations and 1.3 TB
  for these layers alone, Poisson summation 3600 times as many and 35 TB, direct summation
  7500 times as many.
* Where the covering-pair algorithm or Poisson summation fits, the faster of the two took
  4.5 to 190 times our time for $t\ge2$. The covering-pair algorithm took 84 to 550 times
  our time, more than its operation count suggests (see the limits below); Poisson
  summation took 4.5 to 5300 times, the most on $\mathbb F_8^6$, where its table has
  $q^{tn}=1800\,S$ entries.

### Full transform (Theorem 1)

Largest table per field, zeta direction; the Möbius direction, in the same files, gives
ratios 2 to 7% lower. Times are medians. Time ratio: the covering-pair algorithm divided by
ours, median of the per-round ratios over rounds in which the methods alternate. Operation
ratio: covering pairs divided by the real operations of the recursion
([`analysis/zeta_model.py`](analysis/zeta_model.py)). \*: the covering pairs of
$\mathbb F_{32}^5$ exceed memory, so the covering-pair algorithm was timed on 1.9% of them
and scaled up; on $\mathbb F_{16}^5$ and $\mathbb F_8^6$, where all pairs fit, this estimate is
11% and 16% below the full run. Our recursion runs on all of $\mathbb F_{32}^5$.

| field | subspaces $N$ | covering pairs | recursion | hybrid | covering-pair algorithm | time ratio, recursion | time ratio, hybrid | operation ratio |
|---|---|---|---|---|---|---|---|---|
| $\mathbb F_{2}^{10}$ | 2.3·10^8 | 34 GB | 11 s | 7.1 s | 22 s | 1.96× | 3.03× | 0.97 |
| $\mathbb F_{3}^{8}$ | 1.3·10^8 | 27 GB | 5.9 s | 4.7 s | 17 s | 2.96× | 3.72× | 0.65 |
| $\mathbb F_{4}^{7}$ | 5.1·10^7 | 12 GB | 2.1 s | 1.5 s | 7.5 s | 3.61× | 5.08× | 1.66 |
| $\mathbb F_{5}^{7}$ | 6.7·10^8 | 280 GB | 31 s | 28 s | 353 s | 11.4× | 12.8× | 0.92 |
| $\mathbb F_{7}^{6}$ | 6.2·10^7 | 22 GB | 3.6 s | 2.9 s | 20 s | 5.64× | 6.96× | 0.67 |
| $\mathbb F_{8}^{6}$ | 2.0·10^8 | 93 GB | 8.5 s | 6.5 s | 109 s | 12.9× | 16.8× | 2.95 |
| $\mathbb F_{9}^{6}$ | 5.4·10^8 | 326 GB | 28 s | 26 s | 512 s | 18.0× | 20.0× | 1.49 |
| $\mathbb F_{11}^{5}$ | 4.0·10^6 | 1.2 GB | 180 ms | 150 ms | 640 ms | 3.51× | 4.31× | 0.50 |
| $\mathbb F_{13}^{5}$ | 1.1·10^7 | 4.4 GB | 560 ms | 460 ms | 4.0 s | 7.09× | 8.62× | 0.58 |
| $\mathbb F_{16}^{5}$ | 3.6·10^7 | 22 GB | 1.5 s | 1.2 s | 25 s | 16.9× | 21.4× | 4.14 |
| $\mathbb F_{32}^{5}$ | 2.2·10^9 | 5.0 TB* | 145 s | 132 s | 3.8 h* | 95.3× | 105× | 12.5 |

Since $N=\Theta_q(q^{n^2/4})$, the factor $q^{n/2}$ between the two costs equals
$2^{\Theta(\sqrt{\log q\,\log N})}$: at a fixed table size it grows with $q$, and so does the
measured ratio ([`figures/zeta_fields.pdf`](figures/zeta_fields.pdf)).

### Grassmann graph (Theorem 3)

Kernel $a_i=2^{-i}$, one product $Kf$; time of each alternative divided by ours. Factored
recurrence: $d_{\max}$ products with the adjacency matrix, each through the
$(k-1)$-dimensional subspaces, $2[k]_q|V|$ additions. Explicit adjacency: $q[k]_q[n-k]_q$
nonzero entries per row, not run where they exceed the memory limit set for the run (in
parentheses: their size). Last column, an ablation: the reduction of Theorem 3 with the
covering-pair algorithm in place of our recursion. †: in complex arithmetic, which the
covering-pair algorithm does not need, so not a fair comparison.

| graph | vertices | ours | factored recurrence | explicit adjacency | our reduction with covering pairs |
|---|---|---|---|---|---|
| $J_{2}(8,4)$ | 2.0·10^5 | 7.4 ms | 3.00× | 73.1× | 1.05× |
| $J_{2}(10,5)$ | 1.1·10^8 | 17 s | 6.20× | not run (840 GB) | 1.23× |
| $J_{3}(6,3)$ | 3.4·10^4 | 1.2 ms | 1.96× | 52.4× | 0.79×† |
| $J_{3}(8,4)$ | 7.6·10^7 | 10 s | 7.98× | not run (1.5 TB) | 2.36×† |
| $J_{4}(6,3)$ | 3.8·10^5 | 13 ms | 3.93× | 239× | 1.25× |
| $J_{5}(6,3)$ | 2.6·10^6 | 170 ms | 4.83× | 561× | 2.16×† |
| $J_{8}(6,3)$ | 1.6·10^8 | 17 s | 22.1× | not run (26.6 TB) | 6.57× |

### Limits

* **Points and hyperplanes.** For $t=1$, Poisson summation is a single Fourier transform on
  $\mathbb F_q^n$ and is faster than ours: 0.68 times our time on $\mathbb F_2^{16}$.
* **Time ratios exceed operation ratios**, by factors 2 to 12 on the largest tables,
  because the covering-pair algorithm reads its operands at scattered positions: 11 ns per
  covering pair on $\mathbb F_{32}^5$ and 4.6 ns on $\mathbb F_{16}^5$, while the recursion
  streams through memory at 1.1 to 1.4 ns per operation. Our covering-pair algorithm is an
  in-place sweep in the order of an EL-labelling, with exactly one addition per covering
  pair; a layout with better locality would narrow the time ratios, not the operation ratios.
* **Small and prime fields.** On our largest tables over $\mathbb F_2$, $\mathbb F_3$,
  $\mathbb F_5$, $\mathbb F_7$, $\mathbb F_{11}$ and $\mathbb F_{13}$, the recursion makes about as
  many or more operations than the covering-pair algorithm (operation ratio 0.50 to 0.97;
  for odd $q$ it computes in complex numbers), and its time advantage comes from memory
  access alone.
* **Sampled baseline.** The ratio on $\mathbb F_{32}^5$ uses the scaled estimate described
  above, which favors the covering-pair algorithm.
* **Grassmann graph.** Over $\mathbb F_2$, most of the gain over the factored recurrence comes
  from the reduction of Theorem 3, not from the recursion: with the covering-pair algorithm
  in its place, the reduction takes 1.23 times our time on $J_2(10,5)$. Over $\mathbb F_8$ the
  recursion matters more: the same ablation takes 6.6 times our time on $J_8(6,3)$.
* **Index structures are not timed.** Fourier plans, covering pairs, incidence lists and
  adjacency matrices are built beforehand on 28 cores, for every method; their sizes and
  build times are in the CSV files.
* **Conditioning.** In the maximum norm $\mathsf Z^{-1}$ has norm $\prod_{i<n}(1+q^i)$, so a
  floating-point round trip $\mathsf Z^{-1}\mathsf Z f$ loses accuracy at large $n$ with any
  algorithm. The engine also computes exactly modulo $P=15\cdot2^{27}+1$.

## Methodology

* **Same engine, same data.** All methods share the field arithmetic, the subspace
  indexing and huge-page-backed buffers, and compute in doubles. For odd $q$ our algorithms
  and Poisson summation use complex numbers (with the real-input symmetry); the
  covering-pair algorithm and the recurrences add and scale reals.
* **What is timed.** One core per run, one job per socket (`numactl`); only the application
  of the index structures, built beforehand on 28 cores.
* **Paired rounds** (`bench_paired`). Cloud machines drift by tens of percent over minutes.
  In each round the recursion, the hybrid and the covering-pair algorithm each run three
  times back to back, in rotating order, and the best of the three counts; we report the
  median and quartiles of the per-round ratios. The hybrid threshold $t$ is the best of
  $1,\dots,n-1$ on three rounds.
* **Covering pairs beyond memory.** `bench_paired --sample f` stores the covering pairs of
  the upper elements in 64 evenly spaced ranges, a fraction $f$ of the table, times the
  sweep on them with the full-size table, and scales by all pairs over stored pairs.
* **Correctness.** `ctest` compares every method with direct summation on small instances,
  exactly modulo $P$ for $q\notin\{7,11,13\}$ and in floating point for those.
  `bench_incidence_hard` and `bench_poisson` compare with direct summation at random
  positions, and the methods they run with each other on all entries; `bench_grassmann`
  compares its methods with each other on all entries. `bench_paired` only times, so
  `verify_large` (`results/phase5_*`) checks every table it timed, with the same engine
  and the same hybrid thresholds: zeta and Möbius sums by direct summation at random
  positions, and the hybrid and the covering-pair algorithm against the recursion on all
  entries, in both directions (the covering-pair algorithm where its index fits in 400 GB,
  all but $\mathbb F_{32}^5$). For the Grassmann kernels it adds direct summation at random
  centers and the covering-pair variant on all entries. The largest relative error in any
  result file is $7.3\cdot10^{-14}$, on the incidence instance $(14,2,12)$ over $\mathbb F_2$
  (ours and Poisson summation, each against direct summation); in `results/phase5_*` it is
  $7.4\cdot10^{-15}$.

## Provenance

Each folder of `results/` holds the raw output of one campaign, as downloaded from the
server (the scripts name it `results_<campaign>`), with the machine (`environment.txt`).

The campaigns ran development versions of this code. The scripts also record the commit
they ran (`commit.txt`); those commits predate this repository, so the files are omitted.
Relative to the code here, the version behind a campaign lacks the features added after it
ran, and its build also contained the drivers of an exploratory first campaign that the
paper does not use (their names appear in some logs). The features, in the order they were
added:

1. Poisson summation (`bench_poisson`) and the covering-pair algorithm in
   `bench_incidence_hard`;
2. the 5-bit coordinate build (`-DFSC_COORD_BITS=5`, for $q=32$);
3. the paired length-$p$ DFT kernel for odd $p\ge7$ (`arith.hpp`);
4. the checks of `verify_large` against the covering-pair variants (`--zeta`, `--kernel`);
5. the counted alternatives of `bench_incidence_hard` in `long double` (see the known error
   below).

| results | script | features in the version that ran |
|---|---|---|
| `results/bigmem` | `run_bigmem.sh` | none |
| `results/phase2` | `run_phase2.sh` | 1 |
| `results/phase2b`, `results/phase2b_n1` (sockets 0 and 1) | `run_phase2b.sh` | 1 |
| `results/phase3` | `run_phase3.sh` | 1, 2 |
| `results/phase4` | `run_phase4.sh` | 1 to 3 |
| `results/phase5_a` to `results/phase5_d` (four jobs, two per socket) | `run_phase5.sh`, started by `launch_phase5.sh` | 1 to 4 |

For the full transform, the paper uses `results/phase4` for $q=7,11,13$ (paired length-$p$
DFT kernel), `results/phase2b` for $\mathbb F_9^6$ and $\mathbb F_5^7$, `results/phase3` for
$q=32$ and for the check of the sampled estimate, and `results/bigmem` for the rest. For the
incidence transform it uses `results/phase2`, with the Poisson run on $\mathbb F_8^6$ in
`results/phase2b_n1`; for the Grassmann graph, `results/bigmem` and `results/phase2b_n1`.
`results/phase5_*` check the outputs; they come from a second rental of the same machine on
2 November, because the first run of `run_phase5.sh` was lost when its instance was
destroyed. [`analysis/paper_assets.py`](analysis/paper_assets.py) encodes these choices.

**Known error in the raw files.** The counted alternatives in `incidence_hard.csv` were
computed with 64-bit unsigned Gaussian binomials, which wrap for the middle layers of
$\mathbb F_2^{16}$ and $\mathbb F_3^{15}$ ($[16\ 8]_2\approx6.3\cdot10^{19}>2^{64}$). There,
the columns `layer_pairs` and `layer_values` are too small: on $(16,1,15)$ over $\mathbb F_2$,
$1.5\cdot10^{22}$ covering pairs instead of $4.1\cdot10^{22}$. No timing depends on them.
[`analysis/incidence_table.py`](analysis/incidence_table.py) recomputes every counted
alternative in exact integers, and `bench_incidence_hard` now counts in `long double`; the
raw files are kept as measured.
