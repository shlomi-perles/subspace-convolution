// Incidence between dimensions a < n/2 < b against every baseline we know.
//
// For each instance the fast transform is timed (median of runs after a
// warm-up) and checked against direct summation at random outputs.  The
// baselines are counted exactly, together with the memory they need:
//   direct   sum over the a-subspaces of each b-subspace: |Gr(n,b)| [b a]_q terms
//   layers   covering sweep through the dimensions a..b, one addition per
//            covering pair between consecutive layers (it must pass the middle
//            of the lattice); memory: all tables of dimensions a..b
//   tuples   Poisson summation over t-tuples of vectors, t = min(a, n-b) (for
//            n-b < a apply it to the transpose): a Fourier transform on
//            F_q^{tn}, counted as t n e passes over q^{tn} values (a lower
//            bound; the remaining dual incidence problem is not counted)
// Direct summation is also timed per incidence on the sampled outputs, by
// enumerating the a-subspaces of W and ranking them.  With --sweep-gb X the
// covering-pair algorithm itself is run when its index fits in X GB: the
// lattice plan of the truncated table T(n,b), keeping only pairs whose upper
// element has dimension > a (the others move zeros), applied in place on one
// core in real arithmetic for every q (it only adds); the timed run includes
// zeroing T(n,b) and placing the input.
//
// usage: bench_incidence_hard --out results/incidence_hard.csv [--samples 200] [--sweep-gb 0]
#include <cmath>
#include <random>

#include "common.hpp"
#include "fsc/incidence.hpp"
#include "fsc/naive.hpp"
#include "fsc/zeta.hpp"

using namespace fsc;
using namespace bench;

static const std::vector<std::string> kCols = {
    "q",           "n",          "a",           "b",            "S",           "fast_s",       "fast_flops",
    "plan_s",      "fast_gb",    "max_rel_err", "samples",      "direct_pairs", "direct_ns_per_pair",
    "layer_pairs", "layer_values", "tuple_ops", "tuple_values", "middle_crossed", "sweep_pairs", "sweep_s",
    "sweep_gb",    "sweep_plan_s", "sweep_rel_err", "fast_reps"};

template <class A>
void run_case(Csv& csv, int q, int n, int a, int b, int samples, double budget, double sweep_gb_max) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  const uint64_t Nin = S.G(n, a), Nout = S.G(n, b);
  std::mt19937_64 rng(7 + n * 31 + a * 7 + b + 1000 * q);
  std::uniform_real_distribution<double> U(-1, 1);
  hvec<double> f(Nin);
  for (auto& x : f) x = U(rng);

  auto t0 = clk::now();
  IncPlanner P(S);
  IncNode* nd = P.get(n, a, b);
  const double plan_s = seconds_since(t0);
  using T = typename A::T;
  const uint64_t need = arena_need(nd, 1);
  const double gb = (double)(Nin + Nout + need) * sizeof(T) / 1e9 + P.plan_bytes() / 1e9;
  hvec<T> X(Nin), Z(Nout);
  for (uint64_t i = 0; i < Nin; ++i) X[i] = A::from_double(f[i]);
  Arena<T> arena(need + 1);
  IncExec<A> ex{ar, q, F.e};
  auto body = [&] { ex.run(nd, X.data(), Z.data(), 1, arena); };
  auto c0 = clk::now();
  body();
  const double single = seconds_since(c0);
  Timing tm = time_runs(reps_for(single, budget, 3, 15), [] {}, body, false);

  // direct sums at random outputs: correctness and the per-incidence cost
  std::mt19937_64 pick(99 + q * 100 + n * 10 + a);
  std::vector<uint64_t> ws(samples);
  for (auto& w : ws) w = pick() % Nout;
  const uint64_t per = S.G(b, a);
  std::vector<double> want(ws.size());
  auto c1 = clk::now();
  for (size_t s = 0; s < ws.size(); ++s) {
    const Sub W = S.unrank_gr(n, b, ws[s]);
    double acc = 0;
    for (uint64_t c = 0; c < per; ++c) acc += f[S.rank_gr(n, combine(S, S.unrank_gr(b, a, c), W, n))];
    want[s] = acc;
  }
  const double direct_ns = seconds_since(c1) / ((double)ws.size() * (double)per) * 1e9;
  double err = 0, sc = 0;
  for (size_t s = 0; s < ws.size(); ++s) {
    err = std::max(err, std::abs(A::to_double(Z[ws[s]]) - want[s]));
    sc = std::max(sc, std::abs(want[s]));
  }

  // baselines, counted exactly.  The middle layers can exceed 2^64 subspaces
  // ([16 8]_2 = 6.3e19), where the uint64 table S.G wraps, so count in long double.
  auto gauss = [q](int m, int k) {  // [m k]_q; every partial product is [m i]_q
    long double g = 1;
    for (int i = 0; i < k; ++i) g = g * (std::pow((long double)q, m - i) - 1) / (std::pow((long double)q, i + 1) - 1);
    return g;
  };
  double layer_pairs = 0, layer_values = 0;
  for (int j = a; j <= b; ++j) {
    layer_values += (double)gauss(n, j);
    if (j > a) layer_pairs += (double)(gauss(n, j) * gauss(j, 1));
  }
  const int t = std::min(a, n - b);
  const double tuple_values = std::pow((double)q, (double)(t * n));
  const double tuple_ops = tuple_values * t * n * F.e;
  const bool crossed = 2 * a < n && n < 2 * b;

  // the covering-pair algorithm itself, when its index fits; it adds real numbers for every q
  double sweep_s = NAN, sweep_gb = NAN, sweep_plan_s = NAN, sweep_err = NAN, sweep_pairs = NAN;
  const uint64_t Mb = S.M(n, b);
  const double est_gb = (layer_pairs * 4.0 + (double)Mb * (b + 1) * 12.0 + (double)Mb * sizeof(double)) / 1e9;
  if (est_gb <= sweep_gb_max && Mb < (uint64_t(1) << 32)) {
    auto s0 = clk::now();
    auto Lp = build_lattice_plan(S, n, b, a);
    std::vector<uint64_t> pin(Nin), pout(Nout);
#pragma omp parallel for schedule(dynamic, 4096)
    for (int64_t u = 0; u < (int64_t)Nin; ++u) pin[(size_t)u] = S.pos_L(n, b, S.unrank_gr(n, a, (uint64_t)u));
#pragma omp parallel for schedule(dynamic, 4096)
    for (int64_t w = 0; w < (int64_t)Nout; ++w) pout[(size_t)w] = S.pos_L(n, b, S.unrank_gr(n, b, (uint64_t)w));
    sweep_plan_s = seconds_since(s0);
    sweep_pairs = (double)Lp->pairs();
    sweep_gb = (double)(Lp->bytes() + Mb * sizeof(double)) / 1e9;
    hvec<double> xs(Mb);
    std::memset((void*)xs.data(), 0, Mb * sizeof(double));  // fault the pages in before timing
    auto sbody = [&] {
      std::memset((void*)xs.data(), 0, Mb * sizeof(double));
      for (uint64_t u = 0; u < Nin; ++u) xs[pin[u]] = f[u];
      lattice_apply<RealArith>(*Lp, xs.data(), 1, false, false);
    };
    auto c2 = clk::now();
    sbody();
    sweep_s = seconds_since(c2);  // a single run when it exceeds the budget, else a warm-up
    const int more = reps_for(sweep_s, budget, 1, 5) - 1;
    if (more > 0) sweep_s = time_runs(more, [] {}, sbody, false).median;
    double d = 0, m = 0;
    for (uint64_t w = 0; w < Nout; ++w) {
      d = std::max(d, std::abs(xs[pout[w]] - A::to_double(Z[w])));
      m = std::max(m, std::abs(A::to_double(Z[w])));
    }
    sweep_err = d / m;
    std::printf("  covering-pair sweep: %.4g s, %.3g pairs, %.2f GB, plan %.3g s, rel diff to fast on all outputs %.2g\n",
                sweep_s, sweep_pairs, sweep_gb, sweep_plan_s, sweep_err);
  }

  csv.row({{"q", str(q)},
           {"n", str(n)},
           {"a", str(a)},
           {"b", str(b)},
           {"S", str(Nin + Nout)},
           {"fast_s", str(tm.median)},
           {"fast_flops", str(inc_flops(nd, ar, 1.0))},
           {"plan_s", str(plan_s)},
           {"fast_gb", str(gb)},
           {"max_rel_err", str(err / sc)},
           {"samples", str(samples)},
           {"direct_pairs", str((double)Nout * (double)per)},
           {"direct_ns_per_pair", str(direct_ns)},
           {"layer_pairs", str(layer_pairs)},
           {"layer_values", str(layer_values)},
           {"tuple_ops", str(tuple_ops)},
           {"tuple_values", str(tuple_values)},
           {"middle_crossed", crossed ? "1" : "0"},
           {"sweep_pairs", str(sweep_pairs)},
           {"sweep_s", str(sweep_s)},
           {"sweep_gb", str(sweep_gb)},
           {"sweep_plan_s", str(sweep_plan_s)},
           {"sweep_rel_err", str(sweep_err)},
           {"fast_reps", str(tm.reps)}});
  std::printf("q=%d (n,a,b)=(%d,%d,%d) S=%.3g: fast %.4g s (%.2f GB), rel err %.2g; direct %.3g pairs (%.1f ns/pair "
              "on the fly), layers %.3g pairs / %.3g values, tuples %.3g ops / %.3g values\n",
              q, n, a, b, (double)(Nin + Nout), tm.median, gb, err / sc, (double)Nout * (double)per, direct_ns,
              layer_pairs, layer_values, tuple_ops, tuple_values);
  std::fflush(stdout);
}

int main(int argc, char** argv) {
  const std::string out = arg(argc, argv, "out", "results/incidence_hard.csv");
  const int samples = std::stoi(arg(argc, argv, "samples", "200"));
  const double budget = std::stod(arg(argc, argv, "budget", "5"));
  const double sweep_gb_max = std::stod(arg(argc, argv, "sweep-gb", "0"));
  Csv csv(out, kCols);
  struct Case { int q, n, a, b; };
  // the extremal family I^{r,3r}_{4r} at r = 2, middle-crossing incidences with a = 3 and
  // a = 2, and points/hyperplanes for comparison with the Walsh-Hadamard approach
  // Larger instances for a machine with >= 256 GB: I^{2,5}_7 over F_8 (S = 2.5e9), where every
  // alternative needs more than 10^3 times our operations, and the next sizes of two families.
  const Case cases[] = {{2, 8, 2, 6},  {3, 8, 2, 6},   {4, 8, 2, 6},   {2, 9, 3, 6},  {2, 10, 3, 7},
                        {2, 11, 3, 8}, {2, 12, 2, 10}, {2, 13, 2, 11}, {2, 14, 2, 12}, {3, 9, 2, 7},
                        {2, 16, 1, 15}, {3, 15, 1, 14}, {4, 7, 2, 5},  {8, 6, 2, 4},  {8, 7, 2, 5},
                        {4, 9, 2, 7},   {2, 12, 3, 9}};
  const std::string only = arg(argc, argv, "only", "");
  for (const Case& c : cases) {
    const std::string key = str(c.q) + ":" + str(c.n) + ":" + str(c.a) + ":" + str(c.b);
    if (!only.empty() && ("," + only + ",").find("," + key + ",") == std::string::npos) continue;
    if (c.q % 2 == 0) run_case<RealArith>(csv, c.q, c.n, c.a, c.b, samples, budget, sweep_gb_max);
    else run_case<ComplexArith>(csv, c.q, c.n, c.a, c.b, samples, budget, sweep_gb_max);
  }
}
