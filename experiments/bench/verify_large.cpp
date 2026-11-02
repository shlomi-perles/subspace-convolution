// Verification of the largest benchmark instances, where neither the covering
// sweep nor direct summation fits in memory.  Outputs of the fast algorithms are
// recomputed by direct summation (in long double) at random positions, and two
// independent executions are compared on the full output:
//   zeta       Z f and Z^{-1} f at random W, Z f at W = F_q^n; hybrid vs. FFT;
//              with --zeta, also the covering-pair algorithm vs. FFT, Z f and Z^{-1} f
//              on all entries, where its index fits in --sweep-gb
//              (a round trip Z^{-1} Z f is no test at this size: in the maximum norm
//              Z^{-1} has norm prod_{i<n} (1 + q^i), about 1.7e14 for q = 2, n = 10)
//   incidence  I^{a,b} f at random b-dimensional W
//   kernel     K f at random centers U; Algorithm 3 with covering-sweep transforms
//              (--kernel q:n:k,...: these instances, about 2e9 terms of direct sums each)
// The inputs are exactly those of bench_grassmann and of bench_zeta and bench_incidence,
// two drivers of an exploratory first campaign that the paper does not use.
#include <cmath>
#include <random>

#include "common.hpp"
#include "fsc/grassmann_apps.hpp"
#include "fsc/incidence.hpp"
#include "fsc/naive.hpp"
#include "fsc/zeta.hpp"

using namespace fsc;
using namespace bench;

static const std::vector<std::string> kCols = {"experiment", "q",           "n",       "a",    "b", "size",
                                               "check",      "samples",     "max_rel_err", "note", "seconds"};

// max |got - want| / max |want| over the checked positions
struct ErrAcc {
  long double err = 0, sc = 0;
  void add(long double got, long double want) {
    err = std::max(err, std::fabs(got - want));
    sc = std::max(sc, std::fabs(want));
  }
  double rel() const { return sc > 0 ? double(err / sc) : double(err); }
};

struct Row {
  Csv& csv;
  std::string experiment;
  int q, n, a, b;
  uint64_t size;
  void operator()(const std::string& check, uint64_t cnt, double err, double secs, const std::string& note = "") {
    csv.row({{"experiment", experiment}, {"q", str(q)}, {"n", str(n)}, {"a", str(a)}, {"b", str(b)},
             {"size", str(size)}, {"check", check}, {"samples", str(cnt)}, {"max_rel_err", str(err)},
             {"note", note}, {"seconds", str(secs)}});
    std::printf("%s q=%d n=%d (a,b)=(%d,%d) %s: %llu outputs, max rel err %.3g (%.1f s) %s\n", experiment.c_str(), q,
                n, a, b, check.c_str(), (unsigned long long)cnt, err, secs, note.c_str());
    std::fflush(stdout);
  }
};

template <class A>
void verify_zeta(Csv& csv, int q, int n, int samples, int hybrid_t, double sweep_gb = 0) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  const int k = n;
  const uint64_t N = S.M(n, k);
  Row row{csv, "zeta", q, n, 0, n, N};
  std::mt19937_64 rng(42 + 1000 * q + n);
  std::uniform_real_distribution<double> U(-1, 1);
  hvec<double> f(N);
  for (auto& x : f) x = U(rng);

  ZetaPlanner P(S);
  ZetaNode* root = P.get(n, k);
  using T = typename A::T;
  hvec<T> X(N), Y(N);
  ZetaExec<A> ex{ar, q, F.e};
  for (uint64_t i = 0; i < N; ++i) X[i] = A::from_double(f[i]);
  ex.run(root, X.data(), Y.data(), 1, Mode::Forward, true);
  hvec<double> zf(N);
  for (uint64_t i = 0; i < N; ++i) zf[i] = A::to_double(X[i]);

  // Direct zeta and Mobius sums over U <= W, with mu(U,W) = (-1)^j q^(j(j-1)/2) for
  // j = dim W - dim U: uniformly random W, five random W of every dimension with at
  // most 2e6 subspaces, and W = F_q^n for the zeta transform (the total sum).
  {
    auto t0 = clk::now();
    std::mt19937_64 pick(2024 + 100 * q + n);
    std::vector<uint64_t> ws;
    for (int s = 0; s < samples; ++s) ws.push_back(pick() % N);
    std::string dims;
    for (int d = 0; d < n; ++d) {
      if (S.M(d, d) > 2000000) continue;
      for (int s = 0; s < 5; ++s) ws.push_back(S.pos_L(n, k, S.unrank_gr(n, d, pick() % S.G(n, d))));
      dims += (dims.empty() ? "" : " ") + str(d);
    }
    std::vector<long double> mu(n + 1);
    for (int j = 0; j <= n; ++j) mu[j] = (j % 2 ? -1.0L : 1.0L) * std::pow((long double)q, j * (j - 1) / 2);
    std::vector<long double> want_z(ws.size()), want_m(ws.size());
#pragma omp parallel for schedule(dynamic, 1)
    for (int64_t s = 0; s < (int64_t)ws.size(); ++s) {
      Sub W = S.unrank_L(n, k, ws[(size_t)s]);
      long double z = 0, m = 0;
      for (int j = 0; j <= W.d; ++j)
        for (uint64_t c = 0; c < S.G(W.d, j); ++c) {
          const double x = f[S.pos_L(n, k, combine(S, S.unrank_gr(W.d, j, c), W, n))];
          z += x;
          m += mu[W.d - j] * x;
        }
      want_z[(size_t)s] = z;
      want_m[(size_t)s] = m;
    }
    ErrAcc acc;
    for (size_t s = 0; s < ws.size(); ++s) acc.add(zf[ws[s]], want_z[s]);
    row("direct_sums_sampled", ws.size(), acc.rel(), seconds_since(t0), "uniform W and dims " + dims);

    auto t1 = clk::now();
    for (uint64_t i = 0; i < N; ++i) X[i] = A::from_double(f[i]);
    ex.run(root, X.data(), Y.data(), 1, Mode::Inverse, true);
    ErrAcc accm;
    for (size_t s = 0; s < ws.size(); ++s) accm.add(A::to_double(X[ws[s]]), want_m[s]);
    row("direct_mobius_sums_sampled", ws.size(), accm.rel(), seconds_since(t1), "uniform W and dims " + dims);

    Sub Full;
    Full.d = n;
    for (int i = 0; i < n; ++i) Full.r[i] = unit(i);
    long double total = 0;
    for (uint64_t i = 0; i < N; ++i) total += f[i];
    ErrAcc full;
    full.add(zf[S.pos_L(n, k, Full)], total);
    row("direct_sum_full_space", 1, full.rel(), 0);
  }
  // The hybrid (covering sweep below dimension t) agrees with the pure FFT recursion.
  {
    auto t0 = clk::now();
    P.set_lattice_threshold(hybrid_t);
    for (uint64_t i = 0; i < N; ++i) X[i] = A::from_double(f[i]);
    ex.run(root, X.data(), Y.data(), 1, Mode::Forward, true);
    ErrAcc acc;
    for (uint64_t i = 0; i < N; ++i) acc.add(A::to_double(X[i]), zf[i]);
    row("hybrid_vs_fft", N, acc.rel(), seconds_since(t0), "t=" + str(hybrid_t));
  }
  // The covering-pair algorithm (as timed in bench_paired, in real arithmetic) agrees
  // with the pure FFT recursion on all entries, in both directions.
  if (sweep_gb > 0) {
    uint64_t pairs = 0;
    for (int j = 1; j <= n; ++j) pairs += S.G(n, j) * S.G(j, 1);
    const double gb = pairs * 4.0 / 1e9;
    if (gb > sweep_gb) {
      row("sweep_vs_fft", 0, std::nan(""), 0, "not run: covering pairs need " + str(gb) + " GB");
      return;
    }
    auto t0 = clk::now();
    auto L = build_lattice_plan(S, n, k);
    P.set_lattice_threshold(0);
    hvec<double> x(N);
    for (Mode mode : {Mode::Forward, Mode::Inverse}) {
      const bool inv = mode == Mode::Inverse;
      for (uint64_t i = 0; i < N; ++i) X[i] = A::from_double(f[i]);
      ex.run(root, X.data(), Y.data(), 1, mode, true);
      x = f;
      lattice_apply<RealArith>(*L, x.data(), 1, inv, false);
      ErrAcc acc;
      for (uint64_t i = 0; i < N; ++i) acc.add(A::to_double(X[i]), x[i]);
      row(inv ? "sweep_vs_fft_mobius" : "sweep_vs_fft", N, acc.rel(), seconds_since(t0),
          "covering pairs " + str(gb) + " GB");
      t0 = clk::now();
    }
  }
}

template <class A>
void verify_incidence(Csv& csv, int q, int n, int a, int b, int samples) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  const uint64_t Nin = S.G(n, a), Nout = S.G(n, b);
  Row row{csv, "incidence", q, n, a, b, Nin + Nout};
  std::mt19937_64 rng(7 + n * 31 + a * 7 + b);
  std::uniform_real_distribution<double> U(-1, 1);
  hvec<double> f(Nin);
  for (auto& x : f) x = U(rng);

  IncPlanner P(S);
  IncNode* nd = P.get(n, a, b);
  using T = typename A::T;
  hvec<T> X(Nin), Z(Nout);
  for (uint64_t i = 0; i < Nin; ++i) X[i] = A::from_double(f[i]);
  {
    Arena<T> arena(arena_need(nd, 1) + 1);
    IncExec<A> ex{ar, q, F.e};
    ex.run(nd, X.data(), Z.data(), 1, arena);
  }
  auto t0 = clk::now();
  std::mt19937_64 pick(2024 + 100 * q + 10 * n + a);
  std::vector<uint64_t> ws(samples);
  for (auto& w : ws) w = pick() % Nout;
  std::vector<long double> want(ws.size());
#pragma omp parallel for schedule(dynamic, 1)
  for (int64_t s = 0; s < (int64_t)ws.size(); ++s) {
    Sub W = S.unrank_gr(n, b, ws[(size_t)s]);
    long double acc = 0;
    for (uint64_t c = 0; c < S.G(b, a); ++c) acc += f[S.rank_gr(n, combine(S, S.unrank_gr(b, a, c), W, n))];
    want[(size_t)s] = acc;
  }
  ErrAcc acc;
  for (size_t s = 0; s < ws.size(); ++s) acc.add(A::to_double(Z[ws[s]]), want[s]);
  row("direct_sums_sampled", ws.size(), acc.rel(), seconds_since(t0));
}

template <class A>
void verify_kernel(Csv& csv, int q, int n, int k, int samples, bool with_sweep) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  GrassmannOps<A> G(S, n, k, ar);
  const uint64_t v = G.v();
  Row row{csv, "kernel", q, n, k, k, v};
  const int s = std::min(k, n - k);
  std::vector<double> a(s + 1);
  for (int i = 0; i <= s; ++i) a[i] = std::pow(0.5, i);
  std::mt19937_64 rng(11);
  std::uniform_real_distribution<double> U(-1, 1);
  hvec<double> f(v), y(v);
  for (auto& x : f) x = U(rng);
  G.kernel_apply(a, f.data(), y.data());

  // K f at random centers, summing a[d(U,W)] f(W) over all of Gr(n,k).
  {
    auto t0 = clk::now();
    std::mt19937_64 pick(2024 + 100 * q + 10 * n + k);
    ErrAcc acc;
    for (int t = 0; t < samples; ++t) {
      const uint64_t u = pick() % v;
      const Sub C = S.unrank_gr(n, k, u);
      long double want = 0;
#pragma omp parallel reduction(+ : want)
      {
        std::vector<Vec> rows;
        rows.reserve(2 * k);
#pragma omp for schedule(static)
        for (int64_t w = 0; w < (int64_t)v; ++w) {
          const Sub W = S.unrank_gr(n, k, (uint64_t)w);
          rows.assign(C.r, C.r + k);
          rows.insert(rows.end(), W.r, W.r + k);
          want += a[S.echelon(rows, n).d - k] * f[(size_t)w];
        }
      }
      acc.add(y[u], want);
    }
    row("direct_sums_sampled", samples, acc.rel(), seconds_since(t0));
  }
  // Algorithm 3 with covering-sweep transforms gives the same product.
  if (with_sweep) {
    auto t0 = clk::now();
    G.planner().set_lattice_threshold(n);
    hvec<double> yl(v);
    G.kernel_apply(a, f.data(), yl.data());
    ErrAcc acc;
    for (uint64_t u = 0; u < v; ++u) acc.add(yl[u], y[u]);
    row("sweep_vs_fft", v, acc.rel(), seconds_since(t0));
  }
}

int main(int argc, char** argv) {
  const std::string only = arg(argc, argv, "only", "zeta,incidence,kernel");
  const int samples = std::stoi(arg(argc, argv, "samples", "400"));
  Csv csv(arg(argc, argv, "out", "results/verify_large.csv"), kCols);
  auto want = [&](const std::string& m) { return ("," + only + ",").find("," + m + ",") != std::string::npos; };

  // --zeta q:n:t,...: only these full transforms (hybrid threshold t), with the
  // covering-pair algorithm on all entries where its index fits in --sweep-gb
  const std::string zeta_cases = arg(argc, argv, "zeta", "");
  if (!zeta_cases.empty()) {
    const double sweep_gb = std::stod(arg(argc, argv, "sweep-gb", "0"));
    size_t pos = 0;
    while (pos < zeta_cases.size()) {
      size_t end = zeta_cases.find(',', pos);
      if (end == std::string::npos) end = zeta_cases.size();
      const std::string c = zeta_cases.substr(pos, end - pos);
      pos = end + 1;
      int q = 0, n = 0, t = 0;
      if (std::sscanf(c.c_str(), "%d:%d:%d", &q, &n, &t) != 3) {
        std::fprintf(stderr, "bad case '%s' (want q:n:t)\n", c.c_str());
        return 1;
      }
      if (q % 2 == 0) verify_zeta<RealArith>(csv, q, n, samples, t, sweep_gb);
      else verify_zeta<ComplexArith>(csv, q, n, samples, t, sweep_gb);
    }
    return 0;
  }
  // --kernel q:n:k,...: only these kernels, with the covering-sweep variant on all entries
  const std::string kernel_cases = arg(argc, argv, "kernel", "");
  if (!kernel_cases.empty()) {
    size_t pos = 0;
    while (pos < kernel_cases.size()) {
      size_t end = kernel_cases.find(',', pos);
      if (end == std::string::npos) end = kernel_cases.size();
      const std::string c = kernel_cases.substr(pos, end - pos);
      pos = end + 1;
      int q = 0, n = 0, k = 0;
      if (std::sscanf(c.c_str(), "%d:%d:%d", &q, &n, &k) != 3) {
        std::fprintf(stderr, "bad case '%s' (want q:n:k)\n", c.c_str());
        return 1;
      }
      GF F(q);
      Space S(F);
      const double v = (double)S.G(n, k);
      const int m = (int)std::max(4.0, std::min((double)samples / 4, 2e9 / v));
      if (q % 2 == 0) verify_kernel<RealArith>(csv, q, n, k, m, true);
      else verify_kernel<ComplexArith>(csv, q, n, k, m, true);
    }
    return 0;
  }

  if (arg(argc, argv, "smoke", "0") == "1") {  // small instances, to test the checks themselves
    verify_zeta<RealArith>(csv, 2, 6, samples, 3);
    verify_zeta<ComplexArith>(csv, 3, 5, samples, 3);
    verify_incidence<RealArith>(csv, 2, 8, 2, 6, samples / 4);
    verify_incidence<ComplexArith>(csv, 3, 6, 1, 5, samples / 4);
    verify_kernel<RealArith>(csv, 2, 6, 3, 20, true);
    verify_kernel<ComplexArith>(csv, 3, 5, 2, 20, true);
    return 0;
  }
  // zeta: the instances of bench_zeta beyond both memory limits, hybrid
  // thresholds as tuned there
  if (want("zeta")) {
    verify_zeta<RealArith>(csv, 2, 10, samples, 8);
    verify_zeta<ComplexArith>(csv, 3, 8, samples, 6);
    verify_zeta<RealArith>(csv, 4, 7, samples, 6);
  }
  // incidence: the instances of bench_incidence beyond the memory limit of
  // direct summation
  if (want("incidence")) {
    struct Case { int q, n, a, b; };
    const Case cases[] = {{2, 16, 1, 15}, {2, 10, 2, 8},  {2, 11, 2, 9},  {2, 12, 2, 10}, {2, 13, 2, 11},
                          {2, 14, 2, 12}, {2, 9, 3, 6},   {2, 10, 3, 7},  {3, 11, 1, 10}, {3, 12, 1, 11},
                          {3, 13, 1, 12}, {3, 14, 1, 13}, {3, 15, 1, 14}, {3, 8, 2, 6},   {3, 9, 2, 7}};
    for (const Case& c : cases) {
      const int m = samples / 4;
      if (c.q % 2 == 0) verify_incidence<RealArith>(csv, c.q, c.n, c.a, c.b, m);
      else verify_incidence<ComplexArith>(csv, c.q, c.n, c.a, c.b, m);
    }
  }
  // kernels: the instances of bench_grassmann without a full reference
  if (want("kernel")) {
    verify_kernel<RealArith>(csv, 2, 10, 5, 4, false);  // the covering pairs exceed memory
    verify_kernel<ComplexArith>(csv, 5, 6, 3, 50, true);
  }
}
