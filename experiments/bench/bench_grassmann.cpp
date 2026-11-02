// Experiment 4: linear algebra on the Grassmannian Gr(n,k) (Theorem 3).
//
// Part A ("kernel"): y = K f for an intersection kernel K(U,W) = a_{d(U,W)}.
//   fast      Algorithm 3: one upper + one lower truncated transform (FFT plan)
//   lattice   Algorithm 3 with covering-sweep transforms (KKW16-style)
//   graph     s sparse products with the Grassmann graph adjacency (3-term recurrence)
//   dense     pairwise intersection dimensions (small v only)
// Part B ("code"): distance profiles D_i 1_C of a lifted Gabidulin (MRD) code over
//   F_2, validated against the closed-form rank distribution; covering radius.
//
// usage: bench_grassmann --part kernel --q 2 --n 8 --k 4 --out results/grassmann.csv
//        bench_grassmann --part code --m 4 --delta 2 --out results/grassmann_code.csv
#include <cmath>
#include <random>

#include "common.hpp"
#include "fsc/grassmann_apps.hpp"

using namespace fsc;
using namespace bench;

static const std::vector<std::string> kCols = {
    "experiment", "q", "n", "k", "v", "M", "method", "reps", "t_median", "t_min", "t_max", "plan_s",
    "plan_mb", "flops", "max_rel_err", "note", "peak_rss_gb"};

template <class A>
void part_kernel(Csv& csv, int q, int n, int k, double graph_gb, double budget) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  auto t0 = clk::now();
  GrassmannOps<A> G(S, n, k, ar);
  double plan_s = seconds_since(t0);
  const uint64_t v = G.v(), M = G.table_size();
  const int s = std::min(k, n - k);
  std::vector<double> a(s + 1);
  for (int i = 0; i <= s; ++i) a[i] = std::pow(0.5, i);  // exponentially decaying covariance
  std::mt19937_64 rng(11);
  std::uniform_real_distribution<double> U(-1, 1);
  hvec<double> f(v), yf(v), yl(v), yg;
  for (auto& x : f) x = U(rng);
  auto base = [&](const std::string& method) {
    std::map<std::string, std::string> r;
    r["experiment"] = "kernel";
    r["q"] = str(q);
    r["n"] = str(n);
    r["k"] = str(k);
    r["v"] = str(v);
    r["M"] = str(M);
    r["method"] = method;
    return r;
  };
  auto record = [&](const std::string& method, const Timing& tm, double ps, double pmb, double flops) {
    auto r = base(method);
    r["reps"] = str(tm.reps);
    r["t_median"] = str(tm.median);
    r["t_min"] = str(tm.min);
    r["t_max"] = str(tm.max);
    r["plan_s"] = str(ps);
    r["plan_mb"] = str(pmb);
    r["flops"] = str(flops);
    r["peak_rss_gb"] = str(peak_rss_gb());
    csv.row(r);
  };
  // fast
  {
    auto body = [&] { G.kernel_apply(a, f.data(), yf.data()); };
    auto c = clk::now();
    body();
    Timing tm = time_runs(reps_for(seconds_since(c), budget), [] {}, body, false);
    record("fast", tm, plan_s, G.planner().plan_bytes() / 1e6, 0);
    std::printf("q=%d Gr(%d,%d) v=%llu fast kernel: %.4g s (plan %.3g s)\n", q, n, k, (unsigned long long)v,
                tm.median, plan_s);
  }
  // lattice-based Algorithm 3 (covering sweeps on T(n,k)), if its index fits
  double lat_pairs = 0;
  for (int j = 1; j <= k; ++j) lat_pairs += (double)S.G(n, j) * (double)S.G(j, 1);
  if (lat_pairs * 4.4 / 1e9 > graph_gb) {
    auto r = base("lattice");
    r["flops"] = str(2 * lat_pairs);
    r["note"] = "covering-pair index exceeds memory limit";
    csv.row(r);
  } else {
    auto c = clk::now();
    G.planner().set_lattice_threshold(n);
    double lplan = seconds_since(c);
    auto body = [&] { G.kernel_apply(a, f.data(), yl.data()); };
    auto c2 = clk::now();
    body();
    Timing tm = time_runs(reps_for(seconds_since(c2), budget), [] {}, body, false);
    double pairs = 0;
    for (int j = 1; j <= k; ++j) pairs += (double)S.G(n, j) * (double)S.G(j, 1);
    record("lattice", tm, lplan, G.planner().plan_bytes() / 1e6, 2 * pairs);
    std::printf("   lattice kernel: %.4g s (plan %.3g s)\n", tm.median, lplan);
    G.planner().set_lattice_threshold(0);
  }
  // graph recurrence
  double deg = (double)q * (double)S.G(k, 1) * (double)S.G(n - k, 1);
  if ((double)v * deg * 4 / 1e9 <= graph_gb) {
    auto c = clk::now();
    CSR Adj = build_grassmann_adjacency(S, n, k);
    double gplan = seconds_since(c);
    std::vector<hvec<double>> prof;
    yg.assign(v, 0.0);
    auto body = [&] {
      graph_distance_profiles(S, n, k, Adj, f.data(), prof);
      for (uint64_t u = 0; u < v; ++u) {
        double acc = 0;
        for (int i = 0; i <= s; ++i) acc += a[i] * prof[i][u];
        yg[u] = acc;
      }
    };
    auto c2 = clk::now();
    body();
    Timing tm = time_runs(reps_for(seconds_since(c2), budget), [] {}, body, false);
    record("graph", tm, gplan, (Adj.nnz() * 4 + Adj.ptr.size() * 8) / 1e6, (double)s * (double)Adj.nnz());
    double err = 0, sc = 0, errl = 0;
    for (uint64_t u = 0; u < v; ++u) {
      err = std::max(err, std::abs(yf[u] - yg[u]));
      errl = std::max(errl, std::abs(yl[u] - yg[u]));
      sc = std::max(sc, std::abs(yg[u]));
    }
    auto r = base("fast_accuracy");
    r["max_rel_err"] = str(err / sc);
    r["note"] = "vs graph recurrence; lattice rel err " + str(errl / sc);
    csv.row(r);
    std::printf("   graph kernel: %.4g s (adjacency %.3g s, nnz %llu), rel err fast %.2g lattice %.2g\n", tm.median,
                gplan, (unsigned long long)Adj.nnz(), err / sc, errl / sc);
  } else {
    auto r = base("graph");
    r["flops"] = str((double)s * (double)v * deg);
    r["note"] = "adjacency exceeds memory limit";
    csv.row(r);
  }
  // graph recurrence with the adjacency factored through the (k-1)-subspaces (as in [MOR04])
  const double fnnz = (double)v * (double)S.G(k, 1);
  if (fnnz * 4 / 1e9 <= graph_gb) {
    auto c = clk::now();
    CSR Inc = build_incidence_csr(S, n, k - 1, k);
    const double iplan = seconds_since(c);
    std::vector<hvec<double>> prof;
    hvec<double> yh(v);
    auto body = [&] {
      factored_distance_profiles(S, n, k, Inc, f.data(), prof);
      for (uint64_t u = 0; u < v; ++u) {
        double acc = 0;
        for (int i = 0; i <= s; ++i) acc += a[i] * prof[i][u];
        yh[u] = acc;
      }
    };
    auto c2 = clk::now();
    body();
    Timing tm = time_runs(reps_for(seconds_since(c2), budget), [] {}, body, false);
    record("factored", tm, iplan, (Inc.nnz() * 4 + Inc.ptr.size() * 8) / 1e6, 2.0 * s * fnnz);
    double err = 0, sc = 0;
    for (uint64_t u = 0; u < v; ++u) {
      err = std::max(err, std::abs(yf[u] - yh[u]));
      sc = std::max(sc, std::abs(yh[u]));
    }
    auto r = base("factored_accuracy");
    r["max_rel_err"] = str(err / sc);
    r["note"] = "fast vs factored recurrence";
    csv.row(r);
    std::printf("   factored recurrence: %.4g s (incidence lists %.3g s, %.3g GB), rel err fast %.2g\n", tm.median,
                iplan, Inc.nnz() * 4 / 1e9, err / sc);
  } else {
    auto r = base("factored");
    r["flops"] = str(2.0 * s * fnnz);
    r["note"] = "incidence lists exceed memory limit";
    csv.row(r);
  }
  // dense pairwise (small v)
  if ((double)v * (double)v <= 2.5e9) {
    std::vector<Sub> subs(v);
    for (uint64_t i = 0; i < v; ++i) subs[i] = S.unrank_gr(n, k, i);
    hvec<double> yd(v);
    auto body = [&] {
      for (uint64_t u = 0; u < v; ++u) {
        double acc = 0;
        for (uint64_t w = 0; w < v; ++w) acc += a[S.dim_of_sum(subs[u], subs[w], n) - k] * f[w];
        yd[u] = acc;
      }
    };
    auto c = clk::now();
    body();
    Timing t1;
    t1.reps = 1;
    t1.median = t1.min = t1.max = seconds_since(c);
    record("dense", t1, 0, 0, 2.0 * (double)v * (double)v);
    double err = 0, sc = 0;
    for (uint64_t u = 0; u < v; ++u) {
      err = std::max(err, std::abs(yf[u] - yd[u]));
      sc = std::max(sc, std::abs(yd[u]));
    }
    std::printf("   dense kernel: %.4g s, rel err fast %.2g\n", t1.median, err / sc);
  }
}

// ---------------------------------------------------------------------------
// Lifted Gabidulin codes over F_2: graphs {(x, f(x))} of linearized polynomials
// f(x) = sum_{i<kappa} a_i x^{2^i} over F_{2^m}; minimum rank distance m-kappa+1.
// ---------------------------------------------------------------------------
struct GF2m {
  int m;
  uint32_t poly;  // primitive polynomial including x^m
  explicit GF2m(int m_) : m(m_) {
    static const uint32_t P[] = {0, 0, 0x7, 0xB, 0x13, 0x25, 0x43, 0x89, 0x11D};
    poly = P[m];
  }
  uint32_t mul(uint32_t a, uint32_t b) const {
    uint32_t r = 0;
    while (b) {
      if (b & 1) r ^= a;
      b >>= 1;
      a <<= 1;
      if (a >> m & 1) a ^= poly;
    }
    return r;
  }
};

static std::vector<uint64_t> lifted_gabidulin(const Space& S, int m, int kappa) {
  GF2m K(m);
  const uint64_t count = uint64_t(1) << (m * kappa);
  std::vector<uint64_t> idx(count);
#pragma omp parallel for schedule(static)
  for (int64_t code = 0; code < (int64_t)count; ++code) {
    uint32_t coef[8];
    for (int i = 0; i < kappa; ++i) coef[i] = (uint32_t)((code >> (m * i)) & ((1 << m) - 1));
    std::vector<Vec> rows;
    for (int j = 0; j < m; ++j) {
      uint32_t x = 1u << j, y = 0, xp = x;  // xp = x^(2^i)
      for (int i = 0; i < kappa; ++i) {
        y ^= K.mul(coef[i], xp);
        xp = K.mul(xp, xp);
      }
      Vec vrow = 0;
      for (int t = 0; t < m; ++t) {
        if (x >> t & 1) vrow = put(vrow, t, 1);
        if (y >> t & 1) vrow = put(vrow, m + t, 1);
      }
      rows.push_back(vrow);
    }
    idx[(size_t)code] = S.rank_gr(2 * m, S.echelon(rows, 2 * m));
  }
  return idx;
}

// Rank distribution of a linear MRD code of m x m matrices with minimum distance delta.
static std::vector<double> mrd_distribution(const Space& S, int m, int delta) {
  std::vector<double> A(m + 1, 0.0);
  A[0] = 1;
  const double q = S.q;
  for (int i = delta; i <= m; ++i) {
    double sum = 0;
    for (int j = 0; j <= i - delta; ++j)
      sum += ((j % 2) ? -1.0 : 1.0) * std::pow(q, j * (j - 1) / 2.0) * (double)S.G(i, j) *
             (std::pow(q, m * (i - delta + 1 - j)) - 1.0);
    A[i] = (double)S.G(m, i) * sum;
  }
  return A;
}

void part_code(Csv& csv, int m, int delta, double brute_sample) {
  GF F(2);
  Space S(F);
  RealArith ar(2);
  const int n = 2 * m, k = m, kappa = m - delta + 1;
  auto t0 = clk::now();
  auto cw = lifted_gabidulin(S, m, kappa);
  double t_code = seconds_since(t0);
  t0 = clk::now();
  GrassmannOps<RealArith> G(S, n, k, ar);
  double plan_s = seconds_since(t0);
  const uint64_t v = G.v();
  hvec<double> ind(v, 0.0);
  for (uint64_t c : cw) ind[c] += 1.0;
  uint64_t distinct = 0;
  for (uint64_t u = 0; u < v; ++u) distinct += ind[u] > 0;
  std::vector<hvec<float>> prof;  // exact: counts <= |C| < 2^24
  t0 = clk::now();
  G.distance_profiles(ind.data(), prof);
  double t_prof = seconds_since(t0);
  // validation 1: every codeword sees the MRD rank distribution
  auto Aw = mrd_distribution(S, m, delta);
  double max_dev = 0;
  for (uint64_t c : cw)
    for (int i = 0; i <= k; ++i) max_dev = std::max(max_dev, std::abs(prof[i][c] - Aw[i]));
  // validation 2: profiles of every U sum to |C|
  double max_sum_dev = 0;
  std::vector<uint64_t> hist(k + 1, 0);
  int cover = 0;
  for (uint64_t u = 0; u < v; ++u) {
    double s = 0;
    int dist = -1;
    for (int i = 0; i <= k; ++i) {
      s += prof[i][u];
      if (dist < 0 && prof[i][u] > 0.5) dist = i;
    }
    max_sum_dev = std::max(max_sum_dev, std::abs(s - (double)cw.size()));
    hist[dist]++;
    cover = std::max(cover, dist);
  }
  // brute force on a random sample of centers (all codewords each)
  std::mt19937_64 rng(5);
  const uint64_t sample = std::min<uint64_t>(v, (uint64_t)brute_sample);
  std::vector<Sub> code_subs(cw.size());
  for (size_t i = 0; i < cw.size(); ++i) code_subs[i] = S.unrank_gr(n, k, cw[i]);
  uint64_t mismatches = 0;
  t0 = clk::now();
  for (uint64_t t = 0; t < sample; ++t) {
    uint64_t u = rng() % v;
    Sub U = S.unrank_gr(n, k, u);
    std::vector<double> cnt(k + 1, 0);
    for (auto& W : code_subs) cnt[S.dim_of_sum(U, W, n) - k] += 1;
    for (int i = 0; i <= k; ++i) mismatches += std::abs(cnt[i] - prof[i][u]) > 1e-6;
  }
  double t_brute_sample = seconds_since(t0);
  double t_brute_est = t_brute_sample / (double)sample * (double)v;
  std::printf("lifted Gabidulin m=%d delta=%d |C|=%zu (distinct %llu) in Gr(%d,%d), v=%llu\n", m, delta, cw.size(),
              (unsigned long long)distinct, n, k, (unsigned long long)v);
  std::printf("   profiles: %.3g s (plan %.3g s, code %.3g s); MRD-distribution max dev %.2g; sum dev %.2g\n", t_prof,
              plan_s, t_code, max_dev, max_sum_dev);
  std::printf("   brute force on %llu sampled centers: %llu mismatches; est. full brute force %.3g s\n",
              (unsigned long long)sample, (unsigned long long)mismatches, t_brute_est);
  std::printf("   covering radius (graph distance) = %d; distance histogram:", cover);
  for (int i = 0; i <= k; ++i) std::printf(" %llu", (unsigned long long)hist[i]);
  std::printf("\n");
  std::map<std::string, std::string> r;
  r["experiment"] = "code";
  r["q"] = "2";
  r["n"] = str(n);
  r["k"] = str(k);
  r["v"] = str(v);
  r["M"] = str(G.table_size());
  r["method"] = "fast";
  r["t_median"] = str(t_prof);
  r["plan_s"] = str(plan_s);
  r["peak_rss_gb"] = str(peak_rss_gb());
  std::string note = "delta=" + str(delta) + ";|C|=" + str(cw.size()) + ";cover=" + str(cover) +
                     ";mrd_dev=" + str(max_dev) + ";sum_dev=" + str(max_sum_dev) + ";hist=";
  for (int i = 0; i <= k; ++i) note += (i ? "|" : "") + str(hist[i]);
  note += ";sample=" + str(sample) + ";mismatch=" + str(mismatches);
  r["note"] = note;
  csv.row(r);
  r["method"] = "brute_estimate";
  r["t_median"] = str(t_brute_est);
  r["note"] = "extrapolated from " + str(sample) + " sampled centers x |C| codewords";
  csv.row(r);
}

int main(int argc, char** argv) {
  std::string part = arg(argc, argv, "part", "kernel");
  std::string out = arg(argc, argv, "out", "results/grassmann.csv");
  Csv csv(out, kCols);
  if (part == "kernel") {
    int q = std::stoi(arg(argc, argv, "q", "2"));
    int n = std::stoi(arg(argc, argv, "n", "8"));
    int k = std::stoi(arg(argc, argv, "k", "4"));
    double graph_gb = std::stod(arg(argc, argv, "graph-gb", "3"));
    double budget = std::stod(arg(argc, argv, "budget", "3"));
    if (q % 2 == 0) part_kernel<RealArith>(csv, q, n, k, graph_gb, budget);
    else part_kernel<ComplexArith>(csv, q, n, k, graph_gb, budget);
  } else {
    int m = std::stoi(arg(argc, argv, "m", "4"));
    int delta = std::stoi(arg(argc, argv, "delta", "2"));
    double sample = std::stod(arg(argc, argv, "sample", "200"));
    part_code(csv, m, delta, sample);
  }
}
