// Paired timing of the FFT recursion, the hybrid and the covering sweep.
//
// Cloud machines drift by tens of percent over minutes, so speedups are
// measured in rounds: in each round every method runs three times back to back
// (its best run is the warm-cache time), the methods follow each other in a
// rotating order, and the per-round time ratios are summarised by their median
// and quartiles.  This cancels slow drift without changing cache conditions.
//
// When the covering pairs do not fit in memory (--sample f < 1), the sweep is
// timed on contiguous chunks of the table holding a fraction f of the upper
// elements, with the full-size value array, and its time is scaled by the
// ratio of all covering pairs to the pairs in the chunks.
//
// usage: bench_paired --q 2 --nmin 6 --nmax 9 --rounds 21 --out results/paired.csv [--sample 1]
#include <algorithm>
#include <random>

#include "common.hpp"
#include "fsc/zeta.hpp"

using namespace fsc;
using namespace bench;

static const std::vector<std::string> kCols = {"q", "n", "N", "direction", "rounds", "threshold",
                                               "fast_median", "hybrid_median", "lattice_median",
                                               "ratio_fast_q1", "ratio_fast_median", "ratio_fast_q3",
                                               "ratio_hybrid_q1", "ratio_hybrid_median", "ratio_hybrid_q3",
                                               "sweep_fraction", "pairs", "index_gb"};

static double quantile(std::vector<double> v, double p) {
  std::sort(v.begin(), v.end());
  double idx = p * (v.size() - 1);
  size_t lo = (size_t)idx, hi = std::min(lo + 1, v.size() - 1);
  return v[lo] + (idx - lo) * (v[hi] - v[lo]);
}

// Covering pairs of the upper elements in `nchunks` evenly spaced contiguous
// ranges of positions, together a fraction `frac` of the table (same layout and
// pair order as build_lattice_plan).
inline std::unique_ptr<LatticePlan> build_lattice_chunks(const Space& S, int n, int k, double frac, int nchunks) {
  auto L = std::make_unique<LatticePlan>();
  L->n = n;
  L->k = k;
  L->M = S.M(n, k);
  const uint64_t M = L->M, len = std::max<uint64_t>(1, (uint64_t)(frac * (double)M / nchunks));
  std::vector<std::vector<LatticePlan::Label>> part(nchunks, std::vector<LatticePlan::Label>(n));
#pragma omp parallel for schedule(dynamic, 1)
  for (int c = 0; c < nchunks; ++c) {
    auto& my = part[(size_t)c];
    for (auto& l : my) l.ptr.push_back(0);
    const uint64_t lo = M * (uint64_t)c / (uint64_t)nchunks, hi = std::min(M, lo + len);
    std::vector<uint32_t> tmp;
    for (uint64_t w = lo; w < hi; ++w) {
      Sub Wb = S.unrank_L(n, k, w);
      for (int i = 0; i < Wb.d; ++i) {
        const int label = lead(Wb.r[i]);
        const uint64_t cnt = S.qpow[Wb.d - i - 1];
        tmp.clear();
        for (uint64_t cc0 = 0; cc0 < cnt; ++cc0) {
          Sub Ub;
          Ub.d = Wb.d - 1;
          for (int t = 0; t < i; ++t) Ub.r[t] = Wb.r[t];
          uint64_t cc = cc0;
          for (int t = i + 1; t < Wb.d; ++t) {
            const int coef = int(cc % (uint64_t)S.q);
            cc /= (uint64_t)S.q;
            Ub.r[t - 1] = S.axpy(Wb.r[t], coef, Wb.r[i], n);
          }
          tmp.push_back((uint32_t)S.pos_L(n, k, Ub));
        }
        std::sort(tmp.begin(), tmp.end());
        auto& l = my[(size_t)label];
        l.W.push_back((uint32_t)w);
        l.U.insert(l.U.end(), tmp.begin(), tmp.end());
        l.ptr.push_back(l.U.size());
      }
    }
  }
  L->lab.assign(n, {});
  for (int t = 0; t < n; ++t) {
    auto& dst = L->lab[(size_t)t];
    dst.ptr.push_back(0);
    for (int c = 0; c < nchunks; ++c) {
      auto& src = part[(size_t)c][(size_t)t];
      const uint64_t base = dst.U.size();
      dst.W.insert(dst.W.end(), src.W.begin(), src.W.end());
      dst.U.insert(dst.U.end(), src.U.begin(), src.U.end());
      for (size_t i = 1; i < src.ptr.size(); ++i) dst.ptr.push_back(base + src.ptr[i]);
      src = {};
    }
  }
  return L;
}

template <class A>
void run_case(Csv& csv, int q, int n, int rounds, double sample) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  const uint64_t N = S.M(n, n);
  std::mt19937_64 rng(77 + 1000 * q + n);
  std::uniform_real_distribution<double> U(-1, 1);
  hvec<double> f(N);
  for (auto& v : f) v = U(rng);

  // One planner serves both variants: threshold 0 is the pure FFT recursion,
  // threshold t > 0 the hybrid (sweep plans of small nodes are built once).
  ZetaPlanner P(S);
  ZetaNode* root = P.get(n, n);
  int cur_t = 0;
  auto use = [&](int t) {
    if (t != cur_t) P.set_lattice_threshold(t);
    cur_t = t;
  };
  uint64_t pairs = 0;
  for (int j = 1; j <= n; ++j) pairs += S.G(n, j) * S.G(j, 1);
  auto L = sample >= 1 ? build_lattice_plan(S, n, n) : build_lattice_chunks(S, n, n, sample, 64);
  const double scale = (double)pairs / (double)L->pairs();  // 1 for the full index
  using T = typename A::T;
  hvec<T> X(N), Y(N);
  hvec<double> x(N);
  ZetaExec<A> ex{ar, q, F.e};

  auto t_fft = [&](int t, Mode mode) {
    use(t);
    for (uint64_t i = 0; i < N; ++i) X[i] = A::from_double(f[i]);
    auto t0 = clk::now();
    ex.run(root, X.data(), Y.data(), 1, mode, true);
    return seconds_since(t0);
  };
  auto t_lat = [&](bool inverse) {
    x = f;
    auto t0 = clk::now();
    lattice_apply<RealArith>(*L, x.data(), 1, inverse, false);
    return seconds_since(t0) * scale;
  };
  // hybrid threshold: best of t = 1..n-1 on three paired rounds
  int best_t = 1;
  double best = 1e300;
  for (int t = 1; t < n; ++t) {
    t_fft(t, Mode::Forward);
    double tt = 1e300;
    for (int r = 0; r < 3; ++r) tt = std::min(tt, t_fft(t, Mode::Forward));
    if (tt < best) { best = tt; best_t = t; }
  }

  for (Mode mode : {Mode::Forward, Mode::Inverse}) {
    const bool inv = mode == Mode::Inverse;
    t_fft(0, mode); t_fft(best_t, mode); t_lat(inv);  // warm-up
    std::vector<double> tf, th, tl, rf_, rh_;
    // warm time of a method inside a round: best of `reps` back-to-back runs
    const int reps = 3;
    auto warm_fft = [&](int t) {
      double m = 1e300;
      for (int i = 0; i < reps; ++i) m = std::min(m, t_fft(t, mode));
      return m;
    };
    auto warm_lat = [&] {
      double m = 1e300;
      for (int i = 0; i < reps; ++i) m = std::min(m, t_lat(inv));
      return m;
    };
    for (int r = 0; r < rounds; ++r) {
      // rotate the order inside each round to avoid systematic position effects
      double a = 0, b = 0, c = 0;
      switch (r % 3) {
        case 0: a = warm_fft(0); b = warm_fft(best_t); c = warm_lat(); break;
        case 1: c = warm_lat(); a = warm_fft(0); b = warm_fft(best_t); break;
        default: b = warm_fft(best_t); c = warm_lat(); a = warm_fft(0); break;
      }
      tf.push_back(a); th.push_back(b); tl.push_back(c);
      rf_.push_back(c / a); rh_.push_back(c / b);
    }
    std::map<std::string, std::string> row{
        {"q", str(q)}, {"n", str(n)}, {"N", str(N)}, {"direction", inv ? "mobius" : "zeta"},
        {"rounds", str(rounds)}, {"threshold", str(best_t)},
        {"fast_median", str(quantile(tf, 0.5))}, {"hybrid_median", str(quantile(th, 0.5))},
        {"lattice_median", str(quantile(tl, 0.5))},
        {"ratio_fast_q1", str(quantile(rf_, 0.25))}, {"ratio_fast_median", str(quantile(rf_, 0.5))},
        {"ratio_fast_q3", str(quantile(rf_, 0.75))},
        {"ratio_hybrid_q1", str(quantile(rh_, 0.25))}, {"ratio_hybrid_median", str(quantile(rh_, 0.5))},
        {"ratio_hybrid_q3", str(quantile(rh_, 0.75))},
        {"sweep_fraction", str(1.0 / scale)}, {"pairs", str(pairs)}, {"index_gb", str(pairs * 4.0 / 1e9)}};
    csv.row(row);
    std::printf("q=%d n=%d N=%llu %s: speedup over sweep  FFT %.2fx [%.2f, %.2f]  hybrid(t=%d) %.2fx [%.2f, %.2f]"
                "  (fft %.4g s, hybrid %.4g s, sweep %.4g s%s)\n",
                q, n, (unsigned long long)N, inv ? "mobius" : "zeta", quantile(rf_, 0.5), quantile(rf_, 0.25),
                quantile(rf_, 0.75), best_t, quantile(rh_, 0.5), quantile(rh_, 0.25), quantile(rh_, 0.75),
                quantile(tf, 0.5), quantile(th, 0.5), quantile(tl, 0.5),
                scale > 1 ? ", sweep sampled" : "");
    std::fflush(stdout);
  }
}

int main(int argc, char** argv) {
  int q = std::stoi(arg(argc, argv, "q", "2"));
  int nmin = std::stoi(arg(argc, argv, "nmin", "6"));
  int nmax = std::stoi(arg(argc, argv, "nmax", "9"));
  int rounds = std::stoi(arg(argc, argv, "rounds", "21"));
  std::string out = arg(argc, argv, "out", "results/paired.csv");
  double sample = std::stod(arg(argc, argv, "sample", "1"));
  Csv csv(out, kCols);
  for (int n = nmin; n <= nmax; ++n) {
    if (q % 2 == 0) run_case<RealArith>(csv, q, n, rounds, sample);
    else run_case<ComplexArith>(csv, q, n, rounds, sample);
  }
}
