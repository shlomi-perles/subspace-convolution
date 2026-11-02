// Poisson summation over a-tuples of vectors, run (not only counted) as a
// baseline for the incidence transform I_n^{a,b} (Theorem 2).
//
// Lift f to the a-tuple of rows of each subspace's reduced echelon basis:
// F(x_1,...,x_a) = f(U) if (x_1,...,x_a) is that basis of U, and 0 otherwise.
// Every U <= W has exactly one such tuple, and it lies in W^a, so for W in
// Gr(n,b)
//   sum_{U <= W, dim U = a} f(U) = sum_{x in W^a} F(x)
//                                = q^{-a(n-b)} sum_{y in (W^perp)^a} F^(y),
// where F^ is the Fourier transform on F_q^{an}.  (Writing f at all |GL(a,q)|
// ordered bases would also work but costs |GL(a,q)| times more writes.)
//
// As for the fast transform, index structures are built before timing (with
// OpenMP): the table position of each echelon basis, and for each W the
// indices of the q^{n-b} vectors of W^perp.  Three timed stages, on one core:
//   lift   zero the q^{an} table and write f(U) at its echelon basis;
//   fft    in-place transform of the q^{an} table: for q = 2^e a cache-blocked
//          Walsh-Hadamard transform (16 levels per in-cache block, then 7 levels
//          per pass over memory, so 36 levels take 4 passes); for odd q the
//          radix-p DFT of arith.hpp, blocked in the same way;
//   sums   for every W, the q^{a(n-b)} frequencies of (W^perp)^a, gathered
//          with software prefetching.
// The fast transform runs in the same process on the same input; the two
// outputs are compared on all of Gr(n,b), and both against direct summation at
// random outputs.
//
// usage: bench_poisson --q 2 --n 11 --a 3 --b 8 [--samples 200] [--fast 1]
//                      [--budget 5] --out results/poisson.csv
#include <array>
#include <cmath>
#include <cstring>
#include <random>
#include <type_traits>

#include "common.hpp"
#include "fsc/incidence.hpp"
#include "fsc/naive.hpp"

using namespace fsc;
using namespace bench;

static const std::vector<std::string> kCols = {
    "q",         "n",         "a",          "b",          "S",           "t",
    "tuple_values", "poisson_gb", "poisson_plan_s", "lift_s",    "fft_s",       "sums_s",
    "poisson_s", "fft_flops", "sum_adds",   "fast_s",     "fast_flops",  "fast_gb",
    "fast_plan_s", "fast_reps", "poisson_reps", "max_rel_err_poisson", "max_rel_err_fast", "max_rel_diff_all",
    "samples"};

// ---- Walsh-Hadamard transform on 2^L doubles, blocked for the cache ---------
static void wht_in_cache(double* x, int L) {
  const size_t n = size_t(1) << L;
  for (int s = 0; s < L; ++s) {
    const size_t h = size_t(1) << s;
    for (size_t base = 0; base < n; base += 2 * h)
      for (size_t i = base; i < base + h; ++i) {
        const double u = x[i], v = x[i + h];
        x[i] = u + v;
        x[i + h] = u - v;
      }
  }
}

static void wht_blocked(double* x, int L) {
  constexpr int kLo = 16;        // 2^16 doubles = 512 KiB per in-cache block
  constexpr int kGroup = 7;      // levels per pass over memory
  constexpr size_t kTile = 512;  // 2^7 rows x 512 doubles = 512 KiB per tile
  const int lo = std::min(L, kLo);
  const size_t n = size_t(1) << L, blk = size_t(1) << lo;
  for (size_t b0 = 0; b0 < n; b0 += blk) wht_in_cache(x + b0, lo);
  for (int s = lo; s < L; s += kGroup) {
    const int g = std::min(kGroup, L - s);
    const size_t stride = size_t(1) << s, rows = size_t(1) << g, span = stride << g;
    for (size_t sup = 0; sup < n; sup += span)
      for (size_t off = 0; off < stride; off += kTile) {
        double* base = x + sup + off;
        for (int l = 0; l < g; ++l) {
          const size_t hr = size_t(1) << l;
          for (size_t r0 = 0; r0 < rows; r0 += 2 * hr)
            for (size_t r = r0; r < r0 + hr; ++r) {
              double* A = base + r * stride;
              double* B = base + (r + hr) * stride;
              for (size_t t = 0; t < kTile; ++t) {
                const double u = A[t], v = B[t];
                A[t] = u + v;
                B[t] = u - v;
              }
            }
        }
      }
  }
}

// ---- radix-p DFT for odd p, blocked the same way ----------------------------
static void dft_blocked(const ComplexArith& ar, Cplx* x, int L) {
  int lo = 0;
  size_t blk = 1;
  while (lo < L && blk * (size_t)ar.p * sizeof(Cplx) <= (size_t(512) << 10)) { blk *= (size_t)ar.p; ++lo; }
  size_t n = 1;
  for (int i = 0; i < L; ++i) n *= (size_t)ar.p;
  for (size_t b0 = 0; b0 < n; b0 += blk) ar.dft(x + b0, lo, 1, +1);
  if (L > lo) ar.dft(x, L - lo, blk, +1);  // rows of length blk: one streaming pass per level
}

// ---- helpers ------------------------------------------------------------------
// Index of a vector (element codes = polynomial-basis digits) in F_q^n.
static uint64_t vec_index(Vec v, int n, uint64_t q) {
  uint64_t idx = 0;
  for (int j = n - 1; j >= 0; --j) idx = idx * q + (uint64_t)get(v, j);
  return idx;
}
// Index of a frequency (trace-dual digits).
static uint64_t dual_index(const GF& F, Vec y, int n, uint64_t q) {
  uint64_t idx = 0;
  for (int j = n - 1; j >= 0; --j) idx = idx * q + (uint64_t)F.elem_to_dual[get(y, j)];
  return idx;
}
inline double real_part(double v) { return v; }
inline double real_part(const Cplx& v) { return v.re; }

struct Poisson {
  const Space& S;
  int q, n, a, b, c;
  uint64_t qn, qc;       // q^n, q^c with c = n - b
  double norm = 0;       // q^{-a c}
  hvec<uint64_t> lift_idx;  // |Gr(n,a)| table positions of the echelon bases
  hvec<uint64_t> perp;      // |Gr(n,b)| x q^c: frequency indices of the vectors of W^perp

  Poisson(const Space& S_, int n_, int a_, int b_) : S(S_), q(S_.q), n(n_), a(a_), b(b_), c(n_ - b_) {
    qn = S.qpow[n];
    qc = S.qpow[c];
    norm = std::pow((double)q, -(double)(a * c));
  }

  void build() {
    const uint64_t Na = S.G(n, a), Nb = S.G(n, b);
    lift_idx.assign(Na, 0);
    perp.assign(Nb * qc, 0);
#pragma omp parallel for schedule(dynamic, 1024)
    for (int64_t uu = 0; uu < (int64_t)Na; ++uu) {
      const Sub U = S.unrank_gr(n, a, (uint64_t)uu);
      uint64_t idx = 0, mult = 1;
      for (int i = 0; i < a; ++i, mult *= qn) idx += vec_index(U.r[i], n, (uint64_t)q) * mult;
      lift_idx[(size_t)uu] = idx;
    }
#pragma omp parallel for schedule(dynamic, 1024)
    for (int64_t ww = 0; ww < (int64_t)Nb; ++ww) {
      const Sub P = S.annihilator(S.unrank_gr(n, b, (uint64_t)ww), n);
      uint64_t* out = perp.data() + (size_t)ww * qc;
      for (uint64_t cc = 0; cc < qc; ++cc) {
        Vec y = 0;
        uint64_t r = cc;
        for (int k = 0; k < c; ++k) { y = S.axpy(y, (int)(r % (uint64_t)q), P.r[k], n); r /= (uint64_t)q; }
        out[cc] = dual_index(S.F, y, n, (uint64_t)q);
      }
    }
  }

  template <class T, class FromDouble>
  void lift(const double* f, T* Ftab, FromDouble conv) const {
    const uint64_t Na = lift_idx.size();
    for (uint64_t u = 0; u < Na; ++u) Ftab[lift_idx[u]] = conv(f[u]);
  }

  template <class T>
  void sums(const T* Fh, double* out) const {
    const uint64_t Nb = perp.size() / qc;
    uint64_t terms = 1;
    for (int i = 0; i < a; ++i) terms *= qc;
    std::vector<uint64_t> buf(terms), shifted((size_t)a * qc);
    for (uint64_t w = 0; w < Nb; ++w) {
      const uint64_t* v = perp.data() + w * qc;
      // all a-tuples of vectors of W^perp: block i of a tuple index is a
      // vector index times qn^i, so nested partial sums need one addition per
      // tuple (blocks never carry into each other)
      uint64_t mult = 1;
      for (int i = 0; i < a; ++i, mult *= qn)
        for (uint64_t k = 0; k < qc; ++k) shifted[(size_t)i * qc + k] = v[k] * mult;
      buf[0] = 0;
      uint64_t len = 1;
      for (int i = a - 1; i >= 0; --i) {  // buf[j * qc + k] = buf_old[j] + shifted[i][k]
        const uint64_t* sh = shifted.data() + (size_t)i * qc;
        for (uint64_t j = len; j-- > 0;) {
          const uint64_t base = buf[j];
          for (uint64_t k = 0; k < qc; ++k) buf[j * qc + k] = base + sh[k];
        }
        len *= qc;
      }
      constexpr uint64_t D = 24;
      double acc = 0;
      for (uint64_t s = 0; s < terms; ++s) {
        if (s + D < terms) __builtin_prefetch(Fh + buf[s + D]);
        acc += real_part(Fh[buf[s]]);
      }
      out[w] = acc * norm;
    }
  }
};

template <class A>
void run(Csv& csv, int q, int n, int a, int b, int samples, bool with_fast, double budget) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  using T = typename A::T;
  const uint64_t Nin = S.G(n, a), Nout = S.G(n, b);
  std::mt19937_64 rng(7 + n * 31 + a * 7 + b + 1000 * q);  // same input as bench_incidence_hard
  std::uniform_real_distribution<double> Ud(-1, 1);
  hvec<double> f(Nin);
  for (auto& x : f) x = Ud(rng);

  const int L = a * n * F.e;  // base-p digits of the tuple space
  uint64_t tv = 1;
  for (int i = 0; i < a * n; ++i) tv *= (uint64_t)q;
  const double tuple_gb = (double)tv * sizeof(T) / 1e9;
  std::printf("q=%d (n,a,b)=(%d,%d,%d): Poisson table q^%d = %.3g values (%.1f GB)\n", q, n, a, b, a * n,
              (double)tv, tuple_gb);
  std::fflush(stdout);

  // ---- fast transform (Theorem 2) on the same input ----
  hvec<double> fast_out;
  double fast_s = NAN, fast_flops = NAN, fast_gb = NAN, fast_plan_s = NAN;
  int fast_reps = 0;
  if (with_fast) {
    auto p0 = clk::now();
    IncPlanner Pl(S);
    IncNode* nd = Pl.get(n, a, b);
    fast_plan_s = seconds_since(p0);
    const uint64_t need = arena_need(nd, 1);
    fast_gb = (double)(Nin + Nout + need) * sizeof(T) / 1e9 + Pl.plan_bytes() / 1e9;
    hvec<T> X(Nin), Z(Nout);
    for (uint64_t i = 0; i < Nin; ++i) X[i] = A::from_double(f[i]);
    Arena<T> arena(need + 1);
    IncExec<A> ex{ar, q, F.e};
    auto body = [&] { ex.run(nd, X.data(), Z.data(), 1, arena); };
    auto c0 = clk::now();
    body();
    const double single = seconds_since(c0);
    Timing tm = time_runs(reps_for(single, budget, 3, 15), [] {}, body, false);
    fast_s = tm.median;
    fast_reps = tm.reps;
    fast_flops = inc_flops(nd, ar, 1.0);
    fast_out.resize(Nout);
    for (uint64_t w = 0; w < Nout; ++w) fast_out[w] = A::to_double(Z[w]);
    std::printf("  fast: %.4g s (median of %d), %.3g flops, %.2f GB, plan %.3g s\n", fast_s, fast_reps, fast_flops,
                fast_gb, fast_plan_s);
    std::fflush(stdout);
  }

  // ---- Poisson summation ----
  hvec<double> out(Nout);
  double lift_s = 0, fft_s = 0, sums_s = 0, pplan_s = 0, pgb = 0;
  int preps = 0;
  {
    auto p0 = clk::now();
    Poisson P(S, n, a, b);
    P.build();
    pplan_s = seconds_since(p0);
    pgb = tuple_gb + (double)(P.lift_idx.size() + P.perp.size()) * 8 / 1e9;
    hvec<T> Ft(tv);
    std::memset((void*)Ft.data(), 0, tv * sizeof(T));  // fault the pages in before timing
    auto once = [&] {
      auto t0 = clk::now();
      std::memset((void*)Ft.data(), 0, tv * sizeof(T));
      P.lift(f.data(), Ft.data(), [](double v) { return A::from_double(v); });
      const double l = seconds_since(t0);
      t0 = clk::now();
      if constexpr (std::is_same<T, double>::value) wht_blocked(Ft.data(), L);
      else dft_blocked(ar, Ft.data(), L);
      const double ff = seconds_since(t0);
      t0 = clk::now();
      P.sums(Ft.data(), out.data());
      const double sm = seconds_since(t0);
      return std::array<double, 3>{l, ff, sm};
    };
    auto first = once();
    const double tot1 = first[0] + first[1] + first[2];
    const int reps = tot1 > budget ? 1 : reps_for(tot1, budget, 3, 9);
    std::vector<std::array<double, 3>> all{first};
    for (int r = 1; r < reps; ++r) all.push_back(once());
    auto med = [&](int k) {
      std::vector<double> v;
      for (auto& x : all) v.push_back(x[k]);
      std::sort(v.begin(), v.end());
      return v[v.size() / 2];
    };
    lift_s = med(0);
    fft_s = med(1);
    sums_s = med(2);
    preps = (int)all.size();
  }
  const double poisson_s = lift_s + fft_s + sums_s;
  const double fft_flops = std::is_same<T, double>::value ? (double)L * (double)tv : ar.dft_flops(L);
  const double sum_adds = (double)Nout * std::pow((double)q, a * (n - b));
  std::printf("  poisson: lift %.4g s, fft %.4g s, sums %.4g s, total %.4g s (%d run%s), %.1f GB, plan %.3g s\n",
              lift_s, fft_s, sums_s, poisson_s, preps, preps > 1 ? "s" : "", pgb, pplan_s);
  std::fflush(stdout);

  // ---- correctness: direct sums at random outputs, and Poisson vs fast everywhere ----
  std::mt19937_64 pick(99 + q * 100 + n * 10 + a);
  const uint64_t per = S.G(b, a);
  double ep = 0, ef = 0, sc = 0;
  for (int s = 0; s < samples; ++s) {
    const uint64_t w = pick() % Nout;
    const Sub W = S.unrank_gr(n, b, w);
    double acc = 0;
    for (uint64_t cc = 0; cc < per; ++cc) acc += f[S.rank_gr(n, combine(S, S.unrank_gr(b, a, cc), W, n))];
    sc = std::max(sc, std::abs(acc));
    ep = std::max(ep, std::abs(out[w] - acc));
    if (with_fast) ef = std::max(ef, std::abs(fast_out[w] - acc));
  }
  double dall = NAN;
  if (with_fast) {
    double d = 0, m = 0;
    for (uint64_t w = 0; w < Nout; ++w) {
      d = std::max(d, std::abs(out[w] - fast_out[w]));
      m = std::max(m, std::abs(fast_out[w]));
    }
    dall = d / m;
  }
  std::printf("  check: max rel err vs direct (%d samples): poisson %.2g, fast %.2g; poisson vs fast on all %llu "
              "outputs: %.2g\n",
              samples, ep / sc, ef / sc, (unsigned long long)Nout, dall);
  std::fflush(stdout);

  csv.row({{"q", str(q)},
           {"n", str(n)},
           {"a", str(a)},
           {"b", str(b)},
           {"S", str(Nin + Nout)},
           {"t", str(a)},
           {"tuple_values", str((double)tv)},
           {"poisson_gb", str(pgb)},
           {"poisson_plan_s", str(pplan_s)},
           {"lift_s", str(lift_s)},
           {"fft_s", str(fft_s)},
           {"sums_s", str(sums_s)},
           {"poisson_s", str(poisson_s)},
           {"fft_flops", str(fft_flops)},
           {"sum_adds", str(sum_adds)},
           {"fast_s", str(fast_s)},
           {"fast_flops", str(fast_flops)},
           {"fast_gb", str(fast_gb)},
           {"fast_plan_s", str(fast_plan_s)},
           {"fast_reps", str(fast_reps)},
           {"poisson_reps", str(preps)},
           {"max_rel_err_poisson", str(ep / sc)},
           {"max_rel_err_fast", str(ef / sc)},
           {"max_rel_diff_all", str(dall)},
           {"samples", str(samples)}});
}

int main(int argc, char** argv) {
  const std::string out = arg(argc, argv, "out", "results/poisson.csv");
  const int q = std::stoi(arg(argc, argv, "q", "2"));
  const int n = std::stoi(arg(argc, argv, "n", "8"));
  const int a = std::stoi(arg(argc, argv, "a", "2"));
  const int b = std::stoi(arg(argc, argv, "b", "6"));
  const int samples = std::stoi(arg(argc, argv, "samples", "200"));
  const bool fast = std::stoi(arg(argc, argv, "fast", "1")) != 0;
  const double budget = std::stod(arg(argc, argv, "budget", "5"));
  if (!(0 < a && a < b && b < n)) {
    std::fprintf(stderr, "need 0 < a < b < n\n");
    return 1;
  }
  Csv csv(out, kCols);
  if (q % 2 == 0) run<RealArith>(csv, q, n, a, b, samples, fast, budget);
  else run<ComplexArith>(csv, q, n, a, b, samples, fast, budget);
}
