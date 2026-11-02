// Checks of the Grassmannian applications against dense pairwise evaluation.
#include <cmath>
#include <cstdio>
#include <random>

#include "fsc/grassmann_apps.hpp"

using namespace fsc;

static int failures = 0, checks = 0;
#define CHECK(cond, ...)                               \
  do {                                                 \
    ++checks;                                          \
    if (!(cond)) {                                     \
      ++failures;                                      \
      std::printf("FAIL %s:%d: ", __FILE__, __LINE__); \
      std::printf(__VA_ARGS__);                        \
      std::printf("\n");                               \
    }                                                  \
  } while (0)

template <class A>
static void test_grassmann(int q, int n, int k) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  GrassmannOps<A> G(S, n, k, ar);
  const uint64_t v = G.v();
  std::vector<Sub> subs(v);
  for (uint64_t i = 0; i < v; ++i) subs[i] = S.unrank_gr(n, k, i);
  std::vector<std::vector<int>> dist(v, std::vector<int>(v));
  for (uint64_t u = 0; u < v; ++u)
    for (uint64_t w = 0; w < v; ++w) dist[u][w] = S.dim_of_sum(subs[u], subs[w], n) - k;
  std::mt19937_64 rng(q * 100 + n);
  std::uniform_real_distribution<double> U(-1, 1);
  std::vector<double> f(v), y(v);
  for (auto& x : f) x = U(rng);
  const int s = std::min(k, n - k);
  std::vector<double> a(s + 1);
  for (auto& x : a) x = U(rng);
  // kernel product
  G.kernel_apply(a, f.data(), y.data());
  double err = 0, sc = 1e-300;
  for (uint64_t u = 0; u < v; ++u) {
    double want = 0;
    for (uint64_t w = 0; w < v; ++w) want += a[dist[u][w]] * f[w];
    err = std::max(err, std::abs(y[u] - want));
    sc = std::max(sc, std::abs(want));
  }
  CHECK(err <= 1e-10 * sc, "kernel q=%d Gr(%d,%d) err=%g", q, n, k, err / sc);
  // distance profiles
  std::vector<hvec<double>> prof;
  G.distance_profiles(f.data(), prof);
  double perr = 0;
  for (uint64_t u = 0; u < v; ++u) {
    std::vector<double> want(k + 1, 0.0);
    for (uint64_t w = 0; w < v; ++w) want[dist[u][w]] += f[w];
    for (int i = 0; i <= k; ++i) perr = std::max(perr, std::abs(prof[i][u] - want[i]));
  }
  CHECK(perr <= 1e-9, "profiles q=%d Gr(%d,%d) err=%g", q, n, k, perr);
  // graph recurrence baseline
  CSR Adj = build_grassmann_adjacency(S, n, k);
  CHECK(Adj.nnz() == v * (uint64_t)q * S.G(k, 1) * S.G(n - k, 1), "adjacency degree q=%d Gr(%d,%d)", q, n, k);
  std::vector<hvec<double>> gp;
  graph_distance_profiles(S, n, k, Adj, f.data(), gp);
  double gerr = 0;
  for (int i = 0; i <= s; ++i)
    for (uint64_t u = 0; u < v; ++u) gerr = std::max(gerr, std::abs(gp[i][u] - prof[i][u]));
  CHECK(gerr <= 1e-8, "graph recurrence q=%d Gr(%d,%d) err=%g", q, n, k, gerr);
}

int main() {
  test_grassmann<RealArith>(2, 4, 2);
  test_grassmann<RealArith>(2, 6, 3);
  test_grassmann<RealArith>(2, 7, 2);
  test_grassmann<ComplexArith>(3, 4, 2);
  test_grassmann<ComplexArith>(3, 5, 2);
  test_grassmann<RealArith>(4, 4, 2);
  test_grassmann<ComplexArith>(5, 4, 2);
  test_grassmann<RealArith>(8, 4, 2);
  test_grassmann<ComplexArith>(7, 4, 2);
  std::printf("%d checks, %d failures\n", checks, failures);
  return failures ? 1 : 0;
}
