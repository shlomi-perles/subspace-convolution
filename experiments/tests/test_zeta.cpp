// Exact and floating-point checks of the C++ engine against direct summation.
#include <cmath>
#include <cstdio>
#include <random>
#include <vector>

#include "fsc/naive.hpp"
#include "fsc/zeta.hpp"

using namespace fsc;

static int failures = 0, checks = 0;
#define CHECK(cond, ...)                                    \
  do {                                                      \
    ++checks;                                               \
    if (!(cond)) {                                          \
      ++failures;                                           \
      std::printf("FAIL %s:%d: ", __FILE__, __LINE__);      \
      std::printf(__VA_ARGS__);                             \
      std::printf("\n");                                    \
    }                                                       \
  } while (0)

// Brute-force containment matrix on T(n,k) in L layout.
static std::vector<std::vector<int>> brute_containment(const Space& S, int n, int k) {
  uint64_t M = S.M(n, k);
  std::vector<Sub> subs(M);
  for (uint64_t i = 0; i < M; ++i) subs[i] = S.unrank_L(n, k, i);
  std::vector<std::vector<int>> Z(M, std::vector<int>(M, 0));
  for (uint64_t w = 0; w < M; ++w)
    for (uint64_t u = 0; u < M; ++u) Z[w][u] = S.dim_of_sum(subs[w], subs[u], n) == subs[w].d;
  return Z;
}

static void test_indexing(int q, int nmax) {
  GF F(q);
  Space S(F);
  for (int n = 0; n <= nmax; ++n) {
    for (int d = 0; d <= n; ++d)
      for (uint64_t i = 0; i < S.G(n, d); ++i) {
        Sub U = S.unrank_gr(n, d, i);
        CHECK(S.rank_gr(n, U) == i, "rank_gr q=%d n=%d d=%d i=%llu", q, n, d, (unsigned long long)i);
        CHECK(S.echelon(std::vector<Vec>(U.r, U.r + U.d), n).d == d, "unrank_gr not a basis");
      }
    for (int k = 0; k <= n; ++k)
      for (uint64_t i = 0; i < S.M(n, k); ++i) {
        Sub U = S.unrank_L(n, k, i);
        CHECK(S.pos_L(n, k, U) == i, "pos_L q=%d n=%d k=%d i=%llu", q, n, k, (unsigned long long)i);
      }
  }
}

static void test_exact(int q, int nmax) {
  GF F(q);
  Space S(F);
  ModArith ar(F.p);
  std::mt19937_64 rng(1234 + q);
  for (int n = 0; n <= nmax; ++n)
    for (int k = 0; k <= n; ++k) {
      uint64_t M = S.M(n, k);
      auto Z = brute_containment(S, n, k);
      std::vector<uint64_t> f(M);
      for (auto& v : f) v = rng() % ModArith::P;
      std::vector<uint64_t> zf(M, 0), ztf(M, 0);
      for (uint64_t w = 0; w < M; ++w)
        for (uint64_t u = 0; u < M; ++u)
          if (Z[w][u]) {
            zf[w] = (zf[w] + f[u]) % ModArith::P;
            ztf[u] = (ztf[u] + f[w]) % ModArith::P;
          }
      for (int variant = 0; variant < 3; ++variant) {  // 0 FFT, 1 hybrid (n<=2 lattice), 2 pure lattice
        ZetaPlanner P(S);
        ZetaNode* root = P.get(n, k);
        if (variant == 1) P.set_lattice_threshold(2);
        if (variant == 2) P.set_lattice_threshold(64);
        ZetaExec<ModArith> ex{ar, q, F.e};
        std::vector<uint64_t> X(f), Y(M + 1);
        ex.run(root, X.data(), Y.data(), 1, Mode::Forward);
        CHECK(X == zf, "forward q=%d n=%d k=%d variant=%d", q, n, k, variant);
        ex.run(root, X.data(), Y.data(), 1, Mode::Inverse);
        CHECK(X == f, "inverse q=%d n=%d k=%d variant=%d", q, n, k, variant);
        X = f;
        ex.run(root, X.data(), Y.data(), 1, Mode::Transpose);
        CHECK(X == ztf, "transpose q=%d n=%d k=%d variant=%d", q, n, k, variant);
        ex.run(root, X.data(), Y.data(), 1, Mode::TransposeInverse);
        CHECK(X == f, "transpose-inverse q=%d n=%d k=%d variant=%d", q, n, k, variant);
      }
      // covering pairs
      auto L = build_lattice_plan(S, n, k);
      uint64_t e = 0;
      for (int j = 1; j <= std::min(k, n); ++j) e += S.G(n, j) * S.G(j, 1);
      CHECK(L->pairs() == e, "covering pairs q=%d n=%d k=%d", q, n, k);
      // CSR baseline
      CSR C = build_containment_csr(S, n, k);
      std::vector<uint64_t> y(M);
      csr_apply<ModArith>(C, f.data(), y.data());
      CHECK(y == zf, "csr q=%d n=%d k=%d", q, n, k);
    }
}

// Batched execution with beta > 1 must equal beta independent runs.
static void test_batched(int q, int n) {
  GF F(q);
  Space S(F);
  ModArith ar(F.p);
  ZetaPlanner P(S);
  ZetaNode* root = P.get(n, n);
  ZetaExec<ModArith> ex{ar, q, F.e};
  const size_t beta = 3;
  uint64_t M = S.M(n, n);
  std::mt19937_64 rng(99);
  std::vector<uint64_t> X(M * beta), Y(M * beta);
  for (auto& v : X) v = rng() % ModArith::P;
  std::vector<uint64_t> X0 = X;
  ex.run(root, X.data(), Y.data(), beta, Mode::Forward);
  for (size_t b = 0; b < beta; ++b) {
    std::vector<uint64_t> x(M), y(M);
    for (uint64_t i = 0; i < M; ++i) x[i] = X0[i * beta + b];
    ex.run(root, x.data(), y.data(), 1, Mode::Forward);
    bool ok = true;
    for (uint64_t i = 0; i < M; ++i) ok &= (x[i] == X[i * beta + b]);
    CHECK(ok, "batched q=%d n=%d b=%zu", q, n, b);
  }
}

template <class A>
static void test_float(int q, int n) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  ZetaPlanner P(S);
  ZetaNode* root = P.get(n, n);
  ZetaExec<A> ex{ar, q, F.e};
  uint64_t M = S.M(n, n);
  CSR C = build_containment_csr(S, n, n);
  std::mt19937_64 rng(5);
  std::uniform_real_distribution<double> U(-1, 1);
  std::vector<typename A::T> f(M), X(M), Y(M), z(M);
  for (auto& v : f) v = A::from_double(U(rng));
  csr_apply<A>(C, f.data(), z.data());
  for (bool real : {false, true}) {
    X = f;
    ex.run(root, X.data(), Y.data(), 1, Mode::Forward, real);
    double e1 = 0, sc1 = 0;
    for (uint64_t i = 0; i < M; ++i) {
      e1 = std::max(e1, std::abs(A::to_double(X[i]) - A::to_double(z[i])));
      sc1 = std::max(sc1, std::abs(A::to_double(z[i])));
    }
    CHECK(e1 <= 1e-10 * std::max(1.0, sc1), "float forward q=%d n=%d real=%d err=%g", q, n, (int)real, e1);
    for (Mode md : {Mode::Inverse, Mode::Transpose, Mode::TransposeInverse}) {
      std::vector<typename A::T> X1 = f, X2 = f, Y1(M);
      ex.run(root, X1.data(), Y1.data(), 1, md, false);
      ex.run(root, X2.data(), Y1.data(), 1, md, real);
      double e2 = 0;
      for (uint64_t i = 0; i < M; ++i) e2 = std::max(e2, std::abs(A::to_double(X1[i]) - A::to_double(X2[i])));
      CHECK(e2 <= 1e-10 * std::max(1.0, sc1), "real-mode mode=%d q=%d n=%d err=%g", (int)md, q, n, e2);
    }
  }
  X = f;
  ex.run(root, X.data(), Y.data(), 1, Mode::Forward);
  double err = 0, scale = 0;
  for (uint64_t i = 0; i < M; ++i) {
    err = std::max(err, std::abs(A::to_double(X[i]) - A::to_double(z[i])));
    scale = std::max(scale, std::abs(A::to_double(z[i])));
  }
  CHECK(err <= 1e-10 * std::max(1.0, scale), "float forward q=%d n=%d err=%g", q, n, err);
  ex.run(root, X.data(), Y.data(), 1, Mode::Inverse);
  double err2 = 0;
  for (uint64_t i = 0; i < M; ++i) err2 = std::max(err2, std::abs(A::to_double(X[i]) - A::to_double(f[i])));
  CHECK(err2 <= 1e-10, "float roundtrip q=%d n=%d err=%g", q, n, err2);
}

int main() {
  test_indexing(2, 7);
  test_indexing(3, 5);
  test_indexing(4, 4);
  test_indexing(5, 4);
  test_exact(2, 6);
  test_exact(3, 4);
  test_exact(4, 3);
  test_exact(5, 3);
  test_batched(2, 5);
  test_batched(3, 4);
  test_float<RealArith>(2, 7);
  test_float<RealArith>(4, 4);
  test_float<ComplexArith>(3, 5);
  test_float<ComplexArith>(5, 4);
  // larger fields: exact where the test prime has p-th roots of unity (p = 2, 3)
  test_indexing(7, 3);
  test_indexing(8, 4);
  test_indexing(9, 3);
  test_indexing(16, 3);
  test_exact(8, 4);
  test_exact(9, 3);
  test_exact(16, 3);
  test_float<RealArith>(8, 4);
  test_float<RealArith>(16, 3);
  test_float<ComplexArith>(7, 3);
  test_float<ComplexArith>(9, 3);
  test_float<ComplexArith>(11, 3);
  test_float<ComplexArith>(13, 3);
#if FSC_COORD_BITS >= 5
  test_indexing(32, 4);
  test_exact(32, 3);
  test_float<RealArith>(32, 3);
  test_float<RealArith>(32, 4);
#endif
  std::printf("%d checks, %d failures\n", checks, failures);
  return failures ? 1 : 0;
}
