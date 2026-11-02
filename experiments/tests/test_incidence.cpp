// Exact checks of the incidence transform (Algorithm 2) against direct summation.
#include <cstdio>
#include <random>

#include "fsc/incidence.hpp"
#include "fsc/naive.hpp"

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

static void test_exact(int q, int nmax) {
  GF F(q);
  Space S(F);
  ModArith ar(F.p);
  std::mt19937_64 rng(77 + q);
  for (int n = 0; n <= nmax; ++n) {
    IncPlanner P(S);
    for (int a = 0; a <= n; ++a)
      for (int b = a; b <= n; ++b) {
        IncNode* nd = P.get(n, a, b);
        for (size_t beta : {size_t(1), size_t(2)}) {
          std::vector<uint64_t> f(nd->Nin * beta), z(nd->Nout * beta), want(nd->Nout * beta, 0);
          for (auto& v : f) v = rng() % ModArith::P;
          CSR C = build_incidence_csr(S, n, a, b);
          for (uint64_t w = 0; w < nd->Nout; ++w)
            for (uint64_t t = C.ptr[w]; t < C.ptr[w + 1]; ++t)
              for (size_t s = 0; s < beta; ++s)
                want[w * beta + s] = (want[w * beta + s] + f[C.idx[t] * beta + s]) % ModArith::P;
          Arena<uint64_t> arena(arena_need(nd, beta) + 1);
          IncExec<ModArith> ex{ar, q, F.e};
          std::vector<uint64_t> f0 = f;
          ex.run(nd, f.data(), z.data(), beta, arena);
          CHECK(z == want, "incidence q=%d n=%d a=%d b=%d beta=%zu", q, n, a, b, beta);
          CHECK(f == f0, "input modified q=%d n=%d a=%d b=%d", q, n, a, b);
          CHECK(arena.top == 0, "arena not released");
        }
        // CSR row lengths: every b-space contains [b a]_q a-spaces
        CSR C = build_incidence_csr(S, n, a, b);
        CHECK(C.nnz() == S.G(n, b) * S.G(b, a), "incidence count q=%d n=%d a=%d b=%d", q, n, a, b);
      }
  }
}

template <class A>
static void test_float(int q, int n, int a, int b) {
  GF F(q);
  Space S(F);
  A ar(F.p);
  IncPlanner P(S);
  IncNode* nd = P.get(n, a, b);
  CSR C = build_incidence_csr(S, n, a, b);
  std::mt19937_64 rng(3);
  std::uniform_real_distribution<double> U(-1, 1);
  std::vector<typename A::T> f(nd->Nin), z(nd->Nout);
  std::vector<double> fr(nd->Nin), want(nd->Nout, 0.0);
  for (uint64_t i = 0; i < nd->Nin; ++i) { fr[i] = U(rng); f[i] = A::from_double(fr[i]); }
  for (uint64_t w = 0; w < nd->Nout; ++w)
    for (uint64_t t = C.ptr[w]; t < C.ptr[w + 1]; ++t) want[w] += fr[C.idx[t]];
  Arena<typename A::T> arena(arena_need(nd, 1) + 1);
  IncExec<A> ex{ar, q, F.e};
  ex.run(nd, f.data(), z.data(), 1, arena);
  double err = 0, sc = 1;
  for (uint64_t w = 0; w < nd->Nout; ++w) {
    err = std::max(err, std::abs(A::to_double(z[w]) - want[w]));
    sc = std::max(sc, std::abs(want[w]));
  }
  CHECK(err <= 1e-11 * sc, "float incidence q=%d n=%d a=%d b=%d err=%g", q, n, a, b, err);
}

int main() {
  test_exact(2, 6);
  test_exact(3, 4);
  test_exact(4, 4);
  test_exact(5, 3);
  test_float<RealArith>(2, 8, 2, 6);
  test_float<RealArith>(4, 5, 1, 4);
  test_float<ComplexArith>(3, 6, 2, 4);
  test_float<ComplexArith>(5, 4, 1, 3);
  test_exact(8, 4);
  test_exact(16, 3);
  test_float<RealArith>(8, 5, 2, 3);
  test_float<RealArith>(16, 4, 1, 3);
  test_float<ComplexArith>(7, 4, 1, 2);
  std::printf("%d checks, %d failures\n", checks, failures);
  return failures ? 1 : 0;
}
