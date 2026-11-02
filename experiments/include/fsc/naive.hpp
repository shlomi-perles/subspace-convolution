// Direct summation baselines: explicit lists of comparable / incident pairs.
#pragma once

#include <cstdint>
#include <vector>

#include "grassmann.hpp"
#include "hugevec.hpp"

#ifdef _OPENMP
#include <omp.h>
#endif

namespace fsc {

// The subspace of F_q^n spanned by coefficient rows `C` (in F_q^dW) times basis W.
inline Sub combine(const Space& S, const Sub& C, const Sub& W, int n) {
  std::vector<Vec> rows;
  rows.reserve(C.d);
  for (int i = 0; i < C.d; ++i) {
    Vec v = 0;
    for (int t = 0; t < W.d; ++t) v = S.axpy(v, get(C.r[i], t), W.r[t], n);
    rows.push_back(v);
  }
  return S.echelon(rows, n);
}

// CSR over output rows: in[ptr[w] .. ptr[w+1]) lists input rows summed into w.
struct CSR {
  hvec<uint64_t> ptr;
  hvec<uint32_t> idx;
  uint64_t nnz() const { return idx.size(); }
};

// All U <= W (including U = W) in T(n,k), L layout.
inline CSR build_containment_csr(const Space& S, int n, int k) {
  k = std::min(k, n);
  const uint64_t M = S.M(n, k);
  std::vector<std::vector<uint32_t>> per(M);
#pragma omp parallel for schedule(dynamic, 256)
  for (int64_t w = 0; w < (int64_t)M; ++w) {
    Sub W = S.unrank_L(n, k, (uint64_t)w);
    auto& out = per[(size_t)w];
    for (int j = 0; j <= W.d; ++j)
      for (uint64_t c = 0; c < S.G(W.d, j); ++c) {
        Sub C = S.unrank_gr(W.d, j, c);
        out.push_back((uint32_t)S.pos_L(n, k, combine(S, C, W, n)));
      }
  }
  CSR A;
  A.ptr.assign(M + 1, 0);
  for (uint64_t w = 0; w < M; ++w) A.ptr[w + 1] = A.ptr[w] + per[w].size();
  A.idx.reserve(A.ptr[M]);
  for (auto& v : per) A.idx.insert(A.idx.end(), v.begin(), v.end());
  return A;
}

// a-dimensional subspaces of each b-dimensional W (Gr orders).
inline CSR build_incidence_csr(const Space& S, int n, int a, int b) {
  const uint64_t Nb = S.G(n, b);
  std::vector<std::vector<uint32_t>> per(Nb);
#pragma omp parallel for schedule(dynamic, 256)
  for (int64_t w = 0; w < (int64_t)Nb; ++w) {
    Sub W = S.unrank_gr(n, b, (uint64_t)w);
    auto& out = per[(size_t)w];
    for (uint64_t c = 0; c < S.G(b, a); ++c) {
      Sub C = S.unrank_gr(b, a, c);
      out.push_back((uint32_t)S.rank_gr(n, combine(S, C, W, n)));
    }
  }
  CSR A;
  A.ptr.assign(Nb + 1, 0);
  for (uint64_t w = 0; w < Nb; ++w) A.ptr[w + 1] = A.ptr[w] + per[w].size();
  A.idx.reserve(A.ptr[Nb]);
  for (auto& v : per) A.idx.insert(A.idx.end(), v.begin(), v.end());
  return A;
}

// y[w] = sum_{u in row w} x[u]   (out-of-place; one addition per stored pair minus one per row)
template <class A>
void csr_apply(const CSR& C, const typename A::T* x, typename A::T* y) {
  const uint64_t rows = C.ptr.size() - 1;
  for (uint64_t w = 0; w < rows; ++w) {
    typename A::T acc{};
    const uint32_t* p = C.idx.data() + C.ptr[w];
    const uint64_t cnt = C.ptr[w + 1] - C.ptr[w];
    if (cnt) {
      acc = x[p[0]];
      for (uint64_t i = 1; i < cnt; ++i) A::add_to(&acc, x + p[i], 1);
    }
    y[w] = acc;
  }
}

}  // namespace fsc
