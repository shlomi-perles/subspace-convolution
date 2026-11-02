// Incidence between two dimensions (Algorithm 2 / Theorem 2):
//   (I_n^{a,b} f)(W) = sum_{U <= W, dim U = a} f(U),  f on Gr(n,a), W in Gr(n,b).
//
// Tables are single Grassmannians in the coset-major recursive order of
// grassmann.hpp.  A node (n,a,b) has four children: (n-1,a,b) and (n-1,a,b-1)
// on the inside input, (n-1,a-1,b-1) at frequency zero, and (n-2,a-1,b-1)
// batched over the q^{n-1}-1 nonzero functionals.  The executor does not modify
// its input; temporaries come from a stack arena sized by arena_need().
#pragma once

#include <algorithm>
#include <map>
#include <memory>
#include <tuple>
#include <vector>

#include "arith.hpp"
#include "grassmann.hpp"
#include "hugevec.hpp"

namespace fsc {

struct IncNode {
  enum Kind { Identity, Broadcast, Total, Split } kind = Identity;
  int n = 0, a = 0, b = 0, q = 0, e = 1;
  uint64_t Nin = 0, Nout = 0;            // |Gr(n,a)|, |Gr(n,b)|
  uint64_t in_inside = 0, out_inside = 0;  // |Gr(n-1,a)|, |Gr(n-1,b)|
  uint64_t S0in = 0, S0out = 0;          // |Gr(n-1,a-1)|, |Gr(n-1,b-1)|
  uint64_t nfun = 0;
  int m_in = 0, m_out = 0;               // n-a, n-b
  hvec<uint32_t> in_src;                 // child-input row  <- crossing input row
  hvec<uint32_t> out_dest;               // crossing output row <- child-output row
  IncNode *c_ab = nullptr, *c_ab1 = nullptr, *c0 = nullptr, *c1 = nullptr;
  uint64_t cross_in() const { return Nin - in_inside; }
  uint64_t cross_out() const { return Nout - out_inside; }
};

class IncPlanner {
 public:
  explicit IncPlanner(const Space& S) : S_(S) {}
  IncNode* get(int n, int a, int b) {
    if (n > kMaxDim) throw std::invalid_argument("ambient dimension above kMaxDim");
    auto key = std::make_tuple(n, a, b);
    auto it = cache_.find(key);
    if (it != cache_.end()) return it->second.get();
    auto node = std::make_unique<IncNode>();
    IncNode* raw = node.get();
    cache_[key] = std::move(node);
    build(raw, n, a, b);
    return raw;
  }
  uint64_t plan_bytes() const {
    uint64_t s = 0;
    for (auto& [k, nd] : cache_) s += (nd->in_src.size() + nd->out_dest.size()) * 4;
    return s;
  }
  size_t node_count() const { return cache_.size(); }

 private:
  void build(IncNode* nd, int n, int a, int b) {
    const Space& S = S_;
    if (a < 0 || b < a || b > n) throw std::invalid_argument("need 0 <= a <= b <= n");
    nd->n = n; nd->a = a; nd->b = b; nd->q = S.q; nd->e = S.F.e;
    nd->Nin = S.G(n, a);
    nd->Nout = S.G(n, b);
    if (a == b) { nd->kind = IncNode::Identity; return; }
    if (a == 0) { nd->kind = IncNode::Broadcast; return; }
    if (b == n) { nd->kind = IncNode::Total; return; }
    nd->kind = IncNode::Split;
    nd->in_inside = S.G(n - 1, a);
    nd->out_inside = S.G(n - 1, b);
    nd->S0in = S.G(n - 1, a - 1);
    nd->S0out = S.G(n - 1, b - 1);
    nd->nfun = S.qpow[n - 1] - 1;
    nd->m_in = n - a;
    nd->m_out = n - b;
    nd->in_src.assign(nd->cross_in(), 0);
    nd->out_dest.assign(nd->cross_out(), 0);
    const uint64_t nfun = nd->nfun;
    // input side: crossing row r = c*S0in + j  ->  child row t
    {
      const uint64_t nb = nd->S0in, len = S.qpow[nd->m_in];
#pragma omp parallel for schedule(dynamic, 64)
      for (int64_t jj = 0; jj < (int64_t)nb; ++jj) {
        uint64_t j = (uint64_t)jj;
        Sub B = S.unrank_gr(n - 1, a - 1, j);
        nd->in_src[j] = (uint32_t)j;
        for (uint64_t li = 1; li < len; ++li) {
          Vec lam = S.functional(B, n - 1, li);
          uint64_t t = nb + S.rank_gr(n - 2, S.restrict_to_kernel(B, lam)) * nfun + S.functional_index(lam, n - 1);
          nd->in_src[t] = (uint32_t)(li * nb + j);
        }
      }
    }
    // output side: crossing row r = c*S0out + j  <-  child row
    {
      const uint64_t nb = nd->S0out, len = S.qpow[nd->m_out];
#pragma omp parallel for schedule(dynamic, 64)
      for (int64_t jj = 0; jj < (int64_t)nb; ++jj) {
        uint64_t j = (uint64_t)jj;
        Sub D = S.unrank_gr(n - 1, b - 1, j);
        nd->out_dest[j] = (uint32_t)j;
        for (uint64_t li = 1; li < len; ++li) {
          Vec mu = S.functional(D, n - 1, li);
          nd->out_dest[li * nb + j] =
              (uint32_t)(nb + S.rank_gr(n - 2, S.restrict_to_kernel(D, mu)) * nfun + S.functional_index(mu, n - 1));
        }
      }
    }
    nd->c_ab = get(n - 1, a, b);
    nd->c_ab1 = get(n - 1, a, b - 1);
    nd->c0 = get(n - 1, a - 1, b - 1);
    nd->c1 = get(n - 2, a - 1, b - 1);
  }

  const Space& S_;
  std::map<std::tuple<int, int, int>, std::unique_ptr<IncNode>> cache_;
};

// Stack arena for temporaries (values of type T).
template <class T>
struct Arena {
  hvec<T> buf;
  size_t top = 0;
  explicit Arena(size_t cap) : buf(cap) {}
  T* push(size_t n) {
    if (top + n > buf.size()) throw std::length_error("arena exhausted");
    T* p = buf.data() + top;
    top += n;
    return p;
  }
};

inline uint64_t arena_need(const IncNode* nd, uint64_t beta) {
  if (nd->kind != IncNode::Split) return 0;
  const uint64_t ci = nd->cross_in() * beta, co = nd->cross_out() * beta;
  uint64_t inner = std::max(arena_need(nd->c0, beta), arena_need(nd->c1, beta * nd->nfun));
  uint64_t after_R = std::max({arena_need(nd->c_ab1, beta), 2 * ci, ci + co + inner});
  return std::max(arena_need(nd->c_ab, beta), nd->S0out * beta + after_R);
}

template <class A>
struct IncExec {
  using T = typename A::T;
  const A& ar;
  int q, e;

  static void permute_rows(T* dst, const T* src, const uint32_t* idx, size_t C, size_t beta) {
    if (beta == 1) {
      for (size_t r = 0; r < C; ++r) dst[r] = src[idx[r]];
    } else {
      for (size_t r = 0; r < C; ++r) std::memcpy(dst + r * beta, src + (size_t)idx[r] * beta, beta * sizeof(T));
    }
  }

  void run(const IncNode* nd, const T* X, T* Z, size_t beta, Arena<T>& arena) const {
    switch (nd->kind) {
      case IncNode::Identity:
        std::memcpy(Z, X, nd->Nin * beta * sizeof(T));
        return;
      case IncNode::Broadcast:
        for (uint64_t w = 0; w < nd->Nout; ++w) std::memcpy(Z + w * beta, X, beta * sizeof(T));
        return;
      case IncNode::Total:
        std::memcpy(Z, X, beta * sizeof(T));
        for (uint64_t r = 1; r < nd->Nin; ++r) A::add_to(Z, X + r * beta, beta);
        return;
      case IncNode::Split:
        break;
    }
    const size_t mark = arena.top;
    run(nd->c_ab, X, Z, beta, arena);  // inside outputs
    T* R = arena.push(nd->S0out * beta);
    run(nd->c_ab1, X, R, beta, arena);  // r(D) for the crossing outputs
    const uint64_t ci = nd->cross_in(), co = nd->cross_out();
    T* CI = arena.push(ci * beta);
    {
      const size_t m2 = arena.top;
      T* W = arena.push(ci * beta);
      std::memcpy(W, X + nd->in_inside * beta, ci * beta * sizeof(T));
      ar.dft(W, nd->m_in * e, nd->S0in * beta, +1);
      permute_rows(CI, W, nd->in_src.data(), ci, beta);
      arena.top = m2;
    }
    T* CO = arena.push(co * beta);
    run(nd->c0, CI, CO, beta, arena);
    run(nd->c1, CI + nd->S0in * beta, CO + nd->S0out * beta, beta * nd->nfun, arena);
    T* Zc = Z + nd->out_inside * beta;
    permute_rows(Zc, CO, nd->out_dest.data(), co, beta);
    const size_t row = nd->S0out * beta;
    ar.dft(Zc, nd->m_out * e, row, -1);
    auto sc = inv_qpow(ar, q, nd->m_out);
    uint64_t len = 1;
    for (int i = 0; i < nd->m_out; ++i) len *= (uint64_t)q;
    for (uint64_t c = 0; c < len; ++c) A::scale_add(Zc + c * row, sc, R, row);
    arena.top = mark;
  }
};

// Floating-point operations of the executor (per batch element).
template <class A>
double inc_flops(const IncNode* nd, const A& ar, double beta) {
  switch (nd->kind) {
    case IncNode::Identity:
    case IncNode::Broadcast:
      return 0;
    case IncNode::Total:
      return beta * double(nd->Nin - 1) * A::value_flops();
    case IncNode::Split:
      break;
  }
  double f = inc_flops(nd->c_ab, ar, beta) + inc_flops(nd->c_ab1, ar, beta) + inc_flops(nd->c0, ar, beta) +
             inc_flops(nd->c1, ar, beta * (double)nd->nfun);
  double local = (double)nd->S0in * ar.dft_flops(nd->m_in * nd->e) +
                 (double)nd->S0out * ar.dft_flops(nd->m_out * nd->e) + 2.0 * (double)nd->cross_out() * A::value_flops();
  return f + beta * local;
}

}  // namespace fsc
