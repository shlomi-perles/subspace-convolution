// Applications on the Grassmannian Gr(n,k) (Theorem 3 / Algorithm 3).
//
// Intersection kernels K(U,W) = a_{d(U,W)}, d(U,W) = k - dim(U ∩ W), are applied
// with one upper and one lower truncated zeta transform on T(n,k); distance
// profiles D_i f(U) = sum_{d(U,W)=i} f(W) use k+1 lower transforms and a
// triangular back-substitution.  Baselines: the Grassmann graph's three-term
// recurrence with a sparse adjacency matrix, and direct pairwise distances.
#pragma once

#include <cmath>
#include <vector>

#include "hugevec.hpp"
#include "naive.hpp"
#include "zeta.hpp"

namespace fsc {

// Dimension of every row of T(n,k) in L layout.
inline void fill_dims(const Space& S, int n, int k, uint8_t* out) {
  k = std::min(k, n);
  if (n == 0 || k == 0) {
    for (uint64_t i = 0; i < S.M(n, k); ++i) out[i] = 0;
    return;
  }
  int kin = std::min(k, n - 1);
  fill_dims(S, n - 1, kin, out);
  uint64_t pos = S.M(n - 1, kin);
  for (int d = 1; d <= k; ++d) {
    uint64_t cnt = S.G(n - 1, d - 1) * S.qpow[n - d];
    for (uint64_t i = 0; i < cnt; ++i) out[pos + i] = (uint8_t)d;
    pos += cnt;
  }
}

// Exact rational/real helpers for the q-binomial triangular systems.
inline double qbinom_d(const Space& S, int n, int k) { return (double)S.G(n, k); }

// c_t with a_{k-t} = sum_{j<=t} [t j]_q c_j  (Eq. kernel-coefficients)
inline std::vector<double> kernel_coefficients(const Space& S, int k, const std::vector<double>& a) {
  std::vector<double> c(k + 1, 0.0);
  for (int t = 0; t <= k; ++t) {
    double v = (k - t) < (int)a.size() ? a[k - t] : 0.0;
    for (int j = 0; j < t; ++j) v -= qbinom_d(S, t, j) * c[j];
    c[t] = v;
  }
  return c;
}

template <class A>
class GrassmannOps {
 public:
  using T = typename A::T;
  GrassmannOps(const Space& S, int n, int k, const A& ar)
      : S_(S), n_(n), k_(k), ar_(ar), planner_(S), ex_{ar, S.q, S.F.e} {
    if (2 * k > n) throw std::invalid_argument("use k <= n/2 (dualize otherwise)");
    root_ = planner_.get(n, k);
    M_ = S.M(n, k);
    v_ = S.G(n, k);
    dims_.resize(M_);
    fill_dims(S, n, k, dims_.data());
    kpos_.reserve(v_);
    for (uint64_t i = 0; i < M_; ++i)
      if (dims_[i] == k) kpos_.push_back((uint32_t)i);
    X_.resize(M_);
    Y_.resize(M_);
  }
  uint64_t v() const { return v_; }
  uint64_t table_size() const { return M_; }
  ZetaPlanner& planner() { return planner_; }

  // y = K f with K(U,W) = a[d(U,W)]   (two transforms)
  void kernel_apply(const std::vector<double>& a, const double* f, double* y) {
    auto c = kernel_coefficients(S_, k_, a);
    std::fill(X_.begin(), X_.end(), A::from_double(0.0));
    for (uint64_t i = 0; i < v_; ++i) X_[kpos_[i]] = A::from_double(f[i]);
    ex_.run(root_, X_.data(), Y_.data(), 1, Mode::Transpose, true);  // H(L) = sum_{W >= L} f(W)
    for (uint64_t i = 0; i < M_; ++i) scale_one(X_[i], c[dims_[i]]);
    ex_.run(root_, X_.data(), Y_.data(), 1, Mode::Forward, true);
    for (uint64_t i = 0; i < v_; ++i) y[i] = A::to_double(X_[kpos_[i]]);
  }

  // prof[i][U] = sum_{W: d(U,W)=i} f(W), i = 0..k   (k+2 transforms).
  // Computes h_t = sum_{dim(U∩W)=t} f(W) for t = k..0, fusing the triangular
  // back-substitution h_t = m_t - sum_{r>t} [r t]_q h_r with the transform for
  // m_t, so only the k+1 output vectors are stored (Out may be float for counts).
  template <class Out>
  void distance_profiles(const double* f, std::vector<hvec<Out>>& prof) {
    const int k = k_;
    hvec<T> H(M_);
    std::fill(X_.begin(), X_.end(), A::from_double(0.0));
    for (uint64_t i = 0; i < v_; ++i) X_[kpos_[i]] = A::from_double(f[i]);
    ex_.run(root_, X_.data(), Y_.data(), 1, Mode::Transpose, true);  // H(L) = sum_{W >= L} f(W)
    H = X_;
    prof.assign(k + 1, hvec<Out>(v_));
    for (int t = k; t >= 0; --t) {
      for (uint64_t i = 0; i < M_; ++i) X_[i] = dims_[i] == t ? H[i] : A::from_double(0.0);
      ex_.run(root_, X_.data(), Y_.data(), 1, Mode::Forward, true);  // m_t
      hvec<Out>& out = prof[k - t];                                   // D_{k-t} = h_t
      for (uint64_t u = 0; u < v_; ++u) {
        double val = A::to_double(X_[kpos_[u]]);
        for (int r = t + 1; r <= k; ++r) val -= qbinom_d(S_, r, t) * (double)prof[k - r][u];
        out[u] = (Out)val;
      }
    }
  }

 private:
  static void scale_one(double& x, double s) { x *= s; }
  static void scale_one(Cplx& x, double s) { x.re *= s; x.im *= s; }

  const Space& S_;
  int n_, k_;
  const A& ar_;
  ZetaPlanner planner_;
  ZetaExec<A> ex_;
  ZetaNode* root_ = nullptr;
  uint64_t M_ = 0, v_ = 0;
  hvec<uint8_t> dims_;
  hvec<uint32_t> kpos_;
  hvec<T> X_, Y_;
};

// ---------------------------------------------------------------------------
// Baseline: Grassmann graph J_q(n,k), sparse adjacency + three-term recurrence.
// A D_i = b_{i-1} D_{i-1} + a_i D_i + c_{i+1} D_{i+1}, with
// b_i = q^{2i+1} [k-i][n-k-i], c_i = [i]^2, a_i = b_0 - b_i - c_i.
// ---------------------------------------------------------------------------
inline CSR build_grassmann_adjacency(const Space& S, int n, int k) {
  const uint64_t v = S.G(n, k);
  std::vector<std::vector<uint32_t>> nbr(v);
#pragma omp parallel for schedule(dynamic, 64)
  for (int64_t uu = 0; uu < (int64_t)v; ++uu) {
    Sub U = S.unrank_gr(n, k, (uint64_t)uu);
    auto& out = nbr[(size_t)uu];
    // hyperplanes Hp of U, then lines of F^n / Hp other than U/Hp
    for (uint64_t c = 0; c < S.G(k, k - 1); ++c) {
      Sub Cc = S.unrank_gr(k, k - 1, c);
      Sub Hp = combine(S, Cc, U, n);
      uint32_t pm = Hp.pivmask();
      std::vector<int> comp;  // complement coordinates (non-pivots of Hp)
      for (int t = 0; t < n; ++t)
        if (!(pm >> t & 1)) comp.push_back(t);
      const int m = (int)comp.size();  // n-k+1
      // normalized nonzero vectors in span(e_comp): leading (last) coefficient 1
      for (int top = 0; top < m; ++top)
        for (uint64_t lowc = 0; lowc < S.qpow[top]; ++lowc) {
          Vec w = unit(comp[top]);
          uint64_t x = lowc;
          for (int t = 0; t < top; ++t) {
            w = put(w, comp[t], int(x % (uint64_t)S.q));
            x /= (uint64_t)S.q;
          }
          std::vector<Vec> rows(Hp.r, Hp.r + Hp.d);
          rows.push_back(w);
          Sub W = S.echelon(rows, n);
          uint64_t idx = S.rank_gr(n, W);
          if (idx != (uint64_t)uu) out.push_back((uint32_t)idx);
        }
    }
    std::sort(out.begin(), out.end());
  }
  CSR A;
  A.ptr.assign(v + 1, 0);
  for (uint64_t u = 0; u < v; ++u) A.ptr[u + 1] = A.ptr[u] + nbr[u].size();
  A.idx.reserve(A.ptr[v]);
  for (auto& x : nbr) A.idx.insert(A.idx.end(), x.begin(), x.end());
  return A;
}

struct GrassmannGraphParams {
  std::vector<double> a, b, c;  // intersection numbers a_i, b_i, c_i
  int s;
};
inline GrassmannGraphParams grassmann_params(const Space& S, int n, int k) {
  GrassmannGraphParams P;
  P.s = std::min(k, n - k);
  P.a.assign(P.s + 2, 0);
  P.b.assign(P.s + 2, 0);
  P.c.assign(P.s + 2, 0);
  for (int i = 0; i <= P.s; ++i) {
    P.b[i] = std::pow((double)S.q, 2 * i + 1) * (double)S.G(k - i, 1) * (double)S.G(n - k - i, 1);
    P.c[i] = (double)S.G(i, 1) * (double)S.G(i, 1);
  }
  for (int i = 0; i <= P.s; ++i) P.a[i] = P.b[0] - P.b[i] - P.c[i];
  return P;
}

// prof[i] = D_i f by the three-term recurrence; apply(x, y) computes y = A x.
template <class ApplyA>
inline void recurrence_profiles(const Space& S, int n, int k, const double* f, std::vector<hvec<double>>& prof,
                                ApplyA&& apply) {
  auto P = grassmann_params(S, n, k);
  const uint64_t v = S.G(n, k);
  prof.assign(P.s + 1, hvec<double>(v, 0.0));
  for (uint64_t u = 0; u < v; ++u) prof[0][u] = f[u];
  hvec<double> Ad(v);
  for (int i = 0; i < P.s; ++i) {
    apply(prof[i].data(), Ad.data());  // A D_i f
    for (uint64_t u = 0; u < v; ++u) {
      double val = Ad[u] - P.a[i] * prof[i][u] - (i > 0 ? P.b[i - 1] * prof[i - 1][u] : 0.0);
      prof[i + 1][u] = val / P.c[i + 1];
    }
  }
}

// prof[i] = D_i f via s sparse matrix-vector products with the adjacency.
inline void graph_distance_profiles(const Space& S, int n, int k, const CSR& Adj, const double* f,
                                    std::vector<hvec<double>>& prof) {
  recurrence_profiles(S, n, k, f, prof,
                      [&](const double* x, double* y) { csr_apply<RealArith>(Adj, x, y); });
}

// The same recurrence with the adjacency factored through the (k-1)-subspaces,
// as in the isotypic projections of Maslen, Orrison and Rockmore:
// A = U D - [k]_q I, where D sums over the k-spaces containing a (k-1)-space and
// U over the (k-1)-subspaces of a k-space; both use the incidence lists
// Inc = build_incidence_csr(S, n, k-1, k), with v [k]_q entries.
inline void factored_distance_profiles(const Space& S, int n, int k, const CSR& Inc, const double* f,
                                       std::vector<hvec<double>>& prof) {
  const uint64_t v = S.G(n, k), w = S.G(n, k - 1);
  const double kq = (double)S.G(k, 1);
  hvec<double> low(w);
  recurrence_profiles(S, n, k, f, prof, [&](const double* x, double* y) {
    std::fill(low.begin(), low.end(), 0.0);
    for (uint64_t u = 0; u < v; ++u)  // D: scatter each k-space to its (k-1)-subspaces
      for (uint64_t t = Inc.ptr[u]; t < Inc.ptr[u + 1]; ++t) low[Inc.idx[t]] += x[u];
    for (uint64_t u = 0; u < v; ++u) {  // U: gather them back, then subtract [k]_q x
      double acc = 0;
      for (uint64_t t = Inc.ptr[u]; t < Inc.ptr[u + 1]; ++t) acc += low[Inc.idx[t]];
      y[u] = acc - kq * x[u];
    }
  });
}

}  // namespace fsc
