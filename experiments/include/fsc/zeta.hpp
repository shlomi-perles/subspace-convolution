// Fast subspace zeta transform (Algorithm 1) and the covering-pair baseline.
//
// Data layout: a table T(n,k) in L layout (see grassmann.hpp), one "row" per
// subspace, each row a contiguous vector of `beta` coefficients (the batch).
// The q^{n-1}-1 nonzero-frequency subproblems of a node are ONE batched call:
// they share the plan of T(n-2,k-1), so plans have total size O(table) and the
// deep levels run on long contiguous rows.  Crossing rows are coset-major, so
// all Fourier transforms of one dimension form a single batched DFT.
//
// Memory: two buffers of the table size (ping-pong).  A node runs with data X
// and scratch Y; after the Fourier stage it gathers its crossing rows into Y
// (the child inputs) and lends its own crossing region to the children.
#pragma once

#include <algorithm>
#include <cstdint>
#include <map>
#include <memory>
#include <vector>

#include "arith.hpp"
#include "grassmann.hpp"
#include "hugevec.hpp"

#ifdef _OPENMP
#include <omp.h>
#endif

#ifdef FSC_PROFILE
#include <chrono>
namespace fsc { namespace prof {
inline double t[2][4];  // [beta>1][phase: 0 dft, 1 permute, 2 broadcast, 3 lattice]
struct Scope {
  int b, ph; std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
  Scope(size_t beta, int phase) : b(beta > 1), ph(phase) {}
  ~Scope() { t[b][ph] += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); }
};
}}
#define FSC_PROF(beta, phase) ::fsc::prof::Scope _fsc_scope_##phase(beta, phase)
#else
#define FSC_PROF(beta, phase)
#endif

namespace fsc {

// ---------------------------------------------------------------------------
// Covering-pair sweep (KKW16 / BHK+16 on this lattice): one addition per pair.
// Label of U < W (covering) = the pivot of W that is not a pivot of U; labels
// are processed in increasing order.  This is Stanley's EL-labelling of the
// (supersolvable) subspace lattice for the coordinate flag; every interval has
// a unique increasing chain and no chain repeats a label, so each label step
// can be applied in place.  Stored per label in CSR form by the upper element.
// ---------------------------------------------------------------------------
struct LatticePlan {
  int n = 0, k = 0;
  uint64_t M = 0;
  struct Label {
    hvec<uint32_t> W;    // upper elements having this label
    hvec<uint64_t> ptr;  // CSR offsets into U
    hvec<uint32_t> U;    // lower covers
  };
  std::vector<Label> lab;
  uint64_t pairs() const {
    uint64_t s = 0;
    for (auto& l : lab) s += l.U.size();
    return s;
  }
  uint64_t bytes() const {
    uint64_t b = 0;
    for (auto& l : lab) b += l.W.size() * 4 + l.ptr.size() * 8 + l.U.size() * 4;
    return b;
  }
};

// dmin >= 0 skips upper elements of dimension <= dmin: for inputs supported on
// dimensions >= dmin those pairs only move zeros (used for incidence).
inline std::unique_ptr<LatticePlan> build_lattice_plan(const Space& S, int n, int k, int dmin = -1) {
  auto L = std::make_unique<LatticePlan>();
  k = std::min(k, n);
  L->n = n;
  L->k = k;
  L->M = S.M(n, k);
  L->lab.assign(n, {});
  int nth = 1;
#ifdef _OPENMP
  nth = omp_get_max_threads();
#endif
  std::vector<std::vector<LatticePlan::Label>> part(nth, std::vector<LatticePlan::Label>(n));
  const uint64_t M = L->M;
#pragma omp parallel num_threads(nth)
  {
    int tid = 0;
#ifdef _OPENMP
    tid = omp_get_thread_num();
#endif
    auto& my = part[tid];
    for (auto& l : my) l.ptr.push_back(0);
    uint64_t lo = M * (uint64_t)tid / (uint64_t)nth, hi = M * (uint64_t)(tid + 1) / (uint64_t)nth;
    std::vector<uint32_t> tmp;
    for (uint64_t w = lo; w < hi; ++w) {
      Sub Wb = S.unrank_L(n, k, w);
      if (Wb.d <= dmin) continue;
      for (int i = 0; i < Wb.d; ++i) {
        int label = lead(Wb.r[i]);
        int extra = Wb.d - i - 1;
        uint64_t cnt = S.qpow[extra];
        tmp.clear();
        for (uint64_t c = 0; c < cnt; ++c) {
          Sub Ub;
          Ub.d = Wb.d - 1;
          for (int t = 0; t < i; ++t) Ub.r[t] = Wb.r[t];
          uint64_t cc = c;
          for (int t = i + 1; t < Wb.d; ++t) {
            int coef = int(cc % (uint64_t)S.q);
            cc /= (uint64_t)S.q;
            Ub.r[t - 1] = S.axpy(Wb.r[t], coef, Wb.r[i], n);
          }
          tmp.push_back((uint32_t)S.pos_L(n, k, Ub));
        }
        std::sort(tmp.begin(), tmp.end());
        auto& l = my[label];
        l.W.push_back((uint32_t)w);
        l.U.insert(l.U.end(), tmp.begin(), tmp.end());
        l.ptr.push_back(l.U.size());
      }
    }
  }
  for (int l = 0; l < n; ++l) {
    auto& dst = L->lab[l];
    dst.ptr.push_back(0);
    for (int t = 0; t < nth; ++t) {
      auto& src = part[t][l];
      uint64_t base = dst.U.size();
      dst.W.insert(dst.W.end(), src.W.begin(), src.W.end());
      dst.U.insert(dst.U.end(), src.U.begin(), src.U.end());
      for (size_t i = 1; i < src.ptr.size(); ++i) dst.ptr.push_back(base + src.ptr[i]);
      src = {};
    }
  }
  return L;
}

template <class A>
void lattice_apply(const LatticePlan& L, typename A::T* x, size_t beta, bool inverse, bool transpose) {
  using T = typename A::T;
  const int n = L.n;
  // forward: labels ascending, x[W] += x[U]; inverse: descending, x[W] -= x[U]
  // transpose: descending, x[U] += x[W]; transpose-inverse: ascending, x[U] -= x[W]
  const bool ascending = (inverse == transpose);
  for (int s = 0; s < n; ++s) {
    const auto& lb = L.lab[ascending ? s : n - 1 - s];
    const uint32_t* Wp = lb.W.data();
    const uint64_t* ptr = lb.ptr.data();
    const uint32_t* Up = lb.U.data();
    const size_t nw = lb.W.size();
    if (beta == 1 && !transpose) {
      for (size_t i = 0; i < nw; ++i) {
        T acc = x[Up[ptr[i]]];
        for (uint64_t t = ptr[i] + 1; t < ptr[i + 1]; ++t) A::add_to(&acc, x + Up[t], 1);
        inverse ? A::sub_from(x + Wp[i], &acc, 1) : A::add_to(x + Wp[i], &acc, 1);
      }
    } else {
      for (size_t i = 0; i < nw; ++i) {
        T* w = x + (size_t)Wp[i] * beta;
        for (uint64_t t = ptr[i]; t < ptr[i + 1]; ++t) {
          T* u = x + (size_t)Up[t] * beta;
          if (!transpose) inverse ? A::sub_from(w, u, beta) : A::add_to(w, u, beta);
          else inverse ? A::sub_from(u, w, beta) : A::add_to(u, w, beta);
        }
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Plan of one hyperplane-cut node (n,k).
// ---------------------------------------------------------------------------
struct ZetaNode {
  int n = 0, k = 0, q = 0, e = 1;
  bool trivial = true;
  uint64_t M = 0, Min = 0, S0 = 0, S1 = 0, nfun = 0;
  // Odd q: the nonzero-frequency children are stored as two tables A, B with
  // batch nfun/2 each, B holding -lambda for the lambda in A.  For real input
  // only A is solved (B = conj(A)).
  bool halves = false;
  uint64_t nhalf = 0;
  std::vector<int> m;               // m[d] = n - d (d = 1..k)
  std::vector<uint64_t> nblocks;    // nblocks[d] = [n-1, d-1]
  std::vector<uint64_t> cross_off;  // row offset of dim-d crossing rows within crossing region
  std::vector<uint64_t> emb_off;    // offset of dim-d directions in emb
  hvec<uint32_t> dest;              // crossing row -> child buffer row
  hvec<uint32_t> src;               // child buffer row -> crossing row (inverse of dest)
  hvec<uint32_t> emb;               // direction (d,j) -> inside row of D_j
  ZetaNode *inside = nullptr, *child0 = nullptr, *child1 = nullptr;
  // hybrid base case
  bool use_lattice = false;
  std::unique_ptr<LatticePlan> lattice;
};

class ZetaPlanner {
 public:
  explicit ZetaPlanner(const Space& S) : S_(S) {}

  ZetaNode* get(int n, int k) {
    if (n > kMaxDim) throw std::invalid_argument("ambient dimension above kMaxDim");
    k = std::min(k, std::max(n, 0));
    auto key = std::make_pair(n, k);
    auto it = cache_.find(key);
    if (it != cache_.end()) return it->second.get();
    auto node = std::make_unique<ZetaNode>();
    ZetaNode* raw = node.get();
    cache_[key] = std::move(node);
    build(raw, n, k);
    return raw;
  }

  // Hybrid: nodes with n <= threshold run the covering sweep (batched).
  void set_lattice_threshold(int nmax_lattice) {
    set_lattice_rule([&](int n, int) { return n <= nmax_lattice; });
  }
  template <class Pred>
  void set_lattice_rule(Pred pred) {
    for (auto& [key, node] : cache_) {
      bool want = !node->trivial && pred(node->n, node->k);
      node->use_lattice = want;
      if (want && !node->lattice) node->lattice = build_lattice_plan(S_, node->n, node->k);
    }
  }
  uint64_t plan_bytes() const {
    uint64_t b = 0;
    for (auto& [key, node] : cache_) {
      b += (node->dest.size() + node->src.size() + node->emb.size()) * 4;
      if (node->lattice) b += node->lattice->bytes();
    }
    return b;
  }
  const std::map<std::pair<int, int>, std::unique_ptr<ZetaNode>>& nodes() const { return cache_; }
  const Space& space() const { return S_; }

 private:
  void build(ZetaNode* nd, int n, int k) {
    const Space& S = S_;
    nd->n = n;
    nd->k = k;
    nd->q = S.q;
    nd->e = S.F.e;
    nd->M = S.M(n, k);
    nd->trivial = (n <= 0 || k <= 0);
    if (nd->trivial) return;
    int kin = std::min(k, n - 1);
    nd->Min = S.M(n - 1, kin);
    nd->S0 = S.M(n - 1, k - 1);
    nd->S1 = (n >= 2) ? S.M(n - 2, k - 1) : 0;
    nd->nfun = S.qpow[n - 1] - 1;
    nd->halves = (S.q % 2 == 1) && nd->nfun > 0;
    nd->nhalf = nd->nfun / 2;
    nd->m.assign(k + 1, 0);
    nd->nblocks.assign(k + 1, 0);
    nd->cross_off.assign(k + 2, 0);
    nd->emb_off.assign(k + 2, 0);
    for (int d = 1; d <= k; ++d) {
      nd->m[d] = n - d;
      nd->nblocks[d] = S.G(n - 1, d - 1);
      nd->cross_off[d + 1] = nd->cross_off[d] + nd->nblocks[d] * S.qpow[n - d];
      nd->emb_off[d + 1] = nd->emb_off[d] + nd->nblocks[d];
    }
    const uint64_t C = nd->M - nd->Min;
    if (C != nd->cross_off[k + 1]) throw std::logic_error("crossing size mismatch");
    if (C >= (uint64_t(1) << 32)) throw std::length_error("table too large for 32-bit plan");
    nd->dest.assign(C, 0);
    nd->src.assign(C, 0);
    nd->emb.assign(nd->emb_off[k + 1], 0);
    for (int d = 1; d <= k; ++d) {
      const uint64_t bs = S.qpow[n - d];
      const uint64_t nb = nd->nblocks[d];
      const uint64_t roff = nd->cross_off[d];
      const uint64_t eoff = nd->emb_off[d];
      const uint64_t S0 = nd->S0, nfun = nd->nfun, S1 = nd->S1, nhalf = nd->nhalf;
      const bool halves = nd->halves;
#pragma omp parallel for schedule(dynamic, 64)
      for (int64_t jj = 0; jj < (int64_t)nb; ++jj) {
        uint64_t j = (uint64_t)jj;
        Sub B = S.unrank_gr(n - 1, d - 1, j);
        nd->emb[eoff + j] = (uint32_t)S.pos_L(n - 1, kin, B);
        nd->dest[roff + j] = (uint32_t)S.pos_L(n - 1, k - 1, B);  // c = 0: lambda = 0
        for (uint64_t li = 1; li < bs; ++li) {
          Vec lam = S.functional(B, n - 1, li);
          Sub Bp = S.restrict_to_kernel(B, lam);
          uint64_t pos1 = S.pos_L(n - 2, k - 1, Bp);
          uint64_t t;
          if (!halves) {
            t = S0 + pos1 * nfun + S.functional_index(lam, n - 1);
          } else {
            int half = 0;
            uint64_t cls = S.functional_class(lam, n - 1, half);
            t = S0 + (uint64_t)half * S1 * nhalf + pos1 * nhalf + cls;
          }
          nd->dest[roff + li * nb + j] = (uint32_t)t;
        }
      }
    }
    for (uint64_t r = 0; r < C; ++r) nd->src[nd->dest[r]] = (uint32_t)r;
    nd->inside = get(n - 1, kin);
    nd->child0 = get(n - 1, k - 1);
    nd->child1 = (n >= 2 && nd->nfun > 0) ? get(n - 2, k - 1) : nullptr;
  }

  const Space& S_;
  std::map<std::pair<int, int>, std::unique_ptr<ZetaNode>> cache_;
};

// ---------------------------------------------------------------------------
// Executors.  X: node data (nd->M rows of beta), Y: scratch with >= nd->M rows.
// ---------------------------------------------------------------------------
enum class Mode { Forward, Inverse, Transpose, TransposeInverse };

template <class A>
struct ZetaExec {
  using T = typename A::T;
  const A& ar;
  int q, e;

  static void permute_rows(T* dst, const T* srcbuf, const uint32_t* idx, size_t C, size_t beta) {
    if (beta == 1) {
      constexpr size_t kAhead = 64;  // software prefetch distance for the random reads
      size_t r = 0;
      for (; r + kAhead < C; ++r) {
        __builtin_prefetch(srcbuf + idx[r + kAhead]);
        dst[r] = srcbuf[idx[r]];
      }
      for (; r < C; ++r) dst[r] = srcbuf[idx[r]];
    } else {
      for (size_t r = 0; r < C; ++r) std::memcpy(dst + r * beta, srcbuf + (size_t)idx[r] * beta, beta * sizeof(T));
    }
  }
  uint64_t ipow(int m) const {
    uint64_t r = 1;
    for (int i = 0; i < m; ++i) r *= (uint64_t)q;
    return r;
  }
  // One batched DFT per dimension: q^m rows of length nblocks*beta.
  void dft_all(const ZetaNode* nd, T* Xc, size_t beta, int sign) const {
    FSC_PROF(beta, 0);
    for (int d = 1; d <= nd->k; ++d)
      ar.dft(Xc + nd->cross_off[d] * beta, nd->m[d] * e, nd->nblocks[d] * beta, sign);
  }
  // tmp[j] = inside row of D_j, for all directions of dimension d.
  void gather_inside(const ZetaNode* nd, int d, const T* X, T* tmp, size_t beta) const {
    const uint32_t* em = nd->emb.data() + nd->emb_off[d];
    const uint64_t nb = nd->nblocks[d];
    if (beta == 1) for (uint64_t j = 0; j < nb; ++j) tmp[j] = X[em[j]];
    else for (uint64_t j = 0; j < nb; ++j) std::memcpy(tmp + j * beta, X + (size_t)em[j] * beta, beta * sizeof(T));
  }
  void scatter_inside(const ZetaNode* nd, int d, T* X, const T* tmp, size_t beta, bool subtract) const {
    const uint32_t* em = nd->emb.data() + nd->emb_off[d];
    const uint64_t nb = nd->nblocks[d];
    for (uint64_t j = 0; j < nb; ++j) {
      if (subtract) A::sub_from(X + (size_t)em[j] * beta, tmp + j * beta, beta);
      else A::add_to(X + (size_t)em[j] * beta, tmp + j * beta, beta);
    }
  }

  void children(const ZetaNode* nd, T* Xc, T* Y, size_t beta, Mode mode, bool real) const {
    const size_t C = nd->dest.size();
    const bool conj_half = real && A::kHasConj && nd->halves;
    {
      FSC_PROF(beta, 1);
      // child row t <- crossing row src[t]; with conj_half the B table is not needed
      const size_t Cin = conj_half ? nd->S0 + nd->S1 * nd->nhalf : C;
      permute_rows(Y, Xc, nd->src.data(), Cin, beta);
    }
    if (nd->child0) run(nd->child0, Y, Xc, beta, mode, real);
    if (nd->child1) {
      T* tabA = Y + nd->S0 * beta;
      if (!nd->halves) {
        run(nd->child1, tabA, Xc, beta * nd->nfun, mode, false);
      } else {
        const size_t hb = beta * nd->nhalf;
        T* tabB = tabA + nd->S1 * hb;
        run(nd->child1, tabA, Xc, hb, mode, false);
        if (conj_half) A::conj_copy(tabB, tabA, nd->S1 * hb);  // frequency -lambda
        else run(nd->child1, tabB, Xc, hb, mode, false);
      }
    }
    FSC_PROF(beta, 1);
    permute_rows(Xc, Y, nd->dest.data(), C, beta);  // crossing row r <- child row dest[r]
  }

  // `real`: the input rows are real (imaginary parts zero); then frequency
  // -lambda is the conjugate of frequency lambda and only half is computed.
  void run(const ZetaNode* nd, T* X, T* Y, size_t beta, Mode mode, bool real = false) const {
    if (nd->trivial) return;
    if (nd->use_lattice) {
      FSC_PROF(beta, 3);
      lattice_apply<A>(*nd->lattice, X, beta, mode == Mode::Inverse || mode == Mode::TransposeInverse,
                       mode == Mode::Transpose || mode == Mode::TransposeInverse);
      return;
    }
    T* Xc = X + nd->Min * beta;
    const bool tr = (mode == Mode::Transpose || mode == Mode::TransposeInverse);
    const bool inv = (mode == Mode::Inverse || mode == Mode::TransposeInverse);

    if (!tr) {
      if (inv) {  // subtract the given inside cumulative value g0(D) from every coset of D
        for (int d = 1; d <= nd->k; ++d) {
          const size_t row = nd->nblocks[d] * beta;
          gather_inside(nd, d, X, Y, beta);
          T* base = Xc + nd->cross_off[d] * beta;
          for (uint64_t c = 0, len = ipow(nd->m[d]); c < len; ++c) A::sub_from(base + c * row, Y, row);
        }
      }
      run(nd->inside, X, Y, beta, mode, real);
      dft_all(nd, Xc, beta, +1);
      children(nd, Xc, Y, beta, mode, real);
      FSC_PROF(beta, 2);
      for (int d = 1; d <= nd->k; ++d) {
        const size_t row = nd->nblocks[d] * beta;
        T* base = Xc + nd->cross_off[d] * beta;
        ar.dft(base, nd->m[d] * e, row, -1);
        auto sc = inv_qpow(ar, q, nd->m[d]);
        const uint64_t len = ipow(nd->m[d]);
        if (!inv) {
          gather_inside(nd, d, X, Y, beta);
          for (uint64_t c = 0; c < len; ++c) A::scale_add(base + c * row, sc, Y, row);
        } else {
          for (uint64_t c = 0; c < len; ++c) A::scale(base + c * row, sc, row);
        }
      }
    } else {
      if (!inv) {  // transpose of the broadcast: inside rows collect their cosets
        for (int d = 1; d <= nd->k; ++d) {
          const size_t row = nd->nblocks[d] * beta;
          T* base = Xc + nd->cross_off[d] * beta;
          std::memcpy(Y, base, row * sizeof(T));
          for (uint64_t c = 1, len = ipow(nd->m[d]); c < len; ++c) A::add_to(Y, base + c * row, row);
          scatter_inside(nd, d, X, Y, beta, false);
        }
      }
      for (int d = 1; d <= nd->k; ++d) {
        const size_t row = nd->nblocks[d] * beta;
        T* base = Xc + nd->cross_off[d] * beta;
        ar.dft(base, nd->m[d] * e, row, -1);
        auto sc = inv_qpow(ar, q, nd->m[d]);
        for (uint64_t c = 0, len = ipow(nd->m[d]); c < len; ++c) A::scale(base + c * row, sc, row);
      }
      children(nd, Xc, Y, beta, mode, real);
      dft_all(nd, Xc, beta, +1);
      run(nd->inside, X, Y, beta, mode, real);
      if (inv) {  // transpose of the inverse broadcast, with the final crossing values
        for (int d = 1; d <= nd->k; ++d) {
          const size_t row = nd->nblocks[d] * beta;
          T* base = Xc + nd->cross_off[d] * beta;
          std::memcpy(Y, base, row * sizeof(T));
          for (uint64_t c = 1, len = ipow(nd->m[d]); c < len; ++c) A::add_to(Y, base + c * row, row);
          scatter_inside(nd, d, X, Y, beta, true);
        }
      }
    }
  }
};

// ---------------------------------------------------------------------------
// Exact floating-point operation counts of the executor (per batch element).
// ---------------------------------------------------------------------------
template <class A>
double zeta_flops(const ZetaNode* nd, const A& ar, double beta, double lattice_add_flops, bool real = false) {
  if (!nd || nd->trivial) return 0;
  if (nd->use_lattice) return beta * lattice_add_flops * (double)nd->lattice->pairs();
  double f = zeta_flops(nd->inside, ar, beta, lattice_add_flops, real);
  double local = 0;
  for (int d = 1; d <= nd->k; ++d) {
    double len = std::pow((double)nd->q, nd->m[d]);
    double per_block = 2 * ar.dft_flops(nd->m[d] * nd->e) + 2 * len * ar.value_flops();
    local += (double)nd->nblocks[d] * per_block;
  }
  f += beta * local;
  f += zeta_flops(nd->child0, ar, beta, lattice_add_flops, real);
  const bool conj_half = real && A::kHasConj && nd->halves;
  f += zeta_flops(nd->child1, ar, beta * (double)(conj_half ? nd->nhalf : nd->nfun), lattice_add_flops);
  return f;
}

}  // namespace fsc
