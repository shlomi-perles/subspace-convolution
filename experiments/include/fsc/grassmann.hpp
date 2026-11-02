// Subspaces of F_q^n: packed vectors, echelon bases, and the table orders.
//
// Same conventions as reference/fsc_ref/subspaces.py:
//  * coordinate i of a vector is the nibble at bits [4i, 4i+4);
//  * echelon bases are "rightmost-pivot" reduced: pivot = last nonzero
//    coordinate, rows sorted by increasing pivot, pivot columns are unit vectors;
//  * Gr(n,d) is ordered recursively: subspaces of H = {x_{n-1}=0} first, then
//    B + <(x,1)> ordered coset-major, by (coset index of x, index of B in
//    Gr(n-1,d-1)).  (The Python reference lists crossing subspaces B-major;
//    both are valid orders, each implementation is tested on its own.)
//  * the truncated table T(n,k) (all dims <= k) uses the "L layout":
//    L(n,k) = [L(n-1,k) | crossing rows], crossing rows ordered by dimension
//    d = 1..k, then by coset index c, then by the index j of B in Gr(n-1,d-1)
//    ("coset-major": the Fourier transforms of all blocks of one dimension
//    form a single batched DFT whose rows hold all directions B).
#pragma once

#include <cassert>
#include <cstdint>
#include <vector>

#include "gf.hpp"

namespace fsc {

using Vec = uint64_t;  // packed coordinates, kCoordBits bits each
// 4 bits per coordinate (q <= 16, n <= 16) unless built with -DFSC_COORD_BITS=5
// (q <= 32, n <= 12).
#ifndef FSC_COORD_BITS
#define FSC_COORD_BITS 4
#endif
constexpr int kCoordBits = FSC_COORD_BITS;
constexpr Vec kCoordMask = (Vec(1) << kCoordBits) - 1;
constexpr int kMaxDim = 64 / kCoordBits;  // planners reject larger ambient dimensions

inline int get(Vec v, int i) { return int((v >> (kCoordBits * i)) & kCoordMask); }
inline Vec put(Vec v, int i, int c) {
  return (v & ~(kCoordMask << (kCoordBits * i))) | (Vec(c) << (kCoordBits * i));
}
inline int lead(Vec v) { return v ? (63 - __builtin_clzll(v)) / kCoordBits : -1; }
inline int first_nonzero(Vec v) { return v ? __builtin_ctzll(v) / kCoordBits : -1; }
inline Vec unit(int i) { return Vec(1) << (kCoordBits * i); }
inline Vec delete_coord(Vec v, int j) {
  Vec low = j ? (v & (unit(j) - 1)) : 0;
  return low | ((v >> (kCoordBits * (j + 1))) << (kCoordBits * j));
}

struct Sub {
  int d = 0;
  Vec r[kMaxDim]{};  // rows sorted by increasing pivot
  uint32_t pivmask() const {
    uint32_t m = 0;
    for (int i = 0; i < d; ++i) m |= 1u << lead(r[i]);
    return m;
  }
};

struct Space {
  const GF& F;
  int q;
  std::vector<std::vector<uint64_t>> gauss;  // gauss[n][k] = [n choose k]_q
  std::vector<uint64_t> qpow;

  explicit Space(const GF& f, int nmax = kMaxDim) : F(f), q(f.q) {
    gauss.assign(nmax + 2, std::vector<uint64_t>(nmax + 2, 0));
    for (int n = 0; n <= nmax + 1; ++n) {
      gauss[n][0] = 1;
      for (int k = 1; k <= n; ++k) {
        uint64_t qp = 1;
        for (int i = 0; i < n - k; ++i) qp *= (uint64_t)q;
        gauss[n][k] = gauss[n - 1][k] + qp * gauss[n - 1][k - 1];  // [n k] = [n-1 k] + q^{n-k} [n-1 k-1]
      }
    }
    qpow.assign(64, 0);
    qpow[0] = 1;
    for (int i = 1; i < 64; ++i) qpow[i] = qpow[i - 1] * (uint64_t)q;
  }

  uint64_t G(int n, int k) const { return (k < 0 || n < 0 || k > n) ? 0 : gauss[n][k]; }
  uint64_t M(int n, int k) const {  // |T(n,k)|
    if (k < 0) return 0;
    uint64_t s = 0;
    for (int j = 0; j <= std::min(k, n); ++j) s += G(n, j);
    return s;
  }

  Vec axpy(Vec v, int c, Vec w, int n) const {  // v + c*w
    if (!c) return v;
    Vec out = 0;
    for (int i = 0; i < n; ++i) out |= Vec(F.add[get(v, i)][F.mul[c][get(w, i)]]) << (kCoordBits * i);
    return out;
  }

  // coset index of x (zero on pivots) w.r.t. pivot mask pm, ambient dimension m
  uint64_t coset_index(Vec x, uint32_t pm, int m) const {
    uint64_t idx = 0, w = 1;
    for (int t = 0; t < m; ++t)
      if (!(pm >> t & 1)) { idx += (uint64_t)get(x, t) * w; w *= (uint64_t)q; }
    return idx;
  }
  Vec coset_rep(uint64_t idx, uint32_t pm, int m) const {
    Vec x = 0;
    for (int t = 0; t < m; ++t)
      if (!(pm >> t & 1)) { x |= Vec(idx % (uint64_t)q) << (kCoordBits * t); idx /= (uint64_t)q; }
    return x;
  }

  // ---- Gr(n,d) recursive order -------------------------------------------
  uint64_t rank_gr(int n, const Sub& U) const {
    // crossing: rank = [n-1 d] + c * [n-1 d-1] + rank(B); inside: rank in Gr(n-1,d)
    uint64_t acc = 0;
    int d = U.d;
    while (d > 0) {
      Vec top = U.r[d - 1];
      if (lead(top) == n - 1) {
        uint32_t pm = 0;
        for (int i = 0; i < d - 1; ++i) pm |= 1u << lead(U.r[i]);
        Vec x = top & (unit(n - 1) - 1);
        acc += G(n - 1, d) + coset_index(x, pm, n - 1) * G(n - 1, d - 1);
        --d;
      }
      --n;  // the last coordinate is zero on the remaining rows
    }
    return acc;
  }

  Sub unrank_gr(int n, int d, uint64_t idx) const {
    // Descend top-down recording crossing levels, then fill coset representatives.
    int piv[kMaxDim];
    uint64_t code[kMaxDim];
    int dd = d, m = n, cnt = 0;
    while (dd > 0) {
      uint64_t ins = G(m - 1, dd);
      if (idx < ins) { --m; continue; }
      idx -= ins;
      uint64_t nb = G(m - 1, dd - 1);  // coset-major: idx = c * nb + j
      piv[cnt] = m - 1;
      code[cnt] = idx / nb;
      idx %= nb;
      ++cnt;
      --dd;
      --m;
    }
    Sub U;
    U.d = d;
    // rows by increasing pivot: cnt-1 ... 0
    uint32_t pm = 0;
    for (int t = cnt - 1; t >= 0; --t) {
      int row = cnt - 1 - t;
      Vec x = coset_rep(code[t], pm, piv[t]);
      U.r[row] = x | (unit(piv[t]));
      pm |= 1u << piv[t];
    }
    return U;
  }

  // ---- L layout of T(n,k) -------------------------------------------------
  // offset of the dim-d crossing rows inside the crossing region of L(n,k)
  uint64_t cross_off(int n, int d) const {
    uint64_t s = 0;
    for (int e = 1; e < d; ++e) s += G(n - 1, e - 1) * qpow[n - e];
    return s;
  }
  uint64_t pos_L(int n, int k, Sub U) const {
    int d = U.d;
    while (true) {
      if (d == 0) return 0;  // zero subspace is row 0 of every L(n,k)
      Vec top = U.r[d - 1];
      if (lead(top) == n - 1) {
        Sub B;
        B.d = d - 1;
        uint32_t pm = 0;
        for (int i = 0; i < d - 1; ++i) { B.r[i] = U.r[i]; pm |= 1u << lead(U.r[i]); }
        Vec x = top & (unit(n - 1) - 1);
        return M(n - 1, std::min(k, n - 1)) + cross_off(n, d) + coset_index(x, pm, n - 1) * G(n - 1, d - 1) +
               rank_gr(n - 1, B);
      }
      --n;
      k = std::min(k, n);
    }
  }
  // Echelon basis of the subspace at L-layout position idx of T(n,k).
  Sub unrank_L(int n, int k, uint64_t idx) const {
    k = std::min(k, n);
    while (n > 0) {
      uint64_t Min = M(n - 1, std::min(k, n - 1));
      if (idx < Min) { --n; k = std::min(k, n); continue; }
      idx -= Min;
      for (int d = 1; d <= k; ++d) {
        uint64_t nb = G(n - 1, d - 1), sz = nb * qpow[n - d];
        if (idx < sz) {  // coset-major: idx = c * nb + j
          Sub U = unrank_gr(n - 1, d - 1, idx % nb);
          Vec x = coset_rep(idx / nb, U.pivmask(), n - 1);
          U.r[U.d++] = x | (unit(n - 1));
          return U;
        }
        idx -= sz;
      }
      assert(false);
    }
    return Sub{};
  }

  // ---- helpers for the Fourier regrouping ----------------------------------
  // lambda in B° (ambient m) from dual-coded digits on the non-pivots of B.
  Vec functional(const Sub& B, int m, uint64_t dual_idx) const {
    uint32_t pm = B.pivmask();
    Vec lam = 0;
    for (int t = 0; t < m; ++t)
      if (!(pm >> t & 1)) {
        lam |= Vec(F.dual_to_elem[dual_idx % (uint64_t)q]) << (kCoordBits * t);
        dual_idx /= (uint64_t)q;
      }
    for (int i = 0; i < B.d; ++i) {
      int s = 0;
      Vec r = B.r[i];
      for (int t = 0; t < m; ++t)
        if (!(pm >> t & 1)) s = F.add[s][F.mul[get(lam, t)][get(r, t)]];
      lam = put(lam, lead(r), F.neg[s]);
    }
    return lam;
  }
  uint64_t functional_index(Vec lam, int m) const {  // nonzero lam -> 0..q^m-2
    uint64_t idx = 0;
    for (int t = m - 1; t >= 0; --t) idx = idx * (uint64_t)q + (uint64_t)get(lam, t);
    return idx - 1;
  }
  // Odd q only: index of the pair {lambda, -lambda} in [0, (q^m-1)/2) and the
  // member (half = 0 or 1).  lambda = v * mu with mu normalized (first nonzero
  // coordinate 1); the pair {v, -v} of F_q^* is indexed by pair_of[v].
  uint64_t functional_class(Vec lam, int m, int& half) const {
    int j0 = first_nonzero(lam);
    int v = get(lam, j0);
    half = F.neg[v] < v ? 1 : 0;
    int iv = F.inv[v];
    uint64_t off = 0;
    for (int j = 0; j < j0; ++j) off += qpow[m - 1 - j];
    uint64_t mu = 0;
    for (int t = m - 1; t > j0; --t) mu = mu * (uint64_t)q + (uint64_t)F.mul[iv][get(lam, t)];
    return (off + mu) * (uint64_t)((q - 1) / 2) + (uint64_t)pair_of(v);
  }
  int pair_of(int v) const {  // rank of min(v,-v) among {u in F_q^*: u < -u}
    int r = 0, lo = std::min(v, (int)F.neg[v]);
    for (int u = 1; u < lo; ++u)
      if (u < F.neg[u]) ++r;
    return r;
  }
  // phi_lambda(B): delete the first coordinate where lambda is nonzero.
  Sub restrict_to_kernel(const Sub& B, Vec lam) const {
    int j = first_nonzero(lam);
    Sub out;
    out.d = B.d;
    for (int i = 0; i < B.d; ++i) out.r[i] = delete_coord(B.r[i], j);
    return out;
  }
  // Annihilator (as row vectors) of U <= F_q^n, in echelon form.
  Sub annihilator(const Sub& U, int n) const {
    uint32_t pm = U.pivmask();
    std::vector<Vec> rows;
    for (int t = 0; t < n; ++t) {
      if (pm >> t & 1) continue;
      Vec lam = unit(t);
      for (int i = 0; i < U.d; ++i) lam = put(lam, lead(U.r[i]), F.neg[get(U.r[i], t)]);
      rows.push_back(lam);
    }
    return echelon(rows, n);
  }
  Sub echelon(const std::vector<Vec>& vs, int n) const {
    Sub B;
    B.d = 0;
    for (Vec v : vs) {
      for (int i = 0; i < B.d; ++i) {
        int pb = lead(B.r[i]);
        int c = get(v, pb);
        if (c) v = axpy(v, F.neg[c], B.r[i], n);
      }
      int pv = lead(v);
      if (pv < 0) continue;
      int inv = F.inv[get(v, pv)];
      Vec w = 0;
      for (int i = 0; i < n; ++i) w |= Vec(F.mul[inv][get(v, i)]) << (kCoordBits * i);
      for (int i = 0; i < B.d; ++i) {
        int c = get(B.r[i], pv);
        if (c) B.r[i] = axpy(B.r[i], F.neg[c], w, n);
      }
      B.r[B.d++] = w;
    }
    // insertion sort by pivot
    for (int i = 1; i < B.d; ++i)
      for (int j = i; j > 0 && lead(B.r[j]) < lead(B.r[j - 1]); --j) std::swap(B.r[j], B.r[j - 1]);
    return B;
  }
  int dim_of_sum(const Sub& U, const Sub& W, int n) const {
    std::vector<Vec> vs(U.r, U.r + U.d);
    vs.insert(vs.end(), W.r, W.r + W.d);
    return echelon(vs, n).d;
  }
};

}  // namespace fsc
