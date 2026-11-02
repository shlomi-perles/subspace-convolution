// Finite field GF(q), q = p^e <= kMaxQ (16, or 32 with -DFSC_COORD_BITS=5), with
// the trace-dual basis used by the FFT.
//
// Elements are codes 0..q-1; for e > 1 the code lists polynomial-basis
// coefficients in base p.  The Fourier transform over F_q^m is the plain DFT
// over Z_p^(e*m): inputs are indexed by polynomial-basis digits, outputs by
// trace-dual digits (elem_to_dual), so Tr(lambda*x) is a dot product of digits.
#pragma once

#include <array>
#include <cstdint>
#include <stdexcept>
#include <vector>

namespace fsc {

#ifndef FSC_COORD_BITS
#define FSC_COORD_BITS 4
#endif
constexpr int kMaxQ = 1 << FSC_COORD_BITS;

struct GF {
  int q = 0, p = 0, e = 0;
  std::array<std::array<uint8_t, kMaxQ>, kMaxQ> add{}, mul{};
  std::array<uint8_t, kMaxQ> neg{}, inv{}, tr{}, elem_to_dual{}, dual_to_elem{};

  explicit GF(int q_) : q(q_) {
    for (int c = 2; c <= q; ++c)
      if (q % c == 0) { p = c; break; }
    int r = q;
    while (r % p == 0) { r /= p; ++e; }
    if (r != 1 || q > kMaxQ) throw std::invalid_argument("q must be a prime power <= kMaxQ");
    // irreducible polynomial alpha^e = -sum low[j] alpha^j
    std::vector<int> low;
    if (e > 1) {
      if (q == 4) low = {1, 1};
      else if (q == 8) low = {1, 1, 0};
      else if (q == 9) low = {1, 0};
      else if (q == 16) low = {1, 1, 0, 0};
      else if (q == 32) low = {1, 0, 1, 0, 0};  // alpha^5 = alpha^2 + 1
      else throw std::invalid_argument("unsupported q");
    }
    auto digits = [&](int a) {
      std::vector<int> d(e);
      for (int j = 0; j < e; ++j) { d[j] = a % p; a /= p; }
      return d;
    };
    auto undigits = [&](const std::vector<int>& d) {
      int a = 0, w = 1;
      for (int j = 0; j < e; ++j) { a += d[j] * w; w *= p; }
      return a;
    };
    for (int a = 0; a < q; ++a)
      for (int b = 0; b < q; ++b) {
        auto x = digits(a), y = digits(b);
        std::vector<int> s(e);
        for (int j = 0; j < e; ++j) s[j] = (x[j] + y[j]) % p;
        add[a][b] = (uint8_t)undigits(s);
        std::vector<int> prod(2 * e - 1, 0);
        for (int i = 0; i < e; ++i)
          for (int j = 0; j < e; ++j) prod[i + j] = (prod[i + j] + x[i] * y[j]) % p;
        for (int deg = 2 * e - 2; deg >= e; --deg) {
          int c = prod[deg];
          if (!c) continue;
          prod[deg] = 0;
          for (int j = 0; j < e; ++j) prod[deg - e + j] = ((prod[deg - e + j] - c * low[j]) % p + p) % p;
        }
        prod.resize(e);
        mul[a][b] = (uint8_t)undigits(prod);
      }
    for (int a = 0; a < q; ++a) {
      for (int b = 0; b < q; ++b)
        if (add[a][b] == 0) neg[a] = (uint8_t)b;
      inv[a] = 0;
      for (int b = 1; b < q; ++b)
        if (mul[a][b] == 1) inv[a] = (uint8_t)b;
      if (a && mul[a][inv[a]] != 1) throw std::logic_error("reducible polynomial");
    }
    for (int a = 0; a < q; ++a) {
      int t = 0, pw = a;  // pw runs through a^(p^j)
      for (int j = 0; j < e; ++j) {
        t = add[t][pw];
        int nx = 1;
        for (int k = 0; k < p; ++k) nx = mul[nx][pw];
        pw = nx;
      }
      if (t >= p) throw std::logic_error("trace not in prime field");
      tr[a] = (uint8_t)t;
    }
    for (int lam = 0; lam < q; ++lam) {
      int code = 0, w = 1;
      for (int j = 0, b = 1; j < e; ++j, b *= p) { code += tr[mul[lam][b]] * w; w *= p; }
      elem_to_dual[lam] = (uint8_t)code;
      dual_to_elem[code] = (uint8_t)lam;
    }
  }
};

}  // namespace fsc
