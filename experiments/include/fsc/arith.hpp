// Coefficient arithmetic and batched radix-p DFTs.
//
// A "row" is a vector of `beta` coefficients (the batch).  dft() transforms a
// block of p^ndig rows, digit by digit (base p), with kernel omega^(sign*a*b).
// Three policies:
//   RealArith    double, characteristic 2 (q = 2, 4, 8, 16): Walsh-Hadamard.
//   ComplexArith complex<double> stored as {re, im}, any p.
//   ModArith     exact arithmetic modulo P = 15*2^27+1 (p | P-1 for p = 2, 3, 5).
#pragma once

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <vector>

namespace fsc {

struct Cplx {
  double re, im;
};

// --------------------------------------------------------------------------
struct RealArith {
  using T = double;
  static constexpr bool kHasConj = false;
  static void conj_copy(T*, const T*, size_t) {}
  int p = 2;
  explicit RealArith(int p_) : p(p_) {
    if (p_ != 2) throw std::invalid_argument("RealArith requires characteristic 2");
  }
  static T from_double(double v) { return v; }
  static double to_double(T v) { return v; }
  static constexpr int flops_per_add = 1;

  void dft(T* x, int ndig, size_t beta, int /*sign*/) const {
    size_t len = size_t(1) << ndig;
    for (size_t s = 1; s < len; s <<= 1)
      for (size_t base = 0; base < len; base += 2 * s)
        for (size_t i = base; i < base + s; ++i) {
          T* a = x + i * beta;
          T* b = x + (i + s) * beta;
          for (size_t t = 0; t < beta; ++t) {
            T u = a[t], v = b[t];
            a[t] = u + v;
            b[t] = u - v;
          }
        }
  }
  static void add_to(T* dst, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] += src[t];
  }
  static void sub_from(T* dst, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] -= src[t];
  }
  // dst = dst * s + src
  static void scale_add(T* dst, double s, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] = dst[t] * s + src[t];
  }
  static void scale(T* dst, double s, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] *= s;
  }
  static void mul_pointwise(T* dst, const T* a, const T* b, size_t n) {
    for (size_t t = 0; t < n; ++t) dst[t] = a[t] * b[t];
  }
  // flops of one dft on p^ndig rows, per batch element
  static double dft_flops(int ndig) { return double(ndig) * std::ldexp(1.0, ndig); }
  static double value_flops() { return 1; }  // one add / one scaling
};

// --------------------------------------------------------------------------
struct ComplexArith {
  using T = Cplx;
  static constexpr bool kHasConj = true;
  static void conj_copy(T* dst, const T* src, size_t n) {
    for (size_t t = 0; t < n; ++t) dst[t] = {src[t].re, -src[t].im};
  }
  int p;
  std::vector<double> c, s;  // cos/sin(2 pi j / p)
  explicit ComplexArith(int p_) : p(p_), c(p_), s(p_) {
    for (int j = 0; j < p; ++j) {
      c[j] = std::cos(2 * M_PI * j / p);
      s[j] = std::sin(2 * M_PI * j / p);
    }
  }
  static T from_double(double v) { return {v, 0.0}; }
  static double to_double(T v) { return v.re; }

  void dft(T* x, int ndig, size_t beta, int sign) const {
    size_t len = 1;
    for (int i = 0; i < ndig; ++i) len *= (size_t)p;
    if (p == 2) {
      for (size_t st = 1; st < len; st <<= 1)
        for (size_t base = 0; base < len; base += 2 * st)
          for (size_t i = base; i < base + st; ++i) {
            T* a = x + i * beta;
            T* b = x + (i + st) * beta;
            for (size_t t = 0; t < beta; ++t) {
              T u = a[t], v = b[t];
              a[t] = {u.re + v.re, u.im + v.im};
              b[t] = {u.re - v.re, u.im - v.im};
            }
          }
      return;
    }
    if (p == 3) {
      const double h = sign * std::sqrt(3.0) / 2.0;
      for (size_t st = 1; st < len; st *= 3)
        for (size_t base = 0; base < len; base += 3 * st)
          for (size_t i = base; i < base + st; ++i) {
            T* x0 = x + i * beta;
            T* x1 = x + (i + st) * beta;
            T* x2 = x + (i + 2 * st) * beta;
            for (size_t t = 0; t < beta; ++t) {
              double t1r = x1[t].re + x2[t].re, t1i = x1[t].im + x2[t].im;
              double dr = x1[t].re - x2[t].re, di = x1[t].im - x2[t].im;
              double mr = x0[t].re - 0.5 * t1r, mi = x0[t].im - 0.5 * t1i;
              double vr = -h * di, vi = h * dr;  // sign * i * sqrt(3)/2 * d
              x0[t] = {x0[t].re + t1r, x0[t].im + t1i};
              x1[t] = {mr + vr, mi + vi};
              x2[t] = {mr - vr, mi - vi};
            }
          }
      return;
    }
    if (p == 5) {
      // y1,4 = a1 +- i b1, y2,3 = a2 +- i b2 with t1 = x1+x4, t2 = x2+x3, t3 = x1-x4, t4 = x2-x3
      const double c1 = std::cos(2 * M_PI / 5), c2 = std::cos(4 * M_PI / 5);
      const double s1 = sign * std::sin(2 * M_PI / 5), s2 = sign * std::sin(4 * M_PI / 5);
      for (size_t st = 1; st < len; st *= 5)
        for (size_t base = 0; base < len; base += 5 * st)
          for (size_t i = base; i < base + st; ++i) {
            T* x0 = x + i * beta;
            T* x1 = x + (i + st) * beta;
            T* x2 = x + (i + 2 * st) * beta;
            T* x3 = x + (i + 3 * st) * beta;
            T* x4 = x + (i + 4 * st) * beta;
            for (size_t t = 0; t < beta; ++t) {
              double t1r = x1[t].re + x4[t].re, t1i = x1[t].im + x4[t].im;
              double t2r = x2[t].re + x3[t].re, t2i = x2[t].im + x3[t].im;
              double t3r = x1[t].re - x4[t].re, t3i = x1[t].im - x4[t].im;
              double t4r = x2[t].re - x3[t].re, t4i = x2[t].im - x3[t].im;
              double a1r = x0[t].re + c1 * t1r + c2 * t2r, a1i = x0[t].im + c1 * t1i + c2 * t2i;
              double a2r = x0[t].re + c2 * t1r + c1 * t2r, a2i = x0[t].im + c2 * t1i + c1 * t2i;
              double b1r = s1 * t3r + s2 * t4r, b1i = s1 * t3i + s2 * t4i;
              double b2r = s2 * t3r - s1 * t4r, b2i = s2 * t3i - s1 * t4i;
              x0[t] = {x0[t].re + t1r + t2r, x0[t].im + t1i + t2i};
              x1[t] = {a1r - b1i, a1i + b1r};  // a1 + i b1
              x4[t] = {a1r + b1i, a1i - b1r};  // a1 - i b1
              x2[t] = {a2r - b2i, a2i + b2r};
              x3[t] = {a2r + b2i, a2i - b2r};
            }
          }
      return;
    }
    if (p % 2 == 1 && p <= 31) {
      // odd p >= 7: pair x_j with x_{p-j} as in the radix-5 kernel,
      //   y_k, y_{p-k} = x_0 + sum_j cos(2pi jk/p) (x_j + x_{p-j})
      //                  +- i * sign * sum_j sin(2pi jk/p) (x_j - x_{p-j}),  j, k = 1..h = (p-1)/2,
      // so 8h^2 + 10h real operations per length-p transform instead of 8p^2.
      const int h = (p - 1) / 2;
      double cs[16][16], sn[16][16];
      for (int k = 1; k <= h; ++k)
        for (int j = 1; j <= h; ++j) {
          cs[k][j] = c[(j * k) % p];
          sn[k][j] = sign * s[(j * k) % p];
        }
      for (size_t st = 1; st < len; st *= (size_t)p)
        for (size_t base = 0; base < len; base += (size_t)p * st)
          for (size_t i = base; i < base + st; ++i)
            for (size_t t = 0; t < beta; ++t) {
              T* x0 = x + i * beta + t;
              const size_t step = st * beta;
              double pr[16], pi[16], mr[16], mi[16];
              double y0r = x0->re, y0i = x0->im;
              for (int j = 1; j <= h; ++j) {
                const T& u = x0[(size_t)j * step];
                const T& v = x0[(size_t)(p - j) * step];
                pr[j] = u.re + v.re; pi[j] = u.im + v.im;
                mr[j] = u.re - v.re; mi[j] = u.im - v.im;
                y0r += pr[j]; y0i += pi[j];
              }
              const double xr = x0->re, xi = x0->im;
              for (int k = 1; k <= h; ++k) {
                double ar = xr, ai = xi, br = 0, bi = 0;
                for (int j = 1; j <= h; ++j) {
                  ar += cs[k][j] * pr[j]; ai += cs[k][j] * pi[j];
                  br += sn[k][j] * mr[j]; bi += sn[k][j] * mi[j];
                }
                x0[(size_t)k * step] = {ar - bi, ai + br};        // a + i b
                x0[(size_t)(p - k) * step] = {ar + bi, ai - br};  // a - i b
              }
              *x0 = {y0r, y0i};
            }
      return;
    }
    // generic radix-p
    std::vector<T> tmp((size_t)p);
    for (size_t st = 1; st < len; st *= (size_t)p)
      for (size_t base = 0; base < len; base += (size_t)p * st)
        for (size_t i = base; i < base + st; ++i)
          for (size_t t = 0; t < beta; ++t) {
            for (int k = 0; k < p; ++k) {
              double re = 0, im = 0;
              for (int j = 0; j < p; ++j) {
                const T& v = x[(i + (size_t)j * st) * beta + t];
                int w = (j * k) % p;
                double cr = c[w], ci = sign * s[w];
                re += v.re * cr - v.im * ci;
                im += v.re * ci + v.im * cr;
              }
              tmp[k] = {re, im};
            }
            for (int k = 0; k < p; ++k) x[(i + (size_t)k * st) * beta + t] = tmp[k];
          }
  }
  static void add_to(T* dst, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) { dst[t].re += src[t].re; dst[t].im += src[t].im; }
  }
  static void sub_from(T* dst, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) { dst[t].re -= src[t].re; dst[t].im -= src[t].im; }
  }
  static void scale_add(T* dst, double sc, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) {
      dst[t].re = dst[t].re * sc + src[t].re;
      dst[t].im = dst[t].im * sc + src[t].im;
    }
  }
  static void scale(T* dst, double sc, size_t beta) {
    for (size_t t = 0; t < beta; ++t) { dst[t].re *= sc; dst[t].im *= sc; }
  }
  static void mul_pointwise(T* dst, const T* a, const T* b, size_t n) {
    for (size_t t = 0; t < n; ++t)
      dst[t] = {a[t].re * b[t].re - a[t].im * b[t].im, a[t].re * b[t].im + a[t].im * b[t].re};
  }
  double dft_flops(int ndig) const {
    double len = std::pow((double)p, ndig);
    // real flops per butterfly as implemented above
    const double h = (p - 1) / 2;
    double per_butterfly = (p == 2) ? 4 : (p == 3) ? 16 : (p == 5) ? 48
                         : (p % 2 == 1 && p <= 31) ? 8 * h * h + 10 * h : double(p * p * 8);
    return ndig * (len / p) * per_butterfly;
  }
  static double value_flops() { return 2; }
};

// --------------------------------------------------------------------------
struct ModArith {
  using T = uint64_t;
  static constexpr bool kHasConj = false;
  static void conj_copy(T*, const T*, size_t) {}
  static constexpr uint64_t P = 2013265921ULL;  // 15 * 2^27 + 1
  int p;
  std::vector<uint64_t> w;  // w[j] = omega^j
  static uint64_t powmod(uint64_t a, uint64_t e) {
    uint64_t r = 1;
    a %= P;
    while (e) {
      if (e & 1) r = r * a % P;
      a = a * a % P;
      e >>= 1;
    }
    return r;
  }
  explicit ModArith(int p_) : p(p_), w(p_) {
    if ((P - 1) % (uint64_t)p) throw std::invalid_argument("no p-th root of unity mod P");
    uint64_t omega = powmod(31, (P - 1) / (uint64_t)p);
    if (powmod(omega, (uint64_t)p) != 1 || (p > 1 && omega == 1)) throw std::logic_error("bad root");
    for (int j = 0; j < p; ++j) w[j] = powmod(omega, (uint64_t)j);
  }
  static T from_int(int64_t v) { return (uint64_t)(((v % (int64_t)P) + (int64_t)P) % (int64_t)P); }
  void dft(T* x, int ndig, size_t beta, int sign) const {
    size_t len = 1;
    for (int i = 0; i < ndig; ++i) len *= (size_t)p;
    std::vector<T> tmp((size_t)p);
    for (size_t st = 1; st < len; st *= (size_t)p)
      for (size_t base = 0; base < len; base += (size_t)p * st)
        for (size_t i = base; i < base + st; ++i)
          for (size_t t = 0; t < beta; ++t) {
            for (int k = 0; k < p; ++k) {
              uint64_t acc = 0;
              for (int j = 0; j < p; ++j) {
                int e = ((sign > 0 ? j * k : (p - (j * k) % p)) % p);
                acc = (acc + x[(i + (size_t)j * st) * beta + t] * w[e]) % P;
              }
              tmp[k] = acc;
            }
            for (int k = 0; k < p; ++k) x[(i + (size_t)k * st) * beta + t] = tmp[k];
          }
  }
  static void add_to(T* dst, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] = (dst[t] + src[t]) % P;
  }
  static void sub_from(T* dst, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] = (dst[t] + P - src[t]) % P;
  }
  // `s` is passed as the inverse power q^-m encoded by scale_of()
  static void scale_add(T* dst, uint64_t s, const T* src, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] = (dst[t] * s + src[t]) % P;
  }
  static void scale(T* dst, uint64_t s, size_t beta) {
    for (size_t t = 0; t < beta; ++t) dst[t] = dst[t] * s % P;
  }
  static void mul_pointwise(T* dst, const T* a, const T* b, size_t n) {
    for (size_t t = 0; t < n; ++t) dst[t] = a[t] * b[t] % P;
  }
  double dft_flops(int) const { return 0; }
  static double value_flops() { return 1; }
};

// Scalar q^{-m} in the representation the policy expects.
inline double inv_qpow(const RealArith&, int q, int m) { return std::pow((double)q, -m); }
inline double inv_qpow(const ComplexArith&, int q, int m) { return std::pow((double)q, -m); }
inline uint64_t inv_qpow(const ModArith&, int q, int m) {
  return ModArith::powmod(ModArith::powmod((uint64_t)q, (uint64_t)m), ModArith::P - 2);
}

}  // namespace fsc
