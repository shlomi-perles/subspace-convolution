"""Exact operation counts of the zeta-transform recursion (port of zeta_flops in
include/fsc/zeta.hpp, pure recursion, forward transform, k = n) and of the
covering-pair algorithm (one addition per covering pair).
usage: python analysis/zeta_model.py"""
from functools import lru_cache

from incidence_model import factor, gauss


def counts(q):
    p, e = factor(q)
    if p == 2:
        dft = lambda nd: nd * 2.0 ** nd
        val = 1.0
    else:
        h = (p - 1) // 2  # paired length-p kernel of ComplexArith::dft_flops
        pb = {3: 16, 5: 48}.get(p, 8 * h * h + 10 * h if p <= 31 else p * p * 8)
        dft = lambda nd: nd * (p ** nd / p) * pb
        val = 2.0

    @lru_cache(None)
    def Z(n, k, real):
        k = min(k, max(n, 0))
        if n <= 0 or k <= 0:
            return 0.0
        kin = min(k, n - 1)
        f = Z(n - 1, kin, real)
        f += sum(gauss(n - 1, d - 1, q) * (2 * dft((n - d) * e) + 2 * q ** (n - d) * val) for d in range(1, k + 1))
        f += Z(n - 1, k - 1, real)
        nfun = q ** (n - 1) - 1
        if n >= 2 and nfun > 0:
            half = real and p != 2
            f += (nfun // 2 if half else nfun) * Z(n - 2, k - 1, False)
        return f

    return Z, p


def N(q, n):
    return sum(gauss(n, r, q) for r in range(n + 1))


def pairs(q, n):
    return sum(gauss(n, r, q) * gauss(n - r, 1, q) for r in range(n))


if __name__ == "__main__":
    for q in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 32):
        Z, p = counts(q)
        row = []
        for n in range(3, 13):
            if N(q, n) > 1e19:
                break
            row.append(f"n={n}: N={N(q, n):.2g} ratio={pairs(q, n) / Z(n, n, p != 2):.3g}")
        print(f"q={q}: " + "; ".join(row))
