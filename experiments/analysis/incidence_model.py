"""Exact operation counts for the incidence transform I_n^{a,b} (port of
inc_flops in include/fsc/incidence.hpp) and for the three alternatives counted
in bench/bench_incidence_hard.cpp.  Used to choose instances.
usage: python analysis/incidence_model.py [max_S]"""
import sys
from functools import lru_cache

def gauss(n, k, q):
    if k < 0 or k > n or n < 0:
        return 0
    num = den = 1
    for i in range(k):
        num *= q ** (n - i) - 1
        den *= q ** (i + 1) - 1
    return num // den

def factor(q):
    for p in range(2, q + 1):
        if q % p == 0:
            e, r = 0, q
            while r % p == 0:
                r //= p; e += 1
            return p, e

def model(q):
    p, e = factor(q)
    if p == 2:
        dft = lambda nd: nd * 2.0 ** nd
        val = 1.0
    else:
        pb = {3: 16, 5: 48}.get(p, p * p * 8)
        dft = lambda nd: nd * (p ** nd / p) * pb
        val = 2.0
    @lru_cache(None)
    def F(n, a, b):
        if a == b or a == 0:
            return 0.0
        if b == n:
            return (gauss(n, a, q) - 1) * val
        f = F(n - 1, a, b) + F(n - 1, a, b - 1) + F(n - 1, a - 1, b - 1) + (q ** (n - 1) - 1) * F(n - 2, a - 1, b - 1)
        local = gauss(n - 1, a - 1, q) * dft((n - a) * e) + gauss(n - 1, b - 1, q) * dft((n - b) * e) \
            + 2 * (gauss(n, b, q) - gauss(n - 1, b, q)) * val
        return f + local
    return F, p, e

def instance(q, n, a, b):
    F, p, e = model(q)
    ours = F(n, a, b)
    S = gauss(n, a, q) + gauss(n, b, q)
    direct = gauss(n, b, q) * gauss(b, a, q)
    layer = sum(gauss(n, j, q) * gauss(j, 1, q) for j in range(a + 1, b + 1))
    layer_vals = sum(gauss(n, j, q) for j in range(a, b + 1))
    t = min(a, n - b)
    tup_vals = q ** (t * n)
    tup = tup_vals * t * n * e
    return dict(q=q, n=n, a=a, b=b, t=t, S=S, ours=ours, direct=direct / ours, layer=layer / ours,
                poisson=tup / ours, best=min(direct, layer, tup) / ours, layer_vals=layer_vals,
                tup_vals=tup_vals, complex=(p != 2))

if __name__ == "__main__":
    maxS = float(sys.argv[1]) if len(sys.argv) > 1 else 3e9
    rows = []
    for q in (2, 3, 4, 5, 7, 8, 9, 16):
        for n in range(4, 17):
            for a in range(1, n):
                for b in range(a + 1, n):
                    if not (2 * a < n < 2 * b):
                        continue
                    S = gauss(n, a, q) + gauss(n, b, q)
                    if S > maxS or S < 1e4:
                        continue
                    rows.append(instance(q, n, a, b))
    rows.sort(key=lambda r: -r["best"])
    for r in rows[:30]:
        bytes_per = 16 if r["complex"] else 8
        print(f"q={r['q']:2d} (n,a,b)=({r['n']},{r['a']},{r['b']}) t={r['t']} S={r['S']:.2e} ours/S={r['ours']/r['S']:.0f} "
              f"| direct {r['direct']:.3g}  layers {r['layer']:.3g}  poisson {r['poisson']:.3g}  -> best alt {r['best']:.3g}x "
              f"| mem layers {r['layer_vals']*bytes_per/1e9:.3g} GB, poisson {r['tup_vals']*bytes_per/1e9:.3g} GB")
