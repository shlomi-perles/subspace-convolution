"""LaTeX rows for the incidence table of paper/experiments_appendix.tex and a plain
summary.  Inputs: incidence_hard.csv (fast transform, counted alternatives, the
covering-pair sweep where it ran) and one or more poisson.csv (Poisson summation, run).
The counted alternatives are recomputed here in exact integers: the driver that wrote
results/*/incidence_hard.csv counted the layers with uint64 Gaussian binomials, which
wrap for the middle layers of F_2^16 and F_3^15 (fixed in bench_incidence_hard.cpp
since).  Our operations and all times come from the CSV files.
usage: python analysis/incidence_table.py incidence_hard.csv poisson.csv [poisson.csv ...] > rows.tex"""
import csv
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from incidence_model import factor, gauss  # noqa: E402

ROWS = [(2, 16, 1, 15), (2, 14, 2, 12), (3, 8, 2, 6), (4, 8, 2, 6), (4, 9, 2, 7), (8, 6, 2, 4), (8, 7, 2, 5),
        (2, 10, 3, 7), (2, 11, 3, 8), (2, 12, 3, 9)]


def num(x):
    try:
        v = float(x)
        return None if math.isnan(v) else v
    except (TypeError, ValueError):
        return None


def sci(v, digits=2):
    """Two significant digits; powers of ten as 1.2\\cdot10^{3} from 10^4 on."""
    if v is None:
        return "--"
    if v < 9.95:
        return f"{v:.1f}" if v >= 1 else f"{v:.2f}"
    if v < 9995:
        return f"{v:.0f}" if v < 100 else f"{float(f'{v:.2g}'):.0f}"
    e = int(math.floor(math.log10(v)))
    m = v / 10 ** e
    if round(m, 1) >= 10:
        m, e = m / 10, e + 1
    return f"{m:.1f}\\cdot10^{{{e}}}"


def two(v):
    """Two significant digits without exponent: 806 -> 810, 1.905 -> 1.9, 1.014 -> 1.0."""
    return f"{v:.1f}" if v < 10 else f"{float(f'{v:.2g}'):g}"


def tsec(s):
    """Time in text mode with the number in math mode."""
    if s is None:
        return "--"
    if s < 1e-3:
        return f"${two(s * 1e6)}\\,\\mu$s"
    if s < 1:
        return f"${two(s * 1e3)}$\\,ms"
    if s < 600:
        return f"${two(s)}$\\,s" if s < 10 else f"${s:.0f}$\\,s"
    return f"${s / 60:.0f}$\\,min"


def main():
    inc = {(int(r["q"]), int(r["n"]), int(r["a"]), int(r["b"])): r for r in csv.DictReader(open(sys.argv[1]))}
    poi = {}
    for path in sys.argv[2:]:
        for r in csv.DictReader(open(path)):
            poi[(int(r["q"]), int(r["n"]), int(r["a"]), int(r["b"]))] = r
    for key in ROWS:
        q, n, a, b = key
        r = inc.get(key)
        if r is None:
            print(f"% missing {key}")
            continue
        S = num(r["S"])
        fast_s = num(r["fast_s"])
        flops = num(r["fast_flops"])
        t = min(a, n - b)
        layer_values = sum(gauss(n, j, q) for j in range(a, b + 1))
        tuple_values = q ** (t * n)
        direct = gauss(n, b, q) * gauss(b, a, q) / flops
        cover = sum(gauss(n, j, q) * gauss(j, 1, q) for j in range(a + 1, b + 1)) / flops
        tup = tuple_values * t * n * factor(q)[1] / flops
        ops = {"direct": direct, "cover": cover, "poisson": tup}
        best = min(ops, key=ops.get)
        cells = {k: (f"$\\mathbf{{{sci(v)}}}$" if k == best else f"${sci(v)}$") for k, v in ops.items()}
        sweep_s = num(r.get("sweep_s"))
        p = poi.get(key)
        pois_s = num(p["poisson_s"]) if p else None
        pois_fast = num(p["fast_s"]) if p else None
        # measured ratios: the alternative and the fast transform timed on the same machine;
        # Poisson against the fast transform of the same process
        m_cover = sweep_s / fast_s if sweep_s and fast_s else None
        m_pois = pois_s / pois_fast if pois_s and pois_fast else None
        dag = "$^\\dagger$" if (n, a, b) == (4 * a, a, 3 * a) else ""
        print(f"{t} & {q} & $({n},{a},{b})${dag} & ${sci(S)}$ & {tsec(fast_s)} & {cells['direct']} & "
              f"{cells['cover']} & {cells['poisson']} & {f'${sci(m_cover)}$' if m_cover else '--'} & "
              f"{f'${sci(m_pois)}$' if m_pois else '--'}\\\\")
        sys.stderr.write(f"{key}: S={S:.3g} fast={fast_s:.4g}s ({num(r['fast_gb']):.1f} GB) err={r['max_rel_err']} | "
                         f"ops direct {direct:.3g} cover {cover:.3g} poisson {tup:.3g} | sweep {sweep_s} "
                         f"({r.get('sweep_rel_err')}) poisson {pois_s} vs fast {pois_fast} "
                         f"({p['max_rel_diff_all'] if p else ''}) | layer GB {layer_values * 8 / 1e9:.3g} "
                         f"tuple GB {tuple_values * 8 / 1e9:.3g}\n")


if __name__ == "__main__":
    main()
