"""Markdown tables for README.md from the result files.
usage: python analysis/readme_tables.py zeta paired.csv ...   (later files win for the same q, n)
       python analysis/readme_tables.py grass grassmann.csv ...
       python analysis/readme_tables.py inc rows.tex"""
import csv
import math
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from incidence_model import gauss  # noqa: E402
from zeta_model import N, counts, pairs  # noqa: E402


def r3(v):
    """Ratios: 1.05, 18.0, 105."""
    return f"{v:.2f}" if v < 10 else f"{v:.1f}" if v < 100 else f"{v:.0f}"


def gbs(gb):
    return f"{gb / 1e3:.1f} TB" if gb >= 1e3 else f"{gb:.0f} GB" if gb >= 10 else f"{gb:.2g} GB"


def two(v):
    if v >= 100:
        return f"{float(f'{v:.2g}'):.0f}"
    return f"{v:.2g}" if v >= 10 else f"{v:.2f}" if v < 1 else f"{v:.1f}"


def sci(v):
    e = int(math.floor(math.log10(v)))
    m = v / 10 ** e
    if round(m, 1) >= 10:
        m, e = m / 10, e + 1
    return f"{m:.1f}·10^{e}"


def tsec(s):
    if s < 1:
        return f"{two(s * 1e3)} ms"
    if s < 600:
        return f"{two(s)} s" if s < 100 else f"{s:.0f} s"
    if s < 7200:
        return f"{s / 60:.0f} min"
    return f"{s / 3600:.1f} h"


def zeta(paths):
    rows = {}
    for path in paths:
        for r in csv.DictReader(open(path, newline="")):
            if r["direction"] == "zeta":
                rows[(int(r["q"]), int(r["n"]))] = r
    print("| field | subspaces $N$ | covering pairs | recursion | hybrid | covering-pair algorithm "
          "| time ratio, recursion | time ratio, hybrid | operation ratio |")
    print("|---|---|---|---|---|---|---|---|---|")
    for q in sorted({q for q, _ in rows}):
        n = max(nn for qq, nn in rows if qq == q)
        r = rows[(q, n)]
        Z, p = counts(q)
        ops = pairs(q, n) / Z(n, n, p != 2)
        frac = float(r["sweep_fraction"])
        star = "*" if frac < 1 else ""
        gb = float(r["index_gb"])
        print(f"| $\\mathbb F_{{{q}}}^{{{n}}}$ | {sci(float(r['N']))} | {gbs(gb)}{star} "
              f"| {tsec(float(r['fast_median']))} | {tsec(float(r['hybrid_median']))} "
              f"| {tsec(float(r['lattice_median']))}{star} "
              f"| {r3(float(r['ratio_fast_median']))}× | {r3(float(r['ratio_hybrid_median']))}× | {r3(ops)} |")


def grass(paths):
    res = {}
    for path in paths:
        for r in csv.DictReader(open(path, newline="")):
            res[(int(r["q"]), int(r["n"]), int(r["k"]), r["method"])] = r
    graphs = sorted({k[:3] for k in res if int(res[k]["v"]) >= 1e4}, key=lambda g: (g[0], g[1]))
    print("| graph | vertices | ours | factored recurrence | explicit adjacency | our reduction with covering pairs |")
    print("|---|---|---|---|---|---|")
    for g in graphs:
        q, n, k = g
        fast = float(res[g + ("fast",)]["t_median"])

        def ratio(m, odd_note=""):
            r = res.get(g + (m,))
            if r is None:
                return "not run"
            if not r["t_median"]:
                if m == "graph":
                    deg = q * gauss(k, 1, q) * gauss(n - k, 1, q)
                    return f"not run ({gbs(float(r['v']) * deg * 4 / 1e9)})"
                return r["note"] or "not run"
            return f"{r3(float(r['t_median']) / fast)}×{odd_note}"
        odd = "†" if q % 2 else ""
        print(f"| $J_{{{q}}}({n},{k})$ | {sci(float(res[g + ('fast',)]['v']))} | {tsec(fast)} "
              f"| {ratio('factored')} | {ratio('graph')} | {ratio('lattice', odd)} |")


def inc(path):
    print("| $t$ | $q$ | $(n,a,b)$ | $S$ | ours | direct | covering | Poisson | covering, time | Poisson, time |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("%"):
            continue
        cells = [c.strip() for c in line.rstrip("\\").split("&")]
        out = []
        for c in cells:
            c = c.replace("$^\\dagger$", "†").replace("\\,", " ").replace("--", "–")
            c = re.sub(r"\\mathbf\{([^}]*)\}", r"**\1**", c)
            c = re.sub(r"\\cdot10\^\{(-?\d+)\}", r"·10^\1", c)
            c = c.replace("$", "")
            out.append(c)
        print("| " + " | ".join(out) + " |")


if __name__ == "__main__":
    kind, args = sys.argv[1], sys.argv[2:]
    {"zeta": zeta, "grass": grass, "inc": lambda a: inc(a[0])}[kind](args)
