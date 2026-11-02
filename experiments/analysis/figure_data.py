"""Data files for figures/zeta_fields.tex (pgfplots).
Panel (a): measured time ratio covering-pair sweep / FFT recursion (zeta direction,
median and quartiles of paired rounds) per field and table size; points whose sweep
was timed on a sample also go to time_q*_sampled.dat (open markers).  Panel (b):
exact operation ratio covering pairs / recursion operations from zeta_model.py.  Both
panels start at N >= 1e3.
usage: python analysis/figure_data.py OUTDIR paired.csv [paired.csv ...]"""
import csv
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zeta_model import N, counts, pairs  # noqa: E402

FIELDS = (2, 4, 8, 16, 32)


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    best = {}
    for path in sys.argv[2:]:
        for r in csv.DictReader(open(path, newline="")):
            if r["direction"] != "zeta" or int(r["q"]) not in FIELDS:
                continue
            key = (int(r["q"]), int(r["n"]))
            full = float(r["sweep_fraction"]) >= 1
            if key not in best or (full and not best[key][1]):  # a full run replaces a sampled one
                best[key] = (r, full)
    for q in FIELDS:
        rows = sorted((n, r, full) for (qq, n), (r, full) in best.items() if qq == q and float(r["N"]) >= 1e3)
        for suffix, sampled_only in (("", False), ("_sampled", True)):
            with open(os.path.join(out, f"time_q{q}{suffix}.dat"), "w") as f:
                f.write("N ratio lo hi\n")
                for n, r, full in rows:
                    if sampled_only and full:
                        continue
                    med = float(r["ratio_fast_median"])
                    lo = med - float(r["ratio_fast_q1"])
                    hi = float(r["ratio_fast_q3"]) - med
                    f.write(f"{float(r['N']):.6g} {med:.4g} {lo:.4g} {hi:.4g}\n")
        Z, p = counts(q)
        with open(os.path.join(out, f"ops_q{q}.dat"), "w") as f:
            f.write("N ratio\n")
            for n in range(3, 40):
                if N(q, n) > 1e18:
                    break
                if N(q, n) >= 1e3:
                    f.write(f"{N(q, n):.6g} {pairs(q, n) / Z(n, n, False):.4g}\n")
    for (q, n), (r, full) in sorted(best.items()):
        print(q, n, r["N"], r["ratio_fast_median"], "full" if full else "sampled")


if __name__ == "__main__":
    main()
