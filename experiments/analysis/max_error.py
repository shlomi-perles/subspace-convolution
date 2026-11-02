"""Largest error per result file and column, over every column whose name contains
err or diff, and the largest of all.
usage: python analysis/max_error.py results"""
import csv
import math
import os
import sys

worst = (0.0, "")
for root, _, files in sorted(os.walk(sys.argv[1])):
    for name in sorted(files):
        if not name.endswith(".csv"):
            continue
        path = os.path.join(root, name)
        rows = list(csv.DictReader(open(path, newline="")))
        cols = [c for c in (rows[0].keys() if rows else []) if "err" in c or "diff" in c]
        for c in cols:
            vals = []
            for r in rows:
                try:
                    v = float(r[c])
                except (TypeError, ValueError):
                    continue
                if not math.isnan(v):
                    vals.append((v, r))
            if not vals:
                continue
            v, r = max(vals, key=lambda x: x[0])
            where = " ".join(f"{k}={r[k]}" for k in ("experiment", "q", "n", "a", "b", "k", "check", "method") if r.get(k))
            print(f"{os.path.relpath(path, sys.argv[1])}: {c} max {v:.3g} over {len(vals)} rows ({where})")
            if v > worst[0]:
                worst = (v, f"{os.path.relpath(path, sys.argv[1])} {c} {where}")
print(f"largest: {worst[0]:.3g} at {worst[1]}")
