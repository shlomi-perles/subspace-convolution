"""Everything the paper and README.md take from results/: the figure data
(figures/data), the rows of the incidence table (paper/experiments_appendix.tex at the
repository root), the three README tables and the largest error.  Writes the figure
data and the table rows in place and prints the README tables; with --check, changes
nothing and exits with status 1 if anything committed differs from what results/ gives,
or if any error reaches 1e-13 (the bound stated in the paper).  Without the paper's
sources (or without the row markers in them), the table rows are printed instead of
written or checked.
usage: python analysis/paper_assets.py [--check]"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
RESULTS = os.path.join(ROOT, "results")
FIGURE_DATA = os.path.join(ROOT, "figures", "data")
APPENDIX = os.path.join(os.path.dirname(ROOT), "paper", "experiments_appendix.tex")
README = os.path.join(ROOT, "README.md")
BEGIN, END = "% rows from analysis/incidence_table.py", "% end of rows"

# Which result files each output uses (see "Provenance" in README.md).
FIGURE = ["bigmem/paired.csv", "phase3/paired.csv"]
INCIDENCE = ["phase2/incidence_hard.csv", "phase2/poisson.csv", "phase2b_n1/poisson.csv"]
ZETA = ["bigmem/paired.csv", "phase4/paired.csv", "phase3/paired.csv", "phase2b/paired.csv"]  # later files win
GRASSMANN = ["bigmem/grassmann.csv", "phase2b_n1/grassmann.csv"]


def run(script, *args):
    env = dict(os.environ, PYTHONIOENCODING="utf-8")
    out = subprocess.run([sys.executable, os.path.join(HERE, script), *args], check=True,
                         capture_output=True, text=True, encoding="utf-8", env=env)
    return out.stdout


def results(paths):
    return [os.path.join(RESULTS, p) for p in paths]


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read().replace("\r\n", "\n")


def main():
    check = sys.argv[1:] == ["--check"]
    problems = []

    with tempfile.TemporaryDirectory() as tmp:
        out = tmp if check else FIGURE_DATA
        run("figure_data.py", out, *results(FIGURE))
        if check:
            names = sorted(set(os.listdir(tmp)) | set(os.listdir(FIGURE_DATA)))
            for name in names:
                a, b = os.path.join(tmp, name), os.path.join(FIGURE_DATA, name)
                if not (os.path.exists(a) and os.path.exists(b) and read(a) == read(b)):
                    problems.append(f"figures/data/{name} differs from results/")

        rows = [line for line in run("incidence_table.py", *results(INCIDENCE)).splitlines() if line.strip()]
        lines = read(APPENDIX).split("\n") if os.path.exists(APPENDIX) else []
        if BEGIN not in lines or END not in lines:
            if check:
                print("incidence table not checked: no paper/experiments_appendix.tex with the row markers")
            else:
                print("incidence table rows (no paper/experiments_appendix.tex with the row markers):")
                print("\n".join(rows) + "\n")
        else:
            i, j = lines.index(BEGIN), lines.index(END)
            if lines[i + 1:j] != rows:
                if check:
                    problems.append("the incidence table in paper/experiments_appendix.tex differs from results/")
                else:
                    with open(APPENDIX, "w", encoding="utf-8", newline="\n") as f:
                        f.write("\n".join(lines[:i + 1] + rows + lines[j:]))
        rows_file = os.path.join(tmp, "rows.tex")
        with open(rows_file, "w", encoding="utf-8") as f:
            f.write("\n".join(rows) + "\n")

        readme = read(README)
        tables = {"incidence": run("readme_tables.py", "inc", rows_file),
                  "full transform": run("readme_tables.py", "zeta", *results(ZETA)),
                  "Grassmann": run("readme_tables.py", "grass", *results(GRASSMANN))}
        for name, table in tables.items():
            table = table.replace("\r\n", "\n").strip()
            if check and table not in readme:
                problems.append(f"the {name} table in README.md differs from results/")
            if not check:
                print(f"README table, {name}:\n{table}\n")

    largest = run("max_error.py", RESULTS).strip().splitlines()[-1]
    print(largest)
    if float(largest.split()[1]) >= 1e-13:
        problems.append(f"an error reaches 1e-13: {largest}")

    for p in problems:
        print("MISMATCH:", p)
    if check:
        print("all outputs match results/" if not problems else f"{len(problems)} mismatches")
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
