#!/usr/bin/env python3
"""Check the output of `lake env lean Audit.lean`.

Usage: check_axioms.py AUDIT_LOG AUDIT_LEAN

Fails unless
* every `#print axioms` command in AUDIT_LEAN produced a report in AUDIT_LOG, and
* every reported axiom is one of Lean's three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`); in particular no `sorryAx`, and
* the log contains no error.
"""
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    log_path, lean_path = sys.argv[1], sys.argv[2]
    log = open(log_path, encoding="utf-8").read()
    commands = [line for line in open(lean_path, encoding="utf-8")
                if line.startswith("#print axioms")]

    if re.search(r"\berror\b", log):
        print(log)
        print("error: the audit file did not elaborate cleanly", file=sys.stderr)
        return 1

    reports = re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    if len(reports) != len(commands):
        print(f"error: {len(commands)} #print axioms commands but {len(reports)} reports",
              file=sys.stderr)
        return 1

    bad = []
    for name, _, axioms in reports:
        used = {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()}
        if not used <= ALLOWED:
            bad.append((name, sorted(used - ALLOWED)))
    for name, extra in bad:
        print(f"error: {name} depends on {', '.join(extra)}", file=sys.stderr)
    if bad:
        return 1
    print(f"axiom audit passed: {len(reports)} declarations, axioms within "
          f"{{{', '.join(sorted(ALLOWED))}}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
