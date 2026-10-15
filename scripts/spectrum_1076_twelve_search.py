#!/usr/bin/env python3
"""Reproduce the six exhaustive E1076 order-12 first-row searches.

These are research searches, not Lean certificates. Finite E1076 magmas are
idempotent Latin, and their left translations have no nontrivial two-cycles.
Thus the eleven nonzero points of a normalized first row have one of the six
cycle types below. The Lean CanonicalData/RowTransfer modules formalize the
relabeling between the thirteen ordered rows and these six representatives.
The optionally strengthened encoding is formalized in ShortCycles.lean.
The completed Lean exclusion uses further normalization and conditional
three-cycle clauses; reproduce its certificates with
scripts/spectrum_1076_twelve_certificate.py.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import time

from spectrum_small_orders import clauses, variables
from spectrum_generate import load_equations, satisfies

CASES = [(3, 3, 5), (3, 4, 4), (3, 8), (4, 7), (5, 6), (11,)]


def first_row(parts):
    row, offset = [0], 1
    for k in parts:
        row += list(range(offset + 1, offset + k)) + [offset]
        offset += k
    assert len(row) == 12
    return row


def search_clauses(parts, strong=False):
    n = 12
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    q = lambda x, y, z: 1 + n**3 + (x * n + y) * n + z
    cs = clauses(1076, n)
    if strong:
        cs += [[p(x, x, x)] for x in range(n)]
        cs += [[-p(x, y, z), -p(x, z, y)]
               for x, y, z in product(range(n), repeat=3) if x != y]
        cs += [[-q(x, y, y)] for x, y in product(range(n), repeat=2) if x != y]
        for x, y in product(range(n), repeat=2):
            for vs in ([q(x, z, y) for z in range(n)],
                       [q(z, x, y) for z in range(n)]):
                cs.append(vs)
                cs += [[-a, -b] for a, b in combinations(vs, 2)]
    if parts is not None:
        cs += [[p(0, y, z)] for y, z in enumerate(first_row(parts))]
    return cs


def cnf_bytes(parts, strong=False):
    cs = search_clauses(parts, strong)
    return (f"p cnf {variables(1076, 12)} {len(cs)}\n" +
            "".join(" ".join(map(str, c)) + " 0\n" for c in cs)).encode()


def run(parts, args):
    label = "whole" if parts is None else "-".join(map(str, parts))
    label += "-strong" if args.strong else "-base"
    path = args.output / f"{label}.cnf"
    path.write_bytes(cnf_bytes(parts, args.strong))
    if not args.solve:
        print(path)
        return
    start = time.monotonic()
    with path.with_suffix(".log").open("w") as log:
        process = subprocess.run(["cadical", "-t", str(args.seconds), str(path)],
                                 stdout=log, stderr=subprocess.STDOUT,
                                 timeout=args.seconds + 20)
    result = dict(law=1076, order=12, cycles=None if parts is None else [1, *parts],
                  strong=args.strong,
                  status={10: "SAT", 20: "UNSAT"}.get(process.returncode, "timeout"),
                  seconds=round(time.monotonic() - start, 3), lean_proof=False)
    if process.returncode == 10:
        pos = {int(s) for line in path.with_suffix(".log").read_text().splitlines()
               if line.startswith("v ") for s in line[2:].split() if int(s) > 0}
        table = [next(z for z in range(12) if 1 + (x * 12 + y) * 12 + z in pos)
                 for x, y in product(range(12), repeat=2)]
        assert satisfies(*load_equations()[1075], table, 12)
        result["table"] = table
    path.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--strong", action="store_true")
    parser.add_argument("--whole", action="store_true", help="Do not fix a first row")
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--output", type=Path,
                        default=Path(".cache/e1076-twelve-search"))
    args = parser.parse_args()
    if args.seconds <= 0 or args.jobs <= 0:
        parser.error("--seconds and --jobs must be positive")
    args.output.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(lambda parts: run(parts, args), [None] if args.whole else CASES))


if __name__ == "__main__":
    main()
