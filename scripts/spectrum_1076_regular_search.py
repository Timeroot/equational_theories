#!/usr/bin/env python3
"""Search E1076 operations admitting a regular group of automorphisms.

For a specified group G, every such operation has the form
    x * y = x f(x^-1 y).
The Cayley-table clauses below impose exactly this equivariance. The usual
first-row chain normalization is removed: it need not preserve the chosen
labels of the group. An UNSAT answer excludes only this restricted family.
"""

import argparse
from itertools import permutations, product
import json
from pathlib import Path
import subprocess
import time

from spectrum_small_orders import clauses, variables
from spectrum_generate import load_equations, satisfies


def group_table(kind):
    if kind == "A4":
        elements = [p for p in permutations(range(4))
                    if sum(p[i] > p[j] for i in range(4)
                           for j in range(i + 1, 4)) % 2 == 0]
        mul = lambda a, b: tuple(a[b[i]] for i in range(4))
    elif kind == "C3V4":
        elements = list(product(range(3), range(4)))
        mul = lambda a, b: ((a[0] + b[0]) % 3, a[1] ^ b[1])
    elif kind == "D12":
        elements = list(product(range(6), range(2)))
        mul = lambda a, b: ((a[0] + (-1)**a[1] * b[0]) % 6, a[1] ^ b[1])
    else:
        raise ValueError(kind)
    return [[elements.index(mul(a, b)) for b in elements] for a in elements]


def run(kind, seconds, output):
    n = 12
    group = group_table(kind)
    inv = [next(j for j in range(n) if group[i][j] == 0) for i in range(n)]
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    # The negative unit clauses in the chain encoding are exactly the
    # first-row normalization clauses; discard them before imposing symmetry.
    cs = [c for c in clauses(1076, n) if not (len(c) == 1 and c[0] < 0)]
    cs += [[p(x, x, x)] for x in range(n)]
    for x, y, z in product(range(n), repeat=3):
        u, v = p(x, y, z), p(0, group[inv[x]][y], group[inv[x]][z])
        cs.extend([[-u, v], [u, -v]])
    output.mkdir(parents=True, exist_ok=True)
    path = output / f"n12-regular-{kind}.cnf"
    path.write_text(f"p cnf {variables(1076, n)} {len(cs)}\n" +
                    "".join(" ".join(map(str, c)) + " 0\n" for c in cs))
    start = time.monotonic()
    with path.with_suffix(".log").open("w") as log:
        process = subprocess.run(["cadical", "-t", str(seconds), str(path)],
                                 stdout=log, stderr=subprocess.STDOUT,
                                 timeout=seconds + 20)
    result = dict(law=1076, order=12,
                  restriction=f"idempotent; left regular {kind} automorphisms",
                  status={10: "SAT", 20: "UNSAT"}.get(process.returncode, "timeout"),
                  seconds=round(time.monotonic() - start, 3),
                  proof_status="research only")
    if process.returncode == 10:
        positives = {int(s) for line in path.with_suffix(".log").read_text().splitlines()
                     if line.startswith("v ") for s in line[2:].split() if int(s) > 0}
        table = [next(z for z in range(n) if p(x, y, z) in positives)
                 for x, y in product(range(n), repeat=2)]
        assert satisfies(*load_equations()[1075], table, n)
        result["table"] = table
    path.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", choices=["A4", "C3V4", "D12"], required=True)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--output", type=Path,
                        default=Path(".cache/e1076-regular"))
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error("--seconds must be positive")
    run(args.group, args.seconds, args.output)


if __name__ == "__main__":
    main()
