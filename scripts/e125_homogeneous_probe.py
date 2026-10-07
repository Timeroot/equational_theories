#!/usr/bin/env python3
"""Bounded finite-group probes for right-translation-invariant E125 operations.

For m(x,y)=f(y*x^-1)*x, E125 is exactly
    f(f(f(x)^-1)*f(x)) = x.
See Definability/E125Homogeneous.lean. We ask additionally whether f(1) and
f(f(1)) can fail to commute. UNSAT is solver evidence only, not a Lean proof
and not a statement about infinite groups. A conflict budget is mandatory.
"""

import argparse
import itertools
import json
from pathlib import Path
import time

from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical195


def group_table(elements, product):
    index = {x: i for i, x in enumerate(elements)}
    return [[index[product(x, y)] for y in elements] for x in elements]


def semidirect(p, q, r):
    elements = list(itertools.product(range(p), range(q)))
    assert pow(r, q, p) == 1
    return group_table(elements, lambda x, y:
                       ((x[0] + pow(r, x[1], p) * y[0]) % p, (x[1] + y[1]) % q))


def permutation_group(n, even):
    elements = [p for p in itertools.permutations(range(n))
                if not even or sum(p[i] > p[j] for i in range(n)
                                   for j in range(i + 1, n)) % 2 == 0]
    return group_table(elements, lambda p, q: tuple(p[q[i]] for i in range(n)))


def quaternion():
    elements = list(itertools.product(range(2), range(4)))
    base = [[(0, 0), (0, 1), (0, 2), (0, 3)],
            [(0, 1), (1, 0), (0, 3), (1, 2)],
            [(0, 2), (1, 3), (1, 0), (0, 1)],
            [(0, 3), (0, 2), (1, 1), (1, 0)]]
    return group_table(elements, lambda x, y:
                       ((x[0] + y[0] + base[x[1]][y[1]][0]) % 2,
                        base[x[1]][y[1]][1]))


def heisenberg(p):
    elements = list(itertools.product(range(p), repeat=3))
    return group_table(elements, lambda x, y:
                       ((x[0] + y[0]) % p, (x[1] + y[1]) % p,
                        (x[2] + y[2] + x[0] * y[1]) % p))


GROUPS = {
    **{f"D{n}": lambda n=n: semidirect(n // 2, 2, n // 2 - 1)
       for n in (8, 12, 16, 20, 28, 32)},
    "Q8": quaternion,
    "A4": lambda: permutation_group(4, True),
    "S4": lambda: permutation_group(4, False),
    "F20": lambda: semidirect(5, 4, 2),
    "F21": lambda: semidirect(7, 3, 2),
    "F39": lambda: semidirect(13, 3, 3),
    "F42": lambda: semidirect(7, 6, 3),
    "H27": lambda: heisenberg(3),
}


def probe(name, conflicts):
    g = GROUPS[name]()
    n = len(g)
    inv = [next(y for y in range(n) if g[x][y] == 0) for x in range(n)]
    assert all(g[0][x] == g[x][0] == x for x in range(n))
    assert all(g[g[x][y]][z] == g[x][g[y][z]]
               for x in range(n) for y in range(n) for z in range(n))

    def v(x, y):
        return 1 + n * x + y  # f(x)=y

    clauses, top = [], n * n
    # f is a permutation; f(x)*x^-1 is also a permutation. Both are
    # necessary consequences of E125, proved in the Lean module cited above.
    rows = ([[v(x, y) for y in range(n)] for x in range(n)]
            + [[v(x, y) for x in range(n)] for y in range(n)]
            + [[v(x, g[y][x]) for x in range(n)] for y in range(n)])
    for row in rows:
        cnf = CardEnc.equals(row, bound=1, top_id=top, encoding=EncType.seqcounter)
        clauses.extend(cnf.clauses)
        top = cnf.nv
    for x in range(n):
        for a in range(n):
            for b in range(n):
                clauses.append([-v(x, a), -v(inv[a], b), v(g[b][a], x)])
    for a in range(n):
        for b in range(n):
            if g[a][b] == g[b][a]:
                clauses.append([-v(0, a), -v(a, b)])

    start = time.monotonic()
    with Cadical195(bootstrap_with=clauses) as solver:
        solver.conf_budget(conflicts)
        status = solver.solve_limited()
        result = {"group": name, "order": n,
                  "status": "SAT" if status else "UNSAT" if status is False else "UNKNOWN",
                  "evidence": "solver_only", "conflict_budget": conflicts,
                  "seconds": time.monotonic() - start, "stats": solver.accum_stats()}
        if status:
            model = set(solver.get_model())
            f = [next(y for y in range(n) if v(x, y) in model) for x in range(n)]
            m = [[g[f[g[y][inv[x]]]][x] for y in range(n)] for x in range(n)]
            assert all(x == m[y][m[m[y][x]][y]] for x in range(n) for y in range(n))
            assert g[f[0]][f[f[0]]] != g[f[f[0]]][f[0]]
            result.update(f=f, group_table=g, magma_table=m)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--groups", nargs="+", choices=GROUPS, default=["D8", "Q8", "A4"])
    parser.add_argument("--conflicts", type=int, default=200000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.conflicts <= 0:
        parser.error("--conflicts must be positive")
    results = []
    for name in args.groups:
        result = probe(name, args.conflicts)
        results.append(result)
        print(json.dumps({k: v for k, v in result.items()
                          if k not in ("f", "group_table", "magma_table")}), flush=True)
        args.output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
