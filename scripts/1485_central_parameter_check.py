#!/usr/bin/env python3
"""Finite-table regression for the central-parameter counting identities.

This is not an exhaustive model search or a proof of a general assertion.
The reverse-central-product lambda identity is reported separately as an
empirical candidate. Bank formats are those of 1485_structure_check.py.
No input files are modified; only the Python standard library is used.
"""

import argparse
from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from time import perf_counter


def load_structure_helpers():
    path = Path(__file__).with_name("1485_structure_check.py")
    spec = spec_from_file_location("structure_helpers", path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(f):
    n = len(f)
    points = range(n)
    assert n and all(len(row) == n for row in f)
    assert all(isinstance(x, int) and 0 <= x < n for row in f for x in row)
    assert all(f[f[y][x]][f[x][f[z][y]]] == x
               for x in points for y in points for z in points)
    rows = [set(row) for row in f]
    cols = [{f[x][y] for x in points} for y in points]
    degree = list(map(len, rows))
    assert degree == list(map(len, cols))
    r, s = min(degree), max(degree)
    assert r * s == n
    central = [h for h in points if degree[h] == r]
    top = [t for t in points if degree[t] == s]
    assert all(f[f[x][h]][f[h][y]] == h
               for h in central for x in points for y in points)

    edges = {
        h: {(a, f[a][v]) for a in points for v in cols[h]}
        for h in central
    }
    for h in central:
        assert len(edges[h]) == n * r
        assert edges[h] == {(f[t][b], b) for t in rows[h] for b in points}
        assert Counter(a for a, b in edges[h]) == dict.fromkeys(points, r)
        assert Counter(b for a, b in edges[h]) == dict.fromkeys(points, r)
        for a in points:
            for b in points:
                membership = int((a, b) in edges[h])
                assert sum(t in rows[h] and f[t][b] == a for t in top) == membership
                assert sum(v in cols[h] and f[a][v] == b for v in top) == membership

    central_pair_checks = 0
    for h in central:
        for k in central:
            intersection = len(edges[h] & edges[k])
            total_rank = 0
            for t in rows[h]:
                lam = [f[f[t][b]][f[b][k]] for b in points]
                assert all(lam[lam[b]] == lam[b] for b in points)
                rank = len(set(lam))
                assert rank == sum(lam[b] == b for b in points)
                assert all(n % degree[f[v][t]] == 0 for v in cols[k])
                assert rank == sum(n // degree[f[v][t]] for v in cols[k])
                total_rank += rank
            assert intersection == total_rank
            assert n * r - intersection == len(edges[h] ^ edges[k]) // 2

            shift = {
                (a, b): (b, f[b][f[f[h][a]][k]])
                for a, b in edges[h]
            }
            assert set(shift.values()) == edges[k]
            assert len(set(shift.values())) == len(edges[h])
            for (a, b), (c, d) in shift.items():
                assert (f[f[h][f[d][k]]][c], c) == (a, b)
            central_pair_checks += 1

    # This part is deliberately empirical: no general proof is asserted.
    reverse_central_tests = 0
    first_failure = None
    for t in top:
        for u in top:
            if f[u][t] not in central:
                continue
            reverse_central_tests += 1
            for x in points:
                if f[f[t][x]][f[x][u]] != x and first_failure is None:
                    first_failure = (t, u, x, f[u][t], f[f[t][x]][f[x][u]])
    return n, central_pair_checks, reverse_central_tests, first_failure


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("banks", nargs="*", type=Path)
    args = parser.parse_args()
    assert __debug__, "Run without -O: the regression checks use assertions."
    helpers = load_structure_helpers()
    cases = [("built-in models", [helpers.twisted32(),
                                  helpers.rectangular_boolean32(),
                                  helpers.rectangle9(),
                                  helpers.rectangular_boolean18()])]
    cases.extend((str(path), helpers.tables(path)) for path in args.banks)
    started = perf_counter()
    for name, bank in cases:
        assert bank, f"Empty bank: {name}"
        results = [check(f) for f in bank]
        print(f"{name}: {len(bank)} tables passed; orders "
              f"{dict(sorted(Counter(row[0] for row in results).items()))}; "
              f"{sum(row[1] for row in results)} central-pair checks", flush=True)
        failures = [(i, row[3]) for i, row in enumerate(results) if row[3] is not None]
        print("  Empirical reverse-central-product lambda identity: "
              f"{sum(row[2] for row in results)} top-pair tests; "
              f"counterexamples={failures}", flush=True)
    print(f"Elapsed: {perf_counter() - started:.3f}s")


if __name__ == "__main__":
    main()
