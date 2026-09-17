#!/usr/bin/env python3
"""Finite-table regression checks for docs/1485_graph_research.md.

These checks do not prove the general results or exhaust any model order.
With no arguments, check the cyclically twisted Boolean model of order 32.
Arguments may be Kevin M's n8_unique.txt or Mace4 portable JSON model banks.
Only the standard library is used; inputs are read, never modified.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import re


def tables(path):
    data = path.read_text()
    if data.lstrip().startswith("--- magma"):
        return [json.loads(t) for t in re.findall(r"\[\[.*?\]\]", data, re.S)]
    return [entry[2][0][3] for entry in json.loads(data)]


def twisted32():
    left = lambda x: ((x << 1) & 31) | (x >> 4)
    right = lambda x: (x >> 1) | ((x & 1) << 4)
    return [[31 ^ (left(x) & right(y)) for y in range(32)] for x in range(32)]


def check(f):
    n = len(f)
    m = range(n)
    assert n and all(len(row) == n for row in f)
    assert all(type(v) is int and v in m for row in f for v in row)
    assert all(f[f[y][x]][f[x][f[z][y]]] == x for x in m for y in m for z in m)
    rows = [set(row) for row in f]
    cols = [{f[x][y] for x in m} for y in m]
    d = [len(row) for row in rows]
    assert d == [len(col) for col in cols]
    lo, hi = min(d), max(d)
    assert lo * hi == n
    for x in m:
        assert set(Counter(f[x]).values()) == {n // d[x]}
        assert set(Counter(f[y][x] for y in m).values()) == {n // d[x]}

    sharp = [{a for a in m if all(f[e][f[a][x]] == a for x in m)} for e in m]
    assert all(sharp) and set.union(*sharp) == set(m)
    for e in m:
        for a in rows[e]:
            assert (a in sharp[e]) == (d[a] * d[e] == n)
            assert all(f[f[a][x]][f[x][e]] == x for x in m)
            if a in sharp[e]:
                # Verify the actual inverse maps, not just cardinalities.
                for u in rows[a]:
                    for v in cols[e]:
                        assert f[a][f[u][v]] == u and f[f[u][v]][e] == v

    central = {a for a in m if all(f[f[x][a]][f[a][y]] == a for x in m for y in m)}
    assert central == {a for a in m if d[a] == lo}
    observed_image_intersections = True
    for x in m:
        generator_images = set()
        for y in m:
            image = {f[x][f[t][y]] for t in m}
            assert image == {u for u in m if f[f[y][x]][u] == x}
            assert len(image) * d[f[y][x]] == n
            generator_images.add(frozenset(image))
        observed_image_intersections &= all(
            left & right in generator_images
            for left in generator_images for right in generator_images)

    # These further structural properties remain conjectural in general.
    observed_regular_sharp = all(len(s) == lo for s in sharp)
    observed_square_central = len(central) == lo * lo
    return n, observed_regular_sharp, observed_square_central, observed_image_intersections


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("banks", type=Path, nargs="*")
    args = parser.parse_args()
    cases = [("twisted Boolean", [twisted32()])]
    cases.extend((str(path), tables(path)) for path in args.banks)
    for name, bank in cases:
        assert bank, f"No tables found in {name}"
        results = [check(f) for f in bank]
        counts = dict(sorted(Counter(row[0] for row in results).items()))
        print(f"{name}: {len(bank)} tables passed; orders {counts}")
        print("  Empirical only: sharp-regular =", all(row[1] for row in results),
              "; central-square =", all(row[2] for row in results),
              "; image-intersections =", all(row[3] for row in results))


if __name__ == "__main__":
    main()
