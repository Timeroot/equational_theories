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
from itertools import product
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
    degrees = set(d)
    assert {n // degree for degree in degrees} == degrees
    if len(degrees) % 2:
        assert any(degree * degree == n for degree in degrees)
    square = [f[x][x] for x in m]
    for x in m:
        assert set(Counter(f[x]).values()) == {n // d[x]}
        assert set(Counter(f[y][x] for y in m).values()) == {n // d[x]}
        assert square[square[square[x]]] == square[x]
        assert square[square[x]] == x or d[square[square[x]]] < d[x]
        for y in m:
            assert d[x] * d[f[x][y]] * d[y] <= n * n
            p = f[f[y][x]][f[x][y]]
            assert p == x or d[p] < d[x]
            for u in rows[x] & cols[y]:
                assert u == f[x][y] or d[u] > d[f[x][y]]

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
    for a in m:
        assert sum(n // d[u] for u in rows[a]) == sum(n // d[v] for v in cols[a])
        fixed = {u: {b for b in m if f[a][f[u][b]] == u} for u in rows[a]}
        for u in rows[a]:
            assert len(fixed[u]) * d[a] * d[u] == n * n
            for b in m:
                v = f[a][f[u][b]]
                assert fixed[u] <= fixed[v]
                assert v == u or d[v] < d[u]

    if len(set(d)) == 2:
        high = set(m) - central
        z, h = len(central), len(high)
        k = {v: len(rows[v] & central) for v in high}
        assert all(k[v] == len(cols[v] & central) for v in high)
        assert sum(k.values()) == z * lo
        assert sum(t * t for t in k.values()) == z * z
        assert h >= lo * lo and 4 * hi <= (lo + 2) ** 2
        assert hi == 2 * lo
        assert max(k.values()) <= hi - lo
        if len(set(k.values())) == 1 or lo <= 11:
            assert (hi, z, h, set(k.values())) == (2 * lo, lo * lo, lo * lo, {lo})
        delta, t = h - lo * lo, hi - lo
        mixed_cycles = t * (h * h - z * lo * lo)
        bb_good_return = t * sum((hi - v) * (t - v) for v in k.values())
        gg_bad_return = t * (h * hi * hi - 3 * hi * z * lo + 2 * z * z)
        assert gg_bad_return == bb_good_return + mixed_cycles
        assert bb_good_return == mixed_cycles
        assert bb_good_return - mixed_cycles == t * (t - lo) * (
            lo ** 3 + (t + 2 * lo) * delta)
        good_cycles = lo * (h * h - 2 * h * z + 2 * z * z - z * lo * lo)
        assert good_cycles >= 0
        for a in high:
            for b in rows[a] & high:
                assert sum(f[a][c] != b for c in rows[b] & high) == hi - lo
            for c in central:
                targets = {f[v][c] for v in rows[a] & central}
                assert len(targets) == k[a]
                assert sum(len(rows[a] & cols[v] & high) for v in targets) == hi - lo
        e = {(u, v) for u in high for v in high if f[u][v] in high}
        assert all(k[u] + k[v] <= lo for u, v in e)
        assert sum(lo - k[u] - k[v] for u, v in e) == good_cycles
        for u in high:
            assert sum(k[v] for v in high if (u, v) in e) == z * (lo - k[u])
            assert sum(k[v] > lo - k[u] for v in high) <= k[u] ** 2
            for v in high:
                assert sum((u, w) in e and (w, v) in e for w in high) == (
                    h - lo * (k[u] + k[v]) + k[u] * k[v])
        if lo == 2:
            assert (n, hi) == (8, 4)
        if lo > 1:
            assert min(k.values()) >= 2
            assert 8 * hi <= (lo + 4) ** 2
        if lo == 3:
            assert (n, hi) == (18, 6)

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
    # Pure cyclic-pattern checks used in the two five-cycle proofs.
    for bits in product(range(2), repeat=5):
        if any(bits[i] and not (bits[(i-1) % 5] or bits[(i+1) % 5])
               for i in range(5)):
            continue
        bg = sum(bits[i] and not bits[(i+1) % 5] for i in range(5))
        bb_g = sum(bits[i] and bits[(i+1) % 5] and not bits[(i+3) % 5]
                   for i in range(5))
        gg_b = sum(not bits[i] and not bits[(i+1) % 5] and bits[(i+3) % 5]
                   for i in range(5))
        assert bb_g - bg == int(sum(bits) == 3)
        assert gg_b - bb_g - bg == -2 * int(sum(bits) in (3, 4))
        if all(not (bits[i] and bits[(i+1) % 5]) or bits[(i+3) % 5]
               for i in range(5)):
            assert len(set(bits)) == 1
    assert [(r*r + 2*r - 4)**2 - 16*r*r*(r-2) for r in range(4, 10)] == [
        -112, -239, -368, -439, -368, -47]
    print("Five-cycle patterns and the r<=9 discriminant obstruction passed.")
    assert [320*j - 800 - 6*(j-2)*j*j for j in range(3, 7)] == [106, 288, 350, 256]
    assert [495*j - 1210 - 7*(j-2)*j*j for j in range(3, 9)] == [212, 546, 740, 752, 540, 62]
    assert [62**2 - (13*(11-j)+22)*62 + 484*(11-j) - 6*(j-3)*j*j
            for j in range(4, 8)] == [130, 248, 222, 16]
    assert [(m*m - 61*m + 1452) % 5 for m in range(5)] == [2, 2, 4, 3, 4]
    print("The r=10,11 tail-moment and congruence obstructions passed.")
    # Check the necessary bit equations used in the hand proof at order six.
    # This is not a search through all order-six multiplication tables.
    for bits in product(range(2), repeat=4):
        t = [bits[:2], bits[2:]]
        def diagonal_possible(i):
            return any(p == (1 ^ i ^ t[i][i])
                       and q == (1 ^ i ^ t[p][i])
                       and p == (i ^ t[i][q])
                       for p, q in product(range(2), repeat=2))
        assert not (diagonal_possible(0) and diagonal_possible(1))
    print("Order-six bit obstruction: all 16 necessary-pattern checks passed.")
    fifteen_patterns = set()
    for z in range(3, 10):
        h = 15 - z
        for c1, c2 in product(range(h + 1), repeat=2):
            c3 = h - c1 - c2
            if c3 < 0 or c1 + 2*c2 + 3*c3 != 3*z or c1 + 4*c2 + 9*c3 != z*z:
                continue
            counts = (c1, c2, c3)
            fifteen_patterns.add((z, counts))
            assert any(counts[k-1] and sum(counts[3-k:]) > k*k for k in range(1, 4))
    assert fifteen_patterns == {(5, (5, 5, 0)), (6, (0, 9, 0))}
    print("Order-fifteen moments: both possible patterns violate the five-cycle bound.")
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
