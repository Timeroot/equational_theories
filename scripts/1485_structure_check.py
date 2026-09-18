#!/usr/bin/env python3
"""Finite-table regression checks for docs/1485_graph_research.md.

These checks do not prove the general results or exhaust any model order.
With no arguments, check two Boolean-derived models of order 32.
Arguments may be Kevin M's n8_unique.txt or Mace4 portable JSON model banks.
Only the standard library is used; inputs are read, never modified.
"""

import argparse
from math import comb
from collections import Counter
import json
from itertools import permutations, product
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


def rectangular_boolean32():
    """Boolean NAND on eight points times the four-point rectangle.

    The rectangle law is (a,b)*(c,d)=(b,c). This example exercises the
    four-degree theorem at minimum degree two, unlike twisted32().
    """
    return [[4 * (7 ^ ((x // 4) & (y // 4))) + 2 * (x % 2) + (y % 4) // 2
             for y in range(32)] for x in range(32)]


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def check_central_incidence_obstruction():
    """Check the explicit incidence diagram, not an E1485 operation table."""
    pred = [{0, 3}, {0}, {0, 3}, {1}, {2}, {1, 2}, {1, 2}, {3}]
    succ = [{0}, {1, 3}, {2}, {0, 2}, {0, 2}, {3}, {1}, {1, 3}]
    top_rows = [{0, 2, 7}, {1, 3}, {4, 5, 6}, {4, 7},
                {4, 7}, {0, 1, 2}, {3, 5, 6}, {1, 3}]
    b = [[int(i in pred[t]) for t in range(8)] for i in range(4)]
    c = [[int(i in succ[t]) for i in range(4)] for t in range(8)]
    d = [[int(u in top_rows[t]) for u in range(8)] for t in range(8)]
    assert all(sum(row) == 3 for row in b)
    assert all(sum(col) == 3 for col in zip(*c))
    assert matmul(b, c) == [[1] * 4 for _ in range(4)]
    assert all(v <= 1 for row in matmul(c, b) for v in row)
    assert matmul(b, d) == [[1] * 8 for _ in range(4)]
    assert matmul(d, c) == [[1] * 4 for _ in range(8)]
    for t in range(8):
        assert len(pred[t]) + sum(d[u][t] for u in range(8)) == 4
        assert len(succ[t]) + len(top_rows[t]) == 4


def check_infinite_central_seeds():
    """Finite certificates for two infinite counterexamples, not models."""
    base_rows = [{0, 1, 4}, {0, 1, 3}, {2, 3, 4}, {0, 2}, {1, 2}]
    bad = {(0, 0, 0), (0, 0, 1), (0, 1, 1),
           (1, 0, 0), (1, 1, 0), (1, 1, 1)}
    good = {(a, b, c) for a, b, c in product(range(5), repeat=3)
            if b in base_rows[a] and c in base_rows[b] and (a, b, c) not in bad}
    assert all(any((a, b, c) in good for b in range(5))
               for a, c in product(range(5), repeat=2))
    for a, b, c, d, e in product(range(5), repeat=5):
        if (a, b, c) in good and (c, d, e) in good and a in base_rows[e]:
            assert (b, c, d) in good
    # H,K,A,X,C,B,T,U,A1,B1; every listed edge is in a product path.
    colors = [3, 2, 0, 0, 4, 0, 0, 1, 1, 4]
    triples = [(3, 4, 1), (2, 5, 4), (0, 6, 2),
               (5, 7, 0), (6, 8, 5), (2, 9, 7)]
    edges = {(a, b) for a, b, c in triples} | {(b, c) for a, b, c in triples}
    assert all((colors[a], colors[b], colors[c]) in good for a, b, c in triples)
    for a, c in product(range(10), repeat=2):
        assert sum((a, b) in edges and (b, c) in edges
                   and (colors[a], colors[b], colors[c]) in good
                   for b in range(10)) <= 1
    assert all(colors[h] not in triple for h in (0, 1) for triple in bad)
    assert colors[9] not in base_rows[colors[8]]
    # A smaller seed refutes centrality of S(h*k) for central h,k
    # without finiteness. Its vertices have their own labels as colors.
    square_edges = {(2, 3), (3, 0), (0, 4), (4, 2), (0, 0), (0, 1), (1, 0)}
    square_good = {(a, b, c) for a, b, c in good
                   if (a, b) in square_edges and (b, c) in square_edges}
    assert all(sum((a, b, c) in square_good for b in range(5)) <= 1
               for a, c in product(range(5), repeat=2))
    assert square_edges == ({(a, b) for a, b, c in square_good}
                            | {(b, c) for a, b, c in square_good})
    assert (3, 0, 4) in square_good and (0, 1, 0) in square_good
    assert (1, 0, 0) in bad
    assert all(h not in triple for h in (3, 4) for triple in bad)


def check_twelve_coordinate_lemma():
    """Check the small binary lemma, not all order-twelve tables.

    See docs/1485_order_twelve.md for the proof and the derivation of
    these necessary coordinate constraints from a hypothetical magma.
    """
    pairs = list(product(range(2), repeat=2))
    survivors = 0
    for bits in product(range(2), repeat=10):
        alpha = bits[:2]
        gamma = [bits[2:4], bits[4:6]]
        delta = [bits[6:8], bits[8:10]]
        p = lambda a, t: t[0] == a[1] ^ gamma[a[0]][t[1]]
        q = lambda t, a: t[1] == a[0] ^ delta[a[1]][t[0]]
        if any(sum(p(a, t) and q(t, b) for t in pairs) != 1
               for a in pairs for b in pairs):
            continue
        if any(sum(q(t, a) and p(a, u) for a in pairs) != 1
               for t in pairs for u in pairs):
            continue
        valid = True
        for i, j, k in product(range(2), repeat=3):
            first = [(k ^ alpha[v], v) for v in range(2)
                     if q((k ^ alpha[v], v), (i, j))]
            second = [t for t in pairs
                      if p((i, j), t) and q(t, (1 ^ j, k))]
            # B_k*A_ij has a unique top middle, and E1485 cannot
            # return a central vertex when its required result is A_ij.
            if len(first) != 1 or first[0][1] == second[0][0]:
                valid = False
                break
        if not valid:
            continue
        survivors += 1
        assert len(set(delta[0] + delta[1])) == 1
        assert all(gamma[i][j] == i ^ j for i, j in pairs)
        for beta in pairs:
            # A*B has a unique top middle.
            if not all(sum(p(a, t) and t[1] == k ^ beta[t[0]] for t in pairs) == 1
                       for a in pairs for k in range(2)):
                continue
            assert beta[0] == beta[1]
            b, d = beta[0], delta[0][0]
            # The two final W instances have central results when
            # b=d and when b!=d, respectively.
            assert b == d or (1 ^ b) == d
    assert survivors == 8

    # The other order-twelve case forces this reverse path matrix.
    # Its forward product has rank two, so the nonzero determinant is
    # the contradiction. Check every possible permutation and entry.
    forced = 0
    for sigma in permutations(range(3)):
        for exceptional in product(range(3), repeat=3):
            if sum(exceptional) != 4:
                continue
            matrix = [[exceptional[i] if j == sigma[i] else 1 for j in range(3)]
                      for i in range(3)]
            if sum(matrix[i][i] for i in range(3)) != 2:
                continue
            forced += 1
            a, b, c = matrix
            determinant = (a[0] * (b[1]*c[2] - b[2]*c[1])
                           - a[1] * (b[0]*c[2] - b[2]*c[0])
                           + a[2] * (b[0]*c[1] - b[1]*c[0]))
            assert determinant == 2
    assert forced == 3  # The three relabelings of the same matrix.

    # Global r=2,m=2 exclusion: one good extension/predecessor in each
    # central transversal forces both top neighborhoods to be parities.
    for bits in product(range(2), repeat=4):
        pred = [(0, bits[0]), (1, bits[1])]
        succ = [(bits[2], 0), (bits[3], 1)]
        good = [[p[1] != q[0] for q in succ] for p in pred]
        if all(sum(row) == 1 for row in good) and all(
                sum(good[i][j] for i in range(2)) == 1 for j in range(2)):
            assert bits[0] != bits[1] and bits[2] != bits[3]


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
    assert len(central) != lo * lo - 1  # The finite one-missing-vertex theorem.
    central_defect = lo * lo - len(central)
    assert central_defect == 0 or central_defect >= lo + 1
    if central_defect:
        excess = central_defect - lo
        assert excess * (excess + 1) >= lo - 1
    top = {a for a in m if d[a] == hi}
    if lo == 3 and len(central) == 5:
        assert len(top) == 9  # The five-central/ten-top exclusion and moments.
        assert Counter((len(cols[t] & central), len(rows[t] & central))
                       for t in top) == {(1, 1): 1, (1, 2): 2,
                                         (2, 1): 2, (2, 2): 4}
    assert not (lo == 3 and len(central) == 4 and len(top) == 8)
    if lo == 3 and len(central) == 4:
        assert len(top) in (9, 10)
        assert all(len(cols[t] & central) <= 2
                   and len(rows[t] & central) <= 2 for t in top)
    if len(central) == lo and len(degrees) > 1:
        next_degree = min(degree for degree in degrees if degree > lo)
        sharp_count = next_degree - lo
        assert lo % sharp_count == 0
        if sharp_count < lo:
            assert sum(degree == next_degree for degree in d) <= (
                lo * lo * (lo - 1) // (lo - sharp_count))
    for a in m:
        assert {f[z][a] for z in central} == cols[a] & top
        assert {f[a][z] for z in central} == rows[a] & top
    asymmetric_central = sum(f[a][b] in central and f[b][a] not in central
                             for a in top for b in top)
    assert asymmetric_central == len(central) * (lo * lo - len(central))
    central_top_squares = {t for t in top if square[t] in central}
    assert central_top_squares == {square[z] for z in central}
    assert len(central_top_squares) == len(central)
    if len(degrees) > 1:
        next_degree = min(degree for degree in degrees if degree > lo)
        for a in m:
            if d[a] == next_degree:
                sharp_in = sum(a in sharp[b] for b in m)
                assert sharp_in == len(sharp[a])
                k = sharp_in
                assert len(rows[a] & top) == len(cols[a] & top) == next_degree - k
                assert sum(f[t][u] == a for t in top for u in top) == (
                    next_degree - k) * (lo - k)
    # A central vertex supplies an r-regular spanning subrelation of
    # ordinary adjacency. Sharp regularity without a full core remains open.
    defect = sum(d) - sum(n // degree for degree in d)
    assert defect >= 0
    for h in central:
        shadow = [{f[a][c] for c in cols[h]} for a in m]
        assert all(len(row) == lo for row in shadow)
        assert all(sum(u in row for row in shadow) == lo for u in m)
        assert all(sharp[a] <= shadow[a] <= rows[a] for a in m)
        assert sum(d[a] - n // d[u] for a in m for u in shadow[a]) == lo * defect
        assert (defect == 0) == (shadow == sharp)
        for a in m:
            for b in m:
                a1, b1 = f[f[h][a]][b], f[a][f[b][h]]
                assert (f[f[h][a1]][b1], f[a1][f[b1][h]]) == (a, b)
                assert ((a1, b1) == (a, b)) == (b in shadow[a])
                if b in rows[a]:
                    assert (b1 in rows[a1]) == (b in shadow[a])
        # In central coordinates each ordinary block is unipotent.
        # This test needs no full-core hypothesis.
        assert set.union(*(rows[t] for t in rows[h])) == set(m)
        assert set.union(*(cols[u] for u in cols[h])) == set(m)
        for t in rows[h]:
            assert rows[t] == {x for x in m if f[h][x] == t}
            for u in cols[h]:
                assert cols[u] == {x for x in m if f[x][h] == u}
                assert f[u][t] == h
                phi = {a: f[a][u] for a in rows[t]}
                assert set(phi.values()) == cols[u]
                assert all(f[t][phi[a]] == a for a in rows[t])
                for a in rows[t]:
                    assert phi[a] in rows[a] & shadow[a]
                    assert rows[a] & shadow[a] & cols[u] == {phi[a]}
                    for x in rows[t]:
                        if a != x and phi[x] in rows[a]:
                            assert d[x] < d[a] and d[phi[a]] < d[phi[x]]
    if len(central) == lo * lo:
        # Conditional theorem, unconditional at lo=2: maximum-degree
        # translations are mutual inverses on their images, and all
        # central auxiliary relations are one canonical relation.
        top = {a for a in m if d[a] == hi}
        assert len(top) == lo * lo
        assert n != 6 * lo * lo
        canonical = [{f[a][t] for t in top} for a in m]
        # Full core now forces sharp regularity, without a degree-count bound.
        assert canonical == sharp
        predecessors = [{a for a in m if b in canonical[a]} for b in m]
        for a in m:
            assert len(canonical[a]) == lo
            assert all(canonical[a] == {f[a][c] for c in cols[h]} for h in central)
            assert {b for b in m if a in canonical[b]} == {f[t][a] for t in top}
            for t in top & cols[a]:
                assert canonical[a] == {x for x in m if f[t][x] == a}
            for u in top:
                assert len(canonical[a] & cols[u]) == 1
            if lo == 2:
                b, c = sorted(canonical[a], key=lambda x: d[x])
                assert d[b] == n // d[a]
                assert len(rows[b] | rows[c]) == 2 * d[b]
                assert len(rows[b] & rows[c]) == d[c] - d[b]
            assert not (lo < d[a] < 2 * lo or 2 * lo < d[a] < 3 * lo)
            if d[a] in (2 * lo, 3 * lo):
                assert len(sharp[a]) == lo
                assert sum(a in sharp[b] for b in m) == lo
            for b in rows[a]:
                is_auxiliary = b in canonical[a]
                good = {c for c in rows[b] if f[a][c] == b}
                assert len(good - top) == n // d[a] - lo * is_auxiliary
                if not is_auxiliary:
                    assert n // d[a] <= d[b] - lo
                    assert n // d[b] <= d[a] - lo
        if hi > lo:
            assert 2 * lo in degrees and n % (2 * lo) == 0
        for t in top:
            for u in top:
                assert f[t][u] in central
                assert all(f[t][f[f[t][x]][u]] == f[t][x] for x in m)
                assert all(f[f[t][f[x][u]]][u] == f[x][u] for x in m)
                assert all(f[f[t][x]][f[x][u]] == x for x in m)
        for y in m:
            for x in rows[y]:
                # The middle edge is ordinary, not necessarily canonical.
                rectangle = set(product(canonical[x], predecessors[y]))
                coordinates = {(f[x][u], f[u][y]) for u in top}
                assert coordinates == rectangle
                for a, b in rectangle:
                    assert f[a][b] in top
                    assert rows[a] & cols[b] == {f[a][b]}
        c_matrix = [[int(b in canonical[a]) for b in m] for a in m]
        c2 = matmul(c_matrix, c_matrix)
        assert all(entry in (0, 1) for row in c2 for entry in row)
        assert set(Counter(tuple(row) for row in c2).values()) == {lo * lo}
        supports = {frozenset(i for i, entry in enumerate(row) if entry) for row in c2}
        assert all(a == b or a.isdisjoint(b) for a in supports for b in supports)
        assert n % (lo * lo) == 0
        blocks = {tuple(row): frozenset(a for a in m if c2[a] == row)
                  for row in c2}
        block_of = {a: block for block in blocks.values() for a in block}
        sigma = {}
        for block in blocks.values():
            targets = {block_of[b] for a in block for b in canonical[a]}
            assert len(targets) == 1
            sigma[block] = targets.pop()
        assert len(set(sigma.values())) == len(sigma)
        for block in sigma:
            target = block
            for _ in range(10):
                target = sigma[target]
            assert target == block
        if lo < hi:
            assert n % (2 * lo * lo) == 0
        c3 = matmul(c2, c_matrix)
        assert all(entry in (0, lo) for row in c3 for entry in row)
        c5 = matmul(c3, c2)
        assert sum(c5[i][i] for i in m) == (0 if lo < hi else n * lo**3)
        ordinary = [[int(b in rows[a]) for b in m] for a in m]
        cac = matmul(matmul(c_matrix, ordinary), c_matrix)
        assert cac == [[lo * int(f[b][a] in top) for b in m] for a in m]
        block_list = list(blocks.values())
        quotient_size = len(block_list)
        assert quotient_size & (quotient_size - 1) == 0
        atoms = quotient_size.bit_length() - 1
        assert Counter(d) == Counter({lo * 2**j: lo**2 * comb(atoms, j)
                                      for j in range(atoms + 1)})
        for source in block_list:
            for target in block_list:
                row_counts = {len(rows[a] & target) for a in source}
                col_counts = {len(cols[b] & source) for b in target}
                assert row_counts == col_counts
                assert row_counts in ({0}, {lo})
                product_blocks = {block_of[f[a][b]] for a in source for b in target}
                assert len(product_blocks) == 1
                middle = product_blocks.pop()
                assert all(rows[a] & cols[b] & middle == {f[a][b]}
                           for a in source for b in target)
    for threshold in degrees:
        assert sum(degree >= threshold for degree in d) >= sum(
            n // degree >= threshold for degree in d)
    if lo == 2:
        top = {a for a in m if d[a] == hi}
        assert len(top) == 4
        assert all(len(rows[a] & top) == len(cols[a] & top) == 2 for a in m)
        incidence = Counter((len(cols[a] & central), len(rows[a] & central))
                            for a in top)
        assert incidence == {
            2: Counter({(1, 1): 4}),
            3: Counter({(1, 1): 1, (1, 2): 1, (2, 1): 1, (2, 2): 1}),
            4: Counter({(2, 2): 4}),
        }[len(central)]
        assert d.count(3) <= 8 - 2 * len(central)
        assert (len(central) == 4) == (3 not in d)
        assert len(central) == 4
        assert all(len(sharp[a]) == 2 for a in m if d[a] == 4)
        if len(central) == 4:
            core = central | top
            outside = set(m) - core
            assert all(f[a][b] in core for a in core for b in core)
            assert all(f[t][x] in outside and f[x][t] in outside
                       for t in top for x in outside)
            assert all(d[x] >= 4 for x in outside)
        # The cyclic-block theorem now proves the cycle bound and all
        # mate commutation. Keep the two bipartite sides distinct.
        unseen = set(m)
        short_cycles = True
        while unseen:
            left, right = {next(iter(unseen))}, set()
            while True:
                next_right = set.union(*(canonical[a] for a in left))
                next_left = {a for a in m if canonical[a] & next_right}
                if (next_left, next_right) == (left, right):
                    break
                left, right = next_left, next_right
            assert len(left) == len(right) and len(left) % 2 == 0
            for side in (left, right):
                for h in central:
                    assert len({(f[h][x], f[x][h]) for x in side}) == len(side)
            unseen -= left
            short_cycles &= len(left) <= 4
        assert short_cycles
        left_mates = {t: [next(y for y in m if y != x and f[t][y] == f[t][x])
                          for x in m] for t in top}
        right_mates = {t: [next(y for y in m if y != x and f[y][t] == f[x][t])
                           for x in m] for t in top}
        for mates in (left_mates, right_mates):
            commute = all(mates[t][mates[u][x]] == mates[u][mates[t][x]]
                          for t in top for u in top for x in m)
            assert commute == short_cycles
        assert all(left_mates[t][right_mates[u][x]] ==
                   right_mates[u][left_mates[t][x]]
                   for t in top for u in top for x in m)
        for t in top:
            for u in top:
                for x in m:
                    assert {x, left_mates[t][x], right_mates[u][x],
                            left_mates[t][right_mates[u][x]]} == block_of[x]
        for h in central:
            for x in m:
                other = next(c for c in cols[h] if c != f[x][h])
                for t in rows[h]:
                    assert left_mates[t][x] == f[f[t][x]][other]
        distinct_top_rows = len({frozenset(rows[t] & top) for t in top}) == 4
        for a in m:
            for b in canonical[a]:
                bad = sum(f[a][c] != b for c in canonical[b])
                assert bad <= 1
                if distinct_top_rows:
                    assert bad == 0
    for a in m:
        assert sum(n // d[u] for u in rows[a]) == sum(n // d[v] for v in cols[a])
        fixed = {u: {b for b in m if f[a][f[u][b]] == u} for u in rows[a]}
        for u in rows[a]:
            assert len(fixed[u]) * d[a] * d[u] == n * n
            for b in m:
                v = f[a][f[u][b]]
                assert fixed[u] <= fixed[v]
                assert v == u or d[v] < d[u]

    if len(degrees) == 4 and len(central) == lo * lo:
        small, twice_small, middle, largest = sorted(degrees)
        assert twice_small == 2 * small and largest == 2 * middle
        lower = [a for a in m if d[a] == twice_small]
        higher = [a for a in m if d[a] == middle]
        p = [[int(b in rows[a]) for b in higher] for a in lower]
        q = [[int(a in rows[b]) for a in lower] for b in higher]
        internal = [[int(b in rows[a]) for b in higher] for a in higher]
        relation = [[int(b in canonical[a]) for b in higher] for a in higher]
        counts = [len(sharp[a]) for a in higher]
        defects = [lo - count for count in counts]
        k = matmul(q, p)
        e = [[int(d[f[a][b]] == middle) for b in higher] for a in higher]
        g = [[int(d[f[a][b]] == largest) for b in higher] for a in higher]
        internal_squared = matmul(internal, internal)
        bad = [[total - good for total, good in zip(row, good_row)]
               for row, good_row in zip(internal_squared, e)]
        pd, dq = matmul(p, internal), matmul(internal, q)
        pr, rq = matmul(p, relation), matmul(relation, q)
        assert all(entry in (0, 1) for row in pd + dq + k + pr + rq for entry in row)
        for i, row in enumerate(k):
            for j, entry in enumerate(row):
                assert entry + e[i][j] + g[i][j] == 1
                assert bad[i][j] >= 0 and (not bad[i][j] or entry)
                assert not g[i][j] or counts[i] + counts[j] <= lo
        # These identities do not assume sharp regularity. See the
        # full-core four-degree top-return note for their fiber proof.
        assert matmul(p, k) == [[(1 - dq[j][i]) * counts[j]
                                 for j in range(len(higher))]
                                for i in range(len(lower))]
        assert matmul(p, e) == [[lo * (dq[j][i] - rq[j][i])
                                 + (1 - dq[j][i]) * defects[j]
                                 for j in range(len(higher))]
                                for i in range(len(lower))]
        assert matmul(p, g) == [[lo * x for x in col] for col in zip(*rq)]
        assert matmul(g, q) == [[lo * x for x in col] for col in zip(*pr)]
        assert matmul(relation, k) == [[g[j][i] * counts[j]
                                        for j in range(len(higher))]
                                       for i in range(len(higher))]
        assert matmul(k, relation) == [[counts[i] * g[j][i]
                                        for j in range(len(higher))]
                                       for i in range(len(higher))]
        pq = matmul(p, q)
        assert matmul(pd, q) == [[lo * (1 - x) for x in col] for col in zip(*pq)]
        dk2 = matmul(internal, matmul(k, k))
        dfk = matmul(internal, matmul(bad, k))
        assert sum(dk2[i][i] for i in range(len(higher))) == 0
        assert sum(dfk[i][i] for i in range(len(higher))) == 0
        assert all(count == lo for count in counts) or all(count < lo for count in counts)
        if lo <= 6 or len(set(counts)) == 1:
            assert all(count == lo for count in counts)
        if all(len(s) == lo for s in sharp):
            assert middle == 4 * lo and n == 8 * lo * lo
            assert matmul(e, q) == [[lo * x for x in col] for col in zip(*pd)]
            assert matmul(p, e) == [[lo * x for x in col] for col in zip(*dq)]

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
    check_central_incidence_obstruction()
    print("Central-incidence obstruction: exact matrix and balance checks passed.")
    check_infinite_central_seeds()
    print("Two central-parameter infinite-counterexample certificates passed.")
    check_twelve_coordinate_lemma()
    print("Order-twelve binary-coordinate lemma: all 1,024 bit assignments checked.")
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
    cases = [("twisted Boolean", [twisted32()]),
             ("Boolean times rectangle", [rectangular_boolean32()])]
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
