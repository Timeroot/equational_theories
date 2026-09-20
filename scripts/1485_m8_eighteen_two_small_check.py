#!/usr/bin/env python3
"""Exclude the m=8,h=18,a=8,q=2 central profile by a small exact check.

Two normalized double-partition grids; 200 complete central fixtures;
none admits a three-element first-output profile. Standard library only.
See docs/1485_order_forty_eight_central_eighteen_two_small.md.
"""

import argparse
from collections import Counter
from itertools import combinations, permutations, product
from time import perf_counter


N = 8
LABELS = (1 << N) - 1
CELLS = (1 << (N * N)) - 1


def mask(xs):
    return sum(1 << x for x in xs)


PAIRS = tuple(mask(xs) for xs in combinations(range(N), 2))
TRIPLES = tuple(mask(xs) for xs in combinations(range(N), 3))
EXPECTED_TYPES = Counter({(1, 1): 8, (2, 2): 2, (2, 3): 4, (3, 2): 4})
EXPECTED_COUNTS = ((4488, 1432, 40), (7344, 4224, 160))
FIXTURE = ((3, 88), (12, 22), (48, 133), (192, 97),
           (11, 129), (194, 6), (176, 24), (44, 96), (17, 34), (68, 136),
           (1, 4), (2, 32), (4, 1), (8, 8),
           (16, 64), (32, 2), (64, 16), (128, 128))


def rectangle(P, C):
    return sum(C << (N * x) for x in range(N) if P >> x & 1)


def double_complements(multiplicity):
    """All unordered pairs of two-sets with exactly this incidence sum.

    Repeated blocks ARE allowed. No disjointness is assumed.
    """
    if any(value < 0 or value > 2 for value in multiplicity):
        return ()
    answers = []
    for first in PAIRS:
        rest = tuple(multiplicity[x] - (first >> x & 1) for x in range(N))
        if any(value not in (0, 1) for value in rest) or sum(rest) != 2:
            continue
        second = mask(x for x in range(N) if rest[x])
        if first <= second:
            answers.append((first, second))
    return tuple(answers)


def grids(kind):
    A = tuple(mask((2 * i, 2 * i + 1)) for i in range(4))
    if kind == 0:
        B = tuple(mask((2 * j, 2 * ((j - 1) % 4) + 1)) for j in range(4))
    else:
        assert kind == 1
        B = (mask((0, 2)), mask((1, 3)), mask((4, 6)), mask((5, 7)))
    return A, B


def central_fixtures(kind):
    A, B = grids(kind)
    P_options = tuple(t for t in TRIPLES
                      if all((t & b).bit_count() <= 1 for b in B)
                      and sorted((t & a).bit_count() for a in A) == [0, 0, 1, 2])
    C_options = tuple(t for t in TRIPLES
                      if all((t & a).bit_count() <= 1 for a in A)
                      and sorted((t & b).bit_count() for b in B) == [0, 0, 1, 2])
    assert len(P_options) == len(C_options) == 16
    counts, fixtures = [0, 0, 0], []
    for P in product(P_options, repeat=4):
        if any(sum(bool(p & a) for p in P) != 2 for a in A):
            continue
        e = tuple(2 - sum(p >> x & 1 for p in P) for x in range(N))
        U = tuple(us for us in double_complements(e)
                  if all((u & b).bit_count() <= 1 for u in us for b in B))
        if not U:
            continue
        counts[0] += 1
        choices = [tuple(c for c in C_options
                         if all(not (P[j] & A[i]) or not (c & B[j]) for j in range(4))
                         and all((c & p).bit_count() == 1 for p in P))
                   for i in range(4)]
        for C in product(*choices):
            f = tuple(2 - sum(c >> x & 1 for c in C) for x in range(N))
            if any(e[x] * f[x] for x in range(N)):
                continue
            V = tuple(vs for vs in double_complements(f)
                      if all((v & a).bit_count() <= 1 for v in vs for a in A))
            if not V:
                continue
            counts[1] += 1
            large = [rectangle(A[i], C[i]) for i in range(4)]
            large += [rectangle(P[j], B[j]) for j in range(4)]
            used = 0
            for tile in large:
                assert not used & tile
                used |= tile
            assert used.bit_count() == 48
            for us, vs in product(U, V):
                if any((u & c).bit_count() != 1 for u in us for c in C):
                    continue
                if any((v & p).bit_count() != 1 for v in vs for p in P):
                    continue
                for successors in (vs, vs[::-1]):
                    first, second = (rectangle(u, v) for u, v in zip(us, successors))
                    if used & (first | second) or first & second:
                        continue
                    remainder = CELLS ^ (used | first | second)
                    if any(((remainder >> (N * x)) & LABELS).bit_count() != 1
                           for x in range(N)):
                        continue
                    if any(sum(remainder >> (N * x + y) & 1 for x in range(N)) != 1
                           for y in range(N)):
                        continue
                    tiles = [(A[i], C[i]) for i in range(4)]
                    tiles += [(P[j], B[j]) for j in range(4)]
                    tiles += list(zip(us, successors))
                    tiles += [(1 << x, (remainder >> (N * x)) & LABELS)
                              for x in range(N)]
                    counts[2] += 1
                    fixtures.append(tuple(tiles))
    assert len(fixtures) == len(set(fixtures))
    return tuple(counts), fixtures


def fast_profiles(tiles):
    candidates = []
    for side in (0, 1):
        candidates.append(tuple(indices for indices in combinations(range(len(tiles)), 3)
                                if sorted(tiles[i][side].bit_count() for i in indices) == [2, 3, 3]
                                and sum(tiles[i][side] for i in indices) == LABELS
                                and all(not (tiles[i][side] & tiles[j][side])
                                        for i, j in combinations(indices, 2))))
    good = []
    for U, V in product(*candidates):
        K = [[(tiles[i][1] & tiles[j][0]).bit_count() for j in V] for i in U]
        if all(sum(row) == 1 for row in K) and all(sum(K[i][j] for i in range(3)) == 1
                                                for j in range(3)):
            good.append((U, V))
    return tuple(candidates), tuple(good)


def as_sets(tiles):
    return tuple((frozenset(x for x in range(N) if P // (2 ** x) % 2),
                  frozenset(x for x in range(N) if C // (2 ** x) % 2))
                 for P, C in tiles)


def literal_central_valid(tiles):
    blocks = as_sets(tiles)
    if Counter((len(P), len(C)) for P, C in blocks) != EXPECTED_TYPES:
        return False
    if any(sum(x in P for P, C in blocks) != 4 or sum(x in C for P, C in blocks) != 4
           for x in range(N)):
        return False
    if any(sum(x in P and y in C for P, C in blocks) != 1
           for x, y in product(range(N), repeat=2)):
        return False
    if any(len(P & C) > 1 for P, _ in blocks for _, C in blocks):
        return False
    maximal_P = [P for P, C in blocks if len(P) == 3]
    maximal_C = [C for P, C in blocks if len(C) == 3]
    return (all(len(P & C) == 1 for P in maximal_P for C in maximal_C)
            and all(sum(x in P for P in maximal_P) <= 2
                    and sum(x in C for C in maximal_C) <= 2 for x in range(N)))


def literal_profiles(tiles):
    """All 3-subsets of the FULL top set, using sets and explicit matchings."""
    blocks = as_sets(tiles)
    candidates = []
    for side in (0, 1):
        choices = []
        for indices in combinations(range(len(blocks)), 3):
            parts = [blocks[i][side] for i in indices]
            if set.union(set(), *map(set, parts)) == set(range(N)) and all(
                    not (first & second) for first, second in combinations(parts, 2)):
                choices.append(indices)
        candidates.append(tuple(choices))
    good = []
    for U, V in product(*candidates):
        matching = [(i, j) for i in U for j in V if blocks[i][1] & blocks[j][0]]
        if (len(matching) == 3 and len({i for i, j in matching}) == 3
                and len({j for i, j in matching}) == 3
                and all(len(blocks[i][1] & blocks[j][0]) == 1 for i, j in matching)):
            good.append((U, V))
    return tuple(candidates), tuple(good)


def controls():
    # All labeled binary 4-by-4 matrices with row/column degree two are
    # row/column relabelings of precisely the two stated grid forms.
    orbits = []
    for kind in (0, 1):
        A, B = grids(kind)
        orbit = set()
        for rows, cols in product(permutations(range(4)), repeat=2):
            orbit.add(tuple(mask(j for j in range(4) if A[rows[i]] & B[cols[j]])
                            for i in range(4)))
        orbits.append(orbit)
    all_rows = tuple(mask(xs) for xs in combinations(range(4), 2))
    regular = {rows for rows in product(all_rows, repeat=4)
               if all(sum(row >> j & 1 for row in rows) == 2 for j in range(4))}
    assert tuple(map(len, orbits)) == (72, 18)
    assert not orbits[0] & orbits[1] and orbits[0] | orbits[1] == regular
    assert len(regular) == 90

    # The actual target central system is valid before requiring a first profile.
    assert literal_central_valid(FIXTURE)
    assert fast_profiles(FIXTURE) == literal_profiles(FIXTURE)
    assert tuple(map(len, fast_profiles(FIXTURE)[0])) == (2, 2)
    damaged = list(FIXTURE)
    damaged[0] = (1, damaged[0][1])
    assert not literal_central_valid(tuple(damaged))

    # A separate partial incidence fixture makes the profile oracle ACCEPT.
    # Three row/column groups of a 3-by-3 grid with one cell removed.
    rows = (mask((0, 1, 2)), mask((3, 4, 5)), mask((6, 7)))
    cols = (mask((0, 3, 6)), mask((1, 4, 7)), mask((2, 5)))
    partial = tuple((rows[i], 1 << i) for i in range(3))
    partial += tuple((1 << i, cols[i]) for i in range(3))
    fast, direct = fast_profiles(partial), literal_profiles(partial)
    assert fast == direct and ((0, 1, 2), (3, 4, 5)) in fast[1]

    # Every two-block incidence vector is recovered, including repeated pairs.
    for first, second in combinations(PAIRS, 2):
        counts = tuple((first >> x & 1) + (second >> x & 1) for x in range(N))
        assert tuple(sorted((first, second))) in double_complements(counts)
    for first in PAIRS:
        counts = tuple(2 * (first >> x & 1) for x in range(N))
        assert (first, first) in double_complements(counts)


def main():
    if not __debug__:
        raise SystemExit("Run without python -O: this checker needs its assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    started = perf_counter()
    controls()
    total, found_control = 0, False
    for kind in (0, 1):
        counts, fixtures = central_fixtures(kind)
        assert counts == EXPECTED_COUNTS[kind]
        for tiles in fixtures:
            assert literal_central_valid(tiles)
            fast, direct = fast_profiles(tiles), literal_profiles(tiles)
            assert fast == direct
            assert tuple(map(len, fast[0])) == (2, 2) and not fast[1]
            found_control |= tiles == FIXTURE
            if args.verbose:
                print("grid", kind, "tiles", tiles, "one-sided profiles", fast[0])
        total += len(fixtures)
        print(f"Grid {kind}: P families={counts[0]}; P/C families={counts[1]}; "
              f"central fixtures={counts[2]}; compatible first profiles=0")
    assert total == 200 and found_control
    print(f"PASS: 90 normalization controls; 200 independent central audits "
          f"and fast/direct profile comparisons; "
          f"elapsed {perf_counter() - started:.3f}s")


if __name__ == "__main__":
    main()
