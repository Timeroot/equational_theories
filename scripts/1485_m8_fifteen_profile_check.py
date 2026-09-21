#!/usr/bin/env python3
"""Check the fifteen-top, eight-central profile obstruction.

Standalone standard library; no solver. The default run exhausts all
69 normalized maximal-block families. Every complete central fixture is
checked independently with literal sets and a separate profile oracle.
"""

import argparse
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from time import perf_counter


def mask(xs):
    return sum(1 << x for x in xs)


N = 8
ALL = 255
FORBIDDEN_PROFILE_COUNT = 5
rows = (mask((0, 1, 2)), mask((3, 4, 5)), mask((6, 7)))
cols = (mask((0, 3, 6)), mask((1, 4, 7)), mask((2, 5)))
triples = tuple(mask(xs) for xs in combinations(range(8), 3))
popts = tuple(s for s in triples if all((s & c).bit_count() == 1 for c in cols))
copts = tuple(s for s in triples if all((s & r).bit_count() == 1 for r in rows))


def maximum_families():
    for pp in combinations_with_replacement(popts, 2):
        P = rows[:2] + pp
        e = tuple(2 - sum(p >> z & 1 for p in P) for z in range(N))
        if min(e) < 0:
            continue
        for cc in combinations_with_replacement(copts, 2):
            C = cols[:2] + cc
            if any((p & c).bit_count() != 1 for p in P for c in C):
                continue
            f = tuple(2 - sum(c >> z & 1 for c in C) for z in range(N))
            if min(f) < 0 or any(x * y for x, y in zip(e, f)):
                continue
            yield P, C


def canonical(P, C):
    forms = []
    for i, j in product(range(4), repeat=2):
        if i == j or P[i] & P[j]:
            continue
        R = (P[i], P[j], ALL ^ (P[i] | P[j]))
        for k, l in product(range(4), repeat=2):
            if k == l or C[k] & C[l]:
                continue
            S = (C[k], C[l], ALL ^ (C[k] | C[l]))
            images = {}
            target = 0
            for row, col in product(range(3), repeat=2):
                block = R[row] & S[col]
                if row == col == 2:
                    assert not block
                else:
                    assert block.bit_count() == 1
                    images[block.bit_length() - 1] = target
                    target += 1

            def transform(s, images=images):
                return sum(1 << images[z] for z in range(8) if s >> z & 1)

            forms.append(
                (tuple(sorted(map(transform, P))), tuple(sorted(map(transform, C))))
            )
    return min(forms)


CELLS = (1 << 64) - 1
TARGET = (1 << 72) - 1
PAIRS = tuple(mask(xs) for xs in combinations(range(8), 2))
PAIR_IDS = {s: i for i, s in enumerate(PAIRS)}
EXPECTED_TYPES = Counter({(1, 3): 2, (3, 1): 2, (2, 3): 2, (3, 2): 2, (2, 2): 7})
FIXTURE = (
    (66, 36),
    (5, 36),
    (136, 36),
    (48, 36),
    (7, 1),
    (7, 72),
    (8, 73),
    (56, 2),
    (56, 144),
    (48, 73),
    (192, 9),
    (192, 80),
    (192, 130),
    (1, 146),
    (6, 146),
)


def rectangle(p, c):
    return sum(c << (8 * z) for z in range(8) if p >> z & 1)


def candidates(P, C):
    ps = [1 << i for i in range(N)] + [
        s for s in PAIRS if all((s & c).bit_count() <= 1 for c in C)
    ]
    cs = [1 << i for i in range(N)] + [
        s for s in PAIRS if all((s & p).bit_count() <= 1 for p in P)
    ]
    out = []
    for j, p in enumerate(P):
        for c in cs:
            out.append(
                (
                    p,
                    c,
                    rectangle(p, c) | (1 << (64 + j)),
                    0 if c.bit_count() == 1 else 1,
                )
            )
    for i, c in enumerate(C):
        for p in ps:
            out.append(
                (
                    p,
                    c,
                    rectangle(p, c) | (1 << (68 + i)),
                    2 if p.bit_count() == 1 else 3,
                )
            )
    for p, c in product(ps[N:], cs[N:]):
        if p != c:
            out.append((p, c, rectangle(p, c), 4))
    return out


def fast_covers(P, C, node_limit, solution_limit, callback=None):
    options = candidates(P, C)
    columns = [0] * 72
    typemasks = [0] * 5
    prows = [0] * 8
    ccols = [0] * 8
    pairs_p = [0] * 28
    pairs_c = [0] * 28
    for k, (p, c, cover, typ) in enumerate(options):
        bit = 1 << k
        typemasks[typ] |= bit
        for z in range(72):
            if cover >> z & 1:
                columns[z] |= bit
        for z in range(8):
            if p >> z & 1:
                prows[z] |= bit
            if c >> z & 1:
                ccols[z] |= bit
        if p.bit_count() == 2:
            pairs_p[PAIR_IDS[p]] |= bit
        if c.bit_count() == 2:
            pairs_c[PAIR_IDS[c]] |= bit
    conflicts = []
    for p, c, cover, typ in options:
        forbidden = 0
        for z in range(72):
            if cover >> z & 1:
                forbidden |= columns[z]
        if p.bit_count() == 2:
            forbidden |= pairs_c[PAIR_IDS[p]]
        if c.bit_count() == 2:
            forbidden |= pairs_p[PAIR_IDS[c]]
        conflicts.append(forbidden)
    # Repeated maximal blocks have interchangeable top labels. Sort their
    # opposite blocks to keep one representative of these slot permutations.
    for i, (p, c, cover, typ) in enumerate(options):
        for j in range(i + 1, len(options)):
            pp, cc, cov2, _typ2 = options[j]
            a_slot = (cover >> 64) & 15
            b_slot = (cov2 >> 64) & 15
            bad = (
                p == pp
                and a_slot
                and b_slot
                and a_slot != b_slot
                and ((a_slot < b_slot and c >= cc) or (a_slot > b_slot and c <= cc))
            )
            a_slot = (cover >> 68) & 15
            b_slot = (cov2 >> 68) & 15
            bad |= (
                c == cc
                and a_slot
                and b_slot
                and a_slot != b_slot
                and ((a_slot < b_slot and p >= pp) or (a_slot > b_slot and p <= pp))
            )
            if bad:
                conflicts[i] |= 1 << j
                conflicts[j] |= 1 << i
    plabels = [[z for z in range(8) if p >> z & 1] for p, c, co, t in options]
    clabels = [[z for z in range(8) if c >> z & 1] for p, c, co, t in options]
    expected = (2, 2, 2, 2, 7)
    nodes = 0
    solutions = []
    interrupted = False
    complete_count = 0
    bits_order = list(range(64, 72)) + list(range(64))

    def rec(used, active, types, pr, cr, chosen):
        nonlocal nodes, interrupted, complete_count
        nodes += 1
        if nodes > node_limit or complete_count >= solution_limit:
            interrupted = True
            return
        if used == TARGET:
            if tuple(types) == expected and pr == [4] * 8 and cr == [4] * 8:
                complete_count += 1
                solution = tuple((options[k][0], options[k][1]) for k in chosen)
                if callback is None:
                    solutions.append(solution)
                elif callback(solution):
                    solutions.append(solution)
                    interrupted = True
            return
        best = 0
        bestsize = 10000
        for z in bits_order:
            if used >> z & 1:
                continue
            current = columns[z] & active
            count = current.bit_count()
            if not count:
                return
            if count < bestsize:
                best, bestsize = current, count
            if count == 1:
                break
        while best:
            bit = best & -best
            best ^= bit
            k = bit.bit_length() - 1
            _p, _c, cover, typ = options[k]
            tt = types.copy()
            tt[typ] += 1
            rr = pr.copy()
            ss = cr.copy()
            nxt = active & ~conflicts[k]
            if tt[typ] == expected[typ]:
                nxt &= ~typemasks[typ]
            for z in plabels[k]:
                rr[z] += 1
                if rr[z] == 4:
                    nxt &= ~prows[z]
            for z in clabels[k]:
                ss[z] += 1
                if ss[z] == 4:
                    nxt &= ~ccols[z]
            rec(used | cover, nxt, tt, rr, ss, chosen + [k])
            if interrupted:
                return

    rec(0, (1 << len(options)) - 1, [0] * 5, [0] * 8, [0] * 8, [])
    return nodes, solutions, interrupted, len(options), complete_count


def triples_inventory(tiles):
    sides = []
    n = len(tiles)
    for side in (0, 1):
        triples = [i for i in range(n) if tiles[i][side].bit_count() == 3]
        doubles = {}
        for i in range(n):
            s = tiles[i][side]
            if s.bit_count() == 2:
                doubles.setdefault(s, []).append(i)
        choices = []
        for i, j in combinations(triples, 2):
            if tiles[i][side] & tiles[j][side]:
                continue
            for k in doubles.get(255 ^ (tiles[i][side] | tiles[j][side]), []):
                choices.append(tuple(sorted((i, j, k))))
        sides.append(sorted(choices))
    profiles = []
    for U, V in product(*sides):
        K = [[bool(tiles[i][1] & tiles[j][0]) for j in V] for i in U]
        if any(sum(r) != 1 for r in K) or any(
            sum(K[i][j] for i in range(3)) != 1 for j in range(3)
        ):
            continue
        good = sum(
            1 << (i * n + j) for i in U for j in V if not (tiles[i][1] & tiles[j][0])
        )
        profiles.append((U, V, good))
    return sides, profiles


def compatibility(tiles, profiles):
    # Universal support bounds; only capacity-one entries are used.
    alpha = {(1, 3): 1, (3, 1): 4, (2, 3): 1, (3, 2): 3, (2, 2): 3}
    beta = {(1, 3): 4, (3, 1): 1, (2, 3): 3, (3, 2): 1, (2, 2): 3}
    types = [tuple(s.bit_count() for s in tile) for tile in tiles]
    n = len(profiles)
    adj = [0] * n
    for i, j in combinations(range(n), 2):
        U, V, G = profiles[i]
        UU, VV, GG = profiles[j]
        if G & GG:
            continue
        if any(alpha[types[k]] == 1 for k in set(U) & set(UU)):
            continue
        if any(beta[types[k]] == 1 for k in set(V) & set(VV)):
            continue
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def clique(adj, k):
    def rec(candidates, chosen):
        if len(chosen) == k:
            return chosen
        if candidates.bit_count() < k - len(chosen):
            return None
        while candidates:
            bit = candidates & -candidates
            candidates ^= bit
            i = bit.bit_length() - 1
            ans = rec(candidates & adj[i], chosen + [i])
            if ans is not None:
                return ans
        return None

    return rec((1 << len(adj)) - 1, [])


def literal_blocks(tiles):
    return tuple(
        (
            frozenset(z for z in range(8) if p // 2**z % 2),
            frozenset(z for z in range(8) if c // 2**z % 2),
        )
        for p, c in tiles
    )


def literal_valid(tiles):
    blocks = literal_blocks(tiles)
    if Counter((len(p), len(c)) for p, c in blocks) != EXPECTED_TYPES:
        return False
    if any(
        sum(z in p for p, c in blocks) != 4 or sum(z in c for p, c in blocks) != 4
        for z in range(8)
    ):
        return False
    if any(
        sum(x in p and y in c for p, c in blocks) != 1
        for x, y in product(range(8), repeat=2)
    ):
        return False
    if any(len(p & c) > 1 for p, _ in blocks for _, c in blocks):
        return False
    return all(
        len(p & c) == 1
        for p, _ in blocks
        if len(p) == 3
        for _, c in blocks
        if len(c) == 3
    )


def literal_inventory(tiles):
    blocks = literal_blocks(tiles)
    sides = []
    for side in (0, 1):
        choices = []
        for inds in combinations(range(len(tiles)), 3):
            parts = [blocks[i][side] for i in inds]
            if set().union(*parts) == set(range(8)) and all(
                not (p & q) for p, q in combinations(parts, 2)
            ):
                choices.append(inds)
        sides.append(choices)
    profiles = []
    for U, V in product(*sides):
        edges = [(u, v) for u in U for v in V if blocks[u][1] & blocks[v][0]]
        if (
            len(edges) == 3
            and len({u for u, v in edges}) == 3
            and len({v for u, v in edges}) == 3
            and all(len(blocks[u][1] & blocks[v][0]) == 1 for u, v in edges)
        ):
            good = mask(
                u * len(tiles) + v
                for u in U
                for v in V
                if not (blocks[u][1] & blocks[v][0])
            )
            profiles.append((U, V, good))
    return sides, profiles


def literal_compatible(tiles, profiles, size):
    # Independent direct subset test: do not reuse the bitset graph.
    blocks = literal_blocks(tiles)
    sources_one = {i for i, (p, c) in enumerate(blocks) if len(c) == 3}
    targets_one = {i for i, (p, c) in enumerate(blocks) if len(p) == 3}
    records = [
        (
            set(U),
            set(V),
            {(i, j) for i in U for j in V if not (blocks[i][1] & blocks[j][0])},
        )
        for U, V, _ in profiles
    ]
    for chosen in combinations(range(len(records)), size):
        ok = True
        for i, j in combinations(chosen, 2):
            U, V, G = records[i]
            UU, VV, GG = records[j]
            if G & GG or U & UU & sources_one or V & VV & targets_one:
                ok = False
                break
        if ok:
            return chosen
    return None


def controls():
    raw = list(maximum_families())
    assert len(popts) == len(copts) == 18 and len(raw) == 324
    representatives = {canonical(P, C): (P, C) for P, C in raw}
    assert len(representatives) == 69
    # Adjacent transpositions generate all central relabelings. Check
    # canonical invariance on every raw family for all seven generators.
    for P, C in raw:
        normal = canonical(P, C)
        for x in range(7):

            def swap(s, x=x):
                first, second = (s >> x) & 1, (s >> (x + 1)) & 1
                return s ^ ((first ^ second) * ((1 << x) | (1 << (x + 1))))

            assert canonical(tuple(map(swap, P)), tuple(map(swap, C))) == normal
    assert literal_valid(FIXTURE)
    damaged = list(FIXTURE)
    damaged[0] = (2, damaged[0][1])
    assert not literal_valid(damaged)
    assert triples_inventory(FIXTURE) == literal_inventory(FIXTURE)
    # A partial first-profile fixture must be accepted by both oracles.
    partial = tuple((rows[i], 1 << i) for i in range(3))
    partial += tuple((1 << i, cols[i]) for i in range(3))
    fast = triples_inventory(partial)
    direct = literal_inventory(partial)
    assert fast == direct
    assert any(U == (0, 1, 2) and V == (3, 4, 5) for U, V, _ in fast[1])
    complete = [((1 << 6) - 1) ^ (1 << i) for i in range(6)]
    assert clique(complete, 6) is not None
    complete[0] &= ~(1 << 1)
    complete[1] &= ~1
    assert clique(complete, 6) is None
    # Synthetic partial profiles, not a complete central table: six copies
    # of one valid 3-by-3 profile have disjoint top labels. This exercises
    # positive and negative results of BOTH compatibility implementations.
    template = (
        (rows[0], mask((0,))),
        (rows[1], mask((1,))),
        (rows[2], mask((2, 3, 7))),
        (mask((0,)), cols[0]),
        (mask((1,)), cols[1]),
        (mask((2, 4, 6)), cols[2]),
    )
    assert triples_inventory(template) == literal_inventory(template)
    assert any(
        U == (0, 1, 2) and V == (3, 4, 5) for U, V, _ in triples_inventory(template)[1]
    )
    toy = template * 6

    def record(U, V):
        U, V = tuple(sorted(U)), tuple(sorted(V))
        good = mask(
            i * len(toy) + j for i in U for j in V if not (toy[i][1] & toy[j][0])
        )
        assert good.bit_count() == 6
        return U, V, good

    records = [
        record(range(6 * i, 6 * i + 3), range(6 * i + 3, 6 * i + 6)) for i in range(6)
    ]
    assert clique(compatibility(toy, records), 6) is not None
    assert literal_compatible(toy, records, 6) is not None
    assert clique(compatibility(toy, records[:5]), 5) is not None
    assert literal_compatible(toy, records[:5], 5) is not None
    # Repeated good pairs, a capacity-one source, and a capacity-one target
    # are three separate obstructions; the latter two keep good pairs disjoint.
    for replacement in (
        records[0],
        record((2, 6, 7), (9, 10, 11)),
        record((6, 7, 8), (5, 9, 10)),
    ):
        bad = records.copy()
        bad[1] = replacement
        if replacement != records[0]:
            assert not (bad[0][2] & bad[1][2])
        assert clique(compatibility(toy, bad), 6) is None
        assert literal_compatible(toy, bad, 6) is None
        assert clique(compatibility(toy, bad[:5]), 5) is None
        assert literal_compatible(toy, bad[:5], 5) is None
    return [value for key, value in sorted(representatives.items())]


def main():
    if not __debug__:
        raise SystemExit("Run without python -O: assertions are required.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", type=int, help="Verify one numbered family only.")
    args = parser.parse_args()
    started = perf_counter()
    families = controls()
    indices = range(len(families)) if args.case is None else [args.case]
    if args.case is not None and not 0 <= args.case < len(families):
        parser.error("--case must be between 0 and 68")
    totals = Counter()
    found_control = False
    for index in indices:
        begin = perf_counter()
        histogram = Counter()
        count = 0

        def visit(tiles, histogram=histogram):
            nonlocal count, found_control
            count += 1
            assert literal_valid(tiles)
            fast = triples_inventory(tiles)
            direct = literal_inventory(tiles)
            assert fast == direct
            ps = fast[1]
            histogram[len(ps)] += 1
            assert clique(compatibility(tiles, ps), FORBIDDEN_PROFILE_COUNT) is None
            assert literal_compatible(tiles, ps, FORBIDDEN_PROFILE_COUNT) is None
            found_control |= tuple(sorted(tiles)) == tuple(sorted(FIXTURE))
            return False

        nodes, hits, incomplete, _options, total = fast_covers(
            *families[index], 10**12, 10**12, visit
        )
        assert not incomplete and not hits and count == total
        totals["nodes"] += nodes
        totals["fixtures"] += count
        print(
            f"Family {index}: nodes={nodes}; fixtures={count}; "
            f"profile histogram={dict(sorted(histogram.items()))}; "
            f"elapsed={perf_counter() - begin:.3f}s",
            flush=True,
        )
    if args.case is None or args.case == 0:
        assert found_control
    if args.case is None:
        assert totals == Counter(nodes=32567237, fixtures=226500)
    label = "all 69 families" if args.case is None else f"family {args.case} only"
    print(
        f"PASS: {label}; no {FORBIDDEN_PROFILE_COUNT} compatible profiles; "
        f"{dict(totals)}; elapsed={perf_counter() - started:.3f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()
