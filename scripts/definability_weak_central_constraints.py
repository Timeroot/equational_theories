"""Proved structural constraints and verified symmetries for the E1485 recovery search.

The arithmetic constraints use the standalone E1483 translation and constant-row
Lean certificates. The extra permutations preserve the necessary-condition
problem; they are not asserted to be automorphisms of the source operation.
"""

import itertools

from pysat.card import CardEnc, EncType


def strengthen_search(
    n,
    pool,
    solver,
    add,
    P,
    R,
    Col,
    canonical,
    truth,
    entries,
    relations,
    source,
    *,
    bit_channel=False,
    rank_edges=False
):
    for x, b, c in itertools.product(range(n), repeat=3):
        if (x, b, c) != canonical((x, b, c)):
            continue
        add([-Col(x, b), -P(x, b, c), P(c, x, b)])
        add([-R(x, b), -P(b, x, c), P(x, c, b)])

    # Symmetries of the necessary-condition problem (not source automorphisms).
    small = sorted(set().union(*(set(e["sub"]) for e in entries)))
    free_orbits = [[1, 2, 4, 8, 16], [3, 6, 12, 24, 17], [7, 14, 28, 25, 19]]
    assert set(small).isdisjoint(set().union(*map(set, free_orbits)))
    assert len(small) + sum(map(len, free_orbits)) == n
    for oi in range(3):
        perm = list(range(n))
        for i in range(5):
            perm[free_orbits[oi][i]] = free_orbits[oi][(i + 1) % 5]
        assert all(
            {n * perm[v // n] + perm[v % n] for v in r} == set(r) for r in relations
        )
    for oi, oj in [(0, 1), (1, 2)]:
        perm = list(range(n))
        for a, b in zip(free_orbits[oi], free_orbits[oj]):
            perm[a] = b
            perm[b] = a
        assert all(
            {n * perm[v // n] + perm[v % n] for v in r} == set(r) for r in relations
        )

    def seen(i, j):
        return pool.id(("seen_free", i, j)) if i >= 0 else -truth

    for i, (x, y) in enumerate(itertools.product(small, repeat=2)):
        for j, orb in enumerate(free_orbits):
            old, new = seen(i - 1, j), seen(i, j)
            add([-old, new])
            add([-new, old] + [P(x, y, z) for z in orb])
            for z in orb:
                add([-P(x, y, z), new])
                if z != orb[0]:
                    add([-P(x, y, z), old])
                if j:
                    add([-P(x, y, z), seen(i - 1, j - 1)])
    print("free-orbit symmetries verified and encoded", flush=True)

    # For an idempotent a, x -> (a*x,x*a) is injective.
    # Its row and column images are equipotent, so their common size is >= ceil(sqrt(n)).
    for clause in CardEnc.atleast(
        [R(11, z) for z in range(n)], 6, vpool=pool, encoding=EncType.seqcounter
    ):
        add(clause)
    for x, y in itertools.combinations(range(n), 2):
        left = pool.id(("sameleft", x, y))
        right = pool.id(("sameright", x, y))
        for z in range(n):
            add([-P(11, x, z), -P(11, y, z), left])
            add([-P(x, 11, z), -P(y, 11, z), right])
        add([-left, -right])

    # Exactly five idempotents rule out constant rows; a bijective row would give one.
    for x in range(n):
        if (x,) != canonical((x,)):
            continue
        for clause in CardEnc.atleast(
            [R(x, z) for z in range(n)], 2, vpool=pool, encoding=EncType.seqcounter
        ):
            add(clause)
        add([-R(x, z) for z in range(n)])

    if bit_channel:
        # Channel one-hot table entries to their five Boolean coordinate bits.
        Bit = lambda x, y, i: pool.id(("bit", x, y, i))
        for x, y in itertools.product(range(n), repeat=2):
            if (x, y) != canonical((x, y)):
                continue
            bits = [Bit(x, y, i) for i in range(5)]
            for z in range(n):
                lits = [bits[i] if z >> i & 1 else -bits[i] for i in range(5)]
                for b in lits:
                    add([-P(x, y, z), b])
                add([P(x, y, z)] + [-b for b in lits])
            solver.set_phases(
                [bits[i] if int(source[x, y]) >> i & 1 else -bits[i] for i in range(5)]
            )
        add([-R(11, z) for z in range(n)])

    if rank_edges:
        # Exact row/column ranks, with product bounds along row and column edges.
        Rank = lambda x, r: pool.id(("rank", canonical((x,))[0], r))
        for x in range(n):
            if (x,) != canonical((x,)):
                continue
            for clause in CardEnc.equals(
                [Rank(x, r) for r in range(2, n)],
                1,
                vpool=pool,
                encoding=EncType.seqcounter,
            ):
                add(clause)
            for r in range(2, n):
                for image in (R, Col):
                    for clause in CardEnc.equals(
                        [image(x, z) for z in range(n)],
                        r,
                        vpool=pool,
                        encoding=EncType.seqcounter,
                    ):
                        add([-Rank(x, r)] + clause)
        # At a rotation-fixed input, an image is a union of rotation orbits.
        # All orbits except {0} and {31} have size five. Channel that residue
        # directly; the sequential counters otherwise see repeated literals.
        orbit_sizes = {}
        for z in range(n):
            representative = canonical((z,))[0]
            orbit_sizes[representative] = orbit_sizes.get(representative, 0) + 1
        assert sorted(orbit_sizes.values()) == [1, 1, 5, 5, 5, 5, 5, 5]
        assert orbit_sizes[0] == orbit_sizes[31] == 1
        for x, r in itertools.product((0, 31), range(2, n)):
            if r % 5 > 2:
                add([-Rank(x, r)])
                continue
            for image in (R, Col):
                for first, last in itertools.product((False, True), repeat=2):
                    if r % 5 != first + last:
                        add(
                            [
                                -Rank(x, r),
                                -image(x, 0) if first else image(x, 0),
                                -image(x, 31) if last else image(x, 31),
                            ]
                        )
        for x, y in itertools.product(range(n), repeat=2):
            if (x, y) != canonical((x, y)):
                continue
            for r, s in itertools.product(range(2, n), repeat=2):
                if r * s < n:
                    add([-R(x, y), -Rank(x, r), -Rank(y, s)])
                    add([-Col(x, y), -Rank(x, r), -Rank(y, s)])
