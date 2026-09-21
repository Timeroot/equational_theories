#!/usr/bin/env python3
"""No four-profile occurs on the audited 200 eighteen-top central fixtures.

The original three-profile checker and its normalized central generator are
unchanged. This wrapper checks every four-element subset of the full top set,
with an independent literal-set oracle and an accepting partial fixture.
"""

import importlib.util
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from time import perf_counter

SOURCE = Path(__file__).with_name("1485_m8_eighteen_two_small_check.py")
SPEC = importlib.util.spec_from_file_location("central_fixture_generator", SOURCE)
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)


def fast_profiles(tiles):
    """All four-part partitions, followed by the full central permutation test."""
    choices = []
    for side in (0, 1):
        choices.append(
            tuple(
                indices
                for indices in combinations(range(len(tiles)), 4)
                if sum(tiles[i][side] for i in indices) == BASE.LABELS
                and all(
                    not tiles[i][side] & tiles[j][side]
                    for i, j in combinations(indices, 2)
                )
            )
        )
    profiles = []
    for U, V in product(*choices):
        K = [[(tiles[i][1] & tiles[j][0]).bit_count() for j in V] for i in U]
        if all(sum(row) == 1 for row in K) and all(
            sum(K[i][j] for i in range(4)) == 1 for j in range(4)
        ):
            profiles.append((U, V))
    return tuple(choices), tuple(profiles)


def literal_profiles(tiles):
    """Independent set-union partitions and explicit matching-edge counts."""
    blocks = BASE.as_sets(tiles)
    choices = []
    for side in (0, 1):
        candidates = []
        for indices in combinations(range(len(blocks)), 4):
            parts = [blocks[i][side] for i in indices]
            if set.union(set(), *map(set, parts)) == set(range(BASE.N)) and all(
                not first & second for first, second in combinations(parts, 2)
            ):
                candidates.append(indices)
        choices.append(tuple(candidates))
    profiles = []
    for U, V in product(*choices):
        edges = [(i, j) for i in U for j in V if blocks[i][1] & blocks[j][0]]
        if (
            len(edges) == 4
            and len({i for i, j in edges}) == 4
            and len({j for i, j in edges}) == 4
            and all(len(blocks[i][1] & blocks[j][0]) == 1 for i, j in edges)
        ):
            profiles.append((U, V))
    return tuple(choices), tuple(profiles)


def controls():
    BASE.controls()
    # A partial incidence system with a known ACCEPTED four-profile. It is not
    # asserted to be a complete central system or an E1485 magma.
    parts = tuple(BASE.mask((2 * i, 2 * i + 1)) for i in range(4))
    partial = tuple((parts[i], 1 << i) for i in range(4))
    partial += tuple((1 << i, parts[i]) for i in range(4))
    fast, direct = fast_profiles(partial), literal_profiles(partial)
    assert fast == direct
    assert ((0, 1, 2, 3), (4, 5, 6, 7)) in fast[1]
    # Duplicate one matching singleton: the marked pair now has a missing
    # central-matrix column and is REJECTED by both profile implementations.
    damaged = list(partial)
    damaged[7] = (1, damaged[7][1])
    assert fast_profiles(damaged) == literal_profiles(damaged)
    assert ((0, 1, 2, 3), (4, 5, 6, 7)) not in fast_profiles(damaged)[1]
    assert BASE.literal_central_valid(BASE.FIXTURE)
    assert fast_profiles(BASE.FIXTURE) == literal_profiles(BASE.FIXTURE)
    assert not fast_profiles(BASE.FIXTURE)[1]


def main():
    if not __debug__:
        raise SystemExit("Run without python -O: this checker needs its assertions.")
    started = perf_counter()
    controls()
    expected = (
        Counter({(11, 11, 0): 8, (13, 13, 0): 32}),
        Counter({(11, 11, 0): 32, (13, 13, 0): 128}),
    )
    total = 0
    for kind in (0, 1):
        counts, fixtures = BASE.central_fixtures(kind)
        assert counts == BASE.EXPECTED_COUNTS[kind]
        inventory = Counter()
        for tiles in fixtures:
            assert BASE.literal_central_valid(tiles)
            fast = fast_profiles(tiles)
            assert fast == literal_profiles(tiles)
            choices, profiles = fast
            assert not profiles
            inventory[(len(choices[0]), len(choices[1]), len(profiles))] += 1
        assert inventory == expected[kind]
        total += len(fixtures)
        print(
            f"kind={kind}: generator={counts}; four-profile inventory={dict(inventory)}"
        )
    assert total == 200
    print(
        f"PASS: 200 complete central fixtures, 200 direct-oracle comparisons; "
        f"zero four-profiles; {perf_counter() - started:.3f}s"
    )


if __name__ == "__main__":
    main()
