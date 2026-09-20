#!/usr/bin/env python3
"""Finite necessary-profile check for n=48, r=4, m=5, N22=2.

See docs/1485_order_forty_eight_five_central_d2.md. This is not a
model finder and does not assume that incidence data determine a magma.
All arithmetic is exact; no SAT solver or external package is used.
"""

from itertools import combinations, product

LABELS = range(5)
FULL = (1 << 5) - 1
PAIRS = tuple((1 << i) | (1 << j) for i, j in combinations(LABELS, 2))


def central_tilings():
    """Normalize the two disjoint N22 predecessor pairs to 01 and 23."""
    p0, p1, singleton_p = 0b00011, 0b01100, 0b10000
    for c0, c1 in product(PAIRS, repeat=2):
        if c0 & c1:
            continue
        singleton_c = FULL ^ (c0 | c1)
        for extra_p, extra_c in product(PAIRS, repeat=2):
            if extra_p & singleton_p and extra_c & singleton_c:
                continue  # the 2x1 and 1x2 rectangles would overlap
            if {p0, p1, extra_p} & {c0, c1, extra_c}:
                continue  # a top/central/top pair would have two middles
            tiles = [(p0, c0), (p1, c1), (extra_p, singleton_c),
                     (singleton_p, extra_c)]
            covered = {(i, j) for p, c in tiles for i in LABELS
                       for j in LABELS if p >> i & 1 and c >> j & 1}
            assert len(covered) == 12
            tiles += [(1 << i, 1 << j) for i in LABELS for j in LABELS
                      if (i, j) not in covered]
            assert len(tiles) == 17
            yield tiles


def partitions(blocks):
    """All top-index sets whose specified central blocks partition Z."""
    result = []

    def visit(start, used, indices, selected):
        if used == FULL:
            assert 3 <= len(indices) <= 5
            result.append((tuple(indices), selected))
            return
        for i in range(start, len(blocks)):
            if not used & blocks[i]:
                visit(i + 1, used | blocks[i], indices + [i], selected | 1 << i)

    visit(0, 0, [], 0)
    return result


def degree_six_profiles(tiles):
    """Return complete sets of good top pairs of every possible A6 profile."""
    n_top = len(tiles)
    kmasks = [sum(1 << j for j, (p, _) in enumerate(tiles) if c & p)
              for _, c in tiles]
    ups = partitions([p for p, _ in tiles])
    vps = partitions([c for _, c in tiles])
    profiles = []
    for u, _ in ups:
        eligible = sum(1 << j for j in range(n_top)
                       if sum(kmasks[i] >> j & 1 for i in u) == 2)
        for v, vmask in vps:
            if len(u) != len(v) or vmask & ~eligible:
                continue
            if any((kmasks[i] & vmask).bit_count() != 2 for i in u):
                continue
            profiles.append({(i, j) for i in u for j in v
                             if not kmasks[i] >> j & 1})
    return profiles


def check_tiling(tiles):
    profiles = degree_six_profiles(tiles)
    requirements = [(i, z) for i, (_, c) in enumerate(tiles)
                    if c.bit_count() == 1 for z in LABELS]
    choices = []
    for i, z in requirements:
        options = [a for a, good in enumerate(profiles)
                   if any(x == i and tiles[y][1] >> z & 1 for x, y in good)]
        if not options:
            return "missing_profile"
        choices.append(options)
    # Two requirements are incompatible if every way to witness them
    # uses distinct profiles claiming the same top-product cell.
    for left, right in combinations(choices, 2):
        if all(a != b and profiles[a] & profiles[b] for a in left for b in right):
            return "overlapping_profiles"
    raise AssertionError("A central tiling remains unexcluded")


def main():
    counts = {"missing_profile": 0, "overlapping_profiles": 0}
    for tiles in central_tilings():
        counts[check_tiling(tiles)] += 1
    assert counts == {"missing_profile": 976, "overlapping_profiles": 8}, counts
    print("Checked all 984 normalized central tilings:")
    print("  976 have a central-column image without any possible A6 output;")
    print("    8 force two A6 profiles to claim the same good top pair.")
    print("No n=48, r=4, m=5 model can have N22=2.")


if __name__ == "__main__":
    main()
