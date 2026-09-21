#!/usr/bin/env python3
"""Exclude (3,2) after (3,3), (3,1), and (1,3), at r=4,m=p=7.

Solver-free necessary-incidence exhaustion, not a Lean proof or a
search for magma tables.
"""

import argparse
from itertools import combinations, permutations, product
from pathlib import Path
from runpy import run_path
from time import perf_counter


SHARED = run_path(str(Path(__file__).with_name("1485_m7_three_by_three_check.py")))
AllCrownSearch = SHARED["AllCrownSearch"]
TwoCrownSearch = SHARED["TwoCrownSearch"]
SUBSETS = [mask for mask in range(1, 128) if mask.bit_count() <= 3]
PARTITION_CASES = (
    (9, (2, 4, 112)), (9, (2, 16, 100)), (9, (2, 20, 96)),
    (9, (2, 36, 80)), (9, (16, 34, 68)),
    (33, (2, 8, 84)), (33, (2, 12, 80)), (33, (8, 18, 68)),
    (40, (1, 2, 84)), (40, (1, 18, 68)), (96, (1, 10, 20)),
)
EXPECTED = (
    (532, 2408063), (586, 929577), (646, 4435991), (644, 4174707),
    (707, 1831387), (525, 248433), (578, 557522), (632, 923880),
    (459, 186964), (539, 435062), (495, 392215),
)


def verify_partition_cases():
    """Exhaust all residual C partitions modulo P-partition symmetries."""
    symmetries = [
        a + d + s
        for a, d, s in product(
            permutations(range(3)), permutations(range(3, 5)), permutations(range(5, 7))
        )
    ]

    def image(mask, permutation):
        return sum(1 << permutation[label] for label in range(7) if mask >> label & 1)

    result = []
    for b in (9, 33, 40, 96):
        stabilizer = [permutation for permutation in symmetries if image(b, permutation) == b]
        orbits = set()
        for parts in combinations(SUBSETS, 3):
            if b | parts[0] | parts[1] | parts[2] != 127:
                continue
            if sum(block.bit_count() for block in parts) != 5:
                continue
            if any(x & y for x, y in combinations(parts, 2)) or any(x & b for x in parts):
                continue
            if any(
                (block & 7).bit_count() > 1 or (block & 24).bit_count() > 1
                or (block.bit_count() == 1 and block & 96)
                for block in parts
            ):
                continue
            orbits.add(min(
                tuple(sorted(image(block, permutation) for block in parts))
                for permutation in stabilizer
            ))
        result.extend((b, parts) for parts in sorted(orbits))
    assert tuple(result) == PARTITION_CASES


class PartialCrownSearch(AllCrownSearch):
    """Necessary crown lookahead whenever a source row has four tops."""

    def __init__(self, rectangles, audit_limit=0):
        super().__init__(rectangles, audit_limit)
        self.partial_calls = 0
        self.partial_audits = 0
        self.partial_rejections = 0

    def search(self, active, uncovered, row_counts, column_counts, selected, stage):
        if uncovered:
            previous = self.selected
            self.selected = selected
            self.dual.selected = selected
            try:
                for checker, counts in ((self, row_counts), (self.dual, column_counts)):
                    for source in selected:
                        source_c = checker.rectangles[source][1]
                        if source_c.bit_count() != 1:
                            continue
                        label = source_c.bit_length() - 1
                        if counts[label] != 4:
                            continue
                        omitted = next(
                            index for index in selected
                            if checker.rectangles[index][0] >> label & 1
                            and checker.rectangles[index][1].bit_count() == 1
                        )
                        self.partial_calls += 1
                        witnesses = checker.witnesses(active, source, omitted, label)
                        if self.partial_audits < self.audit_limit:
                            fast = set(witnesses)
                            direct = set(checker.reference_witnesses(active, source, omitted, label))
                            assert fast == direct
                            self.partial_audits += 1
                            exists = bool(fast)
                        else:
                            exists = next(witnesses, None) is not None
                        if not exists:
                            self.nodes += 1
                            self.partial_rejections += 1
                            return False
            finally:
                self.selected = previous
        return super().search(active, uncovered, row_counts, column_counts, selected, stage)


def normalized_case(case, audit_limit=0):
    a, d, p_singletons = 7, 24, 96
    b, parts = PARTITION_CASES[case]
    c_singletons = sum(block for block in parts if block.bit_count() == 1)
    required = a, b

    def forbidden(left, right):
        p, c = left
        q, f = right
        p_size, c_size, q_size, f_size = map(int.bit_count, (p, c, q, f))
        return (
            (q & ~p == 0 and q & c_singletons and c_size >= 2
             and (f_size >= 2 or c_size >= 3))
            or (f & ~c == 0 and f & p_singletons and p_size >= 2
                and (q_size >= 2 or p_size >= 3))
            or (p_size == f_size == 1 and p == f)
            or (q_size == c_size == 1 and q == c)
        )

    rectangles = []
    for p in SUBSETS:
        for c in SUBSETS:
            p_size, c_size = p.bit_count(), c.bit_count()
            if (p_size, c_size) in ((3, 3), (3, 1), (1, 3)):
                continue
            if (p & c).bit_count() > 1:
                continue
            if p_size == 1 and p & c_singletons or c_size == 1 and c & p_singletons:
                continue
            if p_size == c_size == 1 and p == c:
                continue
            if any((p & block).bit_count() > 1 for block in (b, *parts)):
                continue
            if (c & a).bit_count() > 1 or (c & d).bit_count() > 1:
                continue
            if (p, c) != required:
                if p & a and c & b:
                    continue
                if forbidden((p, c), required) or forbidden(required, (p, c)):
                    continue
            rectangles.append((p, c))
    search = PartialCrownSearch(rectangles, audit_limit)
    for index, left in enumerate(rectangles):
        for other, right in enumerate(rectangles[:index]):
            if forbidden(left, right) or forbidden(right, left):
                search.compatible[index] &= ~(1 << other)
                search.compatible[other] &= ~(1 << index)
    return search, [required]


def controls():
    SHARED["SHARED"]["controls"]()
    # Same valid central-incidence fixture, now with only the source and
    # its completed central row selected. Its crown needs active tiles.
    fixture = [
        (2, 1), (1, 4), (5, 9), (17, 34), (65, 80), (66, 4),
        (12, 22), (48, 68), (12, 64), (24, 9), (48, 16),
        (2, 80), (2, 42), (12, 32), (96, 3), (96, 40),
    ]
    search = TwoCrownSearch(fixture)
    search.selected = (0, 1, 2, 3, 4)
    active = ((1 << len(fixture)) - 1) ^ sum(1 << index for index in search.selected)
    expected = {(5, 4, 7, 6)}
    assert set(search.witnesses(active, 0, 1, 0)) == expected
    assert set(search.reference_witnesses(active, 0, 1, 0)) == expected
    assert not list(search.witnesses(active & ~(1 << 5), 0, 1, 0))
    assert not list(search.reference_witnesses(active & ~(1 << 5), 0, 1, 0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-witnesses", type=int, default=100)
    parser.add_argument("--case", type=int, choices=range(1, 12),
                        help="run one numbered partition case (default: all eleven)")
    args = parser.parse_args()
    if args.audit_witnesses < 0:
        parser.error("--audit-witnesses must be nonnegative")
    verify_partition_cases()
    controls()
    for case in range(11) if args.case is None else (args.case - 1,):
        start = perf_counter()
        search, required = normalized_case(case, args.audit_witnesses)
        assert not search.has_cover(required)
        assert (len(search.rectangles), search.nodes) == EXPECTED[case]
        assert search.incidence_covers == 0
        assert search.partial_audits == min(args.audit_witnesses, search.partial_calls)
        print(
            f"case {case + 1}: {len(search.rectangles)} rectangles; {search.nodes} states; "
            f"{search.partial_rejections} partial-crown rejections; "
            f"no complete incidence cover; {search.partial_audits} witness audits; "
            f"{perf_counter() - start:.3f}s", flush=True
        )


if __name__ == "__main__":
    main()
