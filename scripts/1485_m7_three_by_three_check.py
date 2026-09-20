#!/usr/bin/env python3
"""Exclude a (3,3) central top profile when r=4 and m=p=7.

This is a solver-free finite incidence check, not a Lean proof. See
docs/1485_seven_central_three_by_three.md for its complete normalization.
Every central rectangle cover is tested against necessary singleton
crowns; a cover is not itself a magma model.
"""

import argparse
from pathlib import Path
from runpy import run_path
from time import perf_counter


SHARED = run_path(str(Path(__file__).with_name("1485_m7_overlap_one_check.py")))
RectangleSearch = SHARED["RectangleSearch"]
TwoCrownSearch = SHARED["TwoCrownSearch"]


class AllCrownSearch(TwoCrownSearch):
    """Complete central covers, then test every singleton omission."""

    def __init__(self, rectangles, audit_limit=0):
        super().__init__(rectangles, audit_limit)
        self.dual = TwoCrownSearch([(c, p) for p, c in rectangles])
        self.incidence_covers = 0
        self.rejections = [0, 0]

    def search(self, active, uncovered, row_counts, column_counts, selected, stage):
        previous = self.selected, self.stage
        self.selected, self.stage = selected, stage
        try:
            if uncovered:
                return RectangleSearch.search(
                    self, active, uncovered, row_counts, column_counts
                )
            self.nodes += 1
            if any(count != 4 for count in row_counts + column_counts):
                return False
            self.incidence_covers += 1
            self.dual.selected = selected
            for orientation, checker in enumerate((self, self.dual)):
                for source in selected:
                    if checker.rectangles[source][1].bit_count() != 1:
                        continue
                    label = checker.rectangles[source][1].bit_length() - 1
                    for omitted in selected:
                        predecessors, successors = checker.rectangles[omitted]
                        if not predecessors >> label & 1 or successors.bit_count() != 1:
                            continue
                        self.witness_calls += 1
                        witnesses = checker.witnesses(0, source, omitted, label)
                        if self.audits < self.audit_limit:
                            fast = set(witnesses)
                            reference = set(checker.reference_witnesses(0, source, omitted, label))
                            assert fast == reference
                            self.audits += 1
                            exists = bool(fast)
                        else:
                            exists = next(witnesses, None) is not None
                        if not exists:
                            self.rejections[orientation] += 1
                            return False
            return True
        finally:
            self.selected, self.stage = previous

    def has_cover(self, required):
        state = (1 << len(self.rectangles)) - 1, (1 << 49) - 1, (0,) * 7, (0,) * 7
        selected = []
        for rectangle in required:
            index = self.rectangles.index(rectangle)
            state = RectangleSearch.add(self, index, *state)
            assert state is not None
            selected.append(index)
        return self.search(*state, tuple(selected), 0)


def normalized_case(case, audit_limit=0):
    # A,D,{5},{6} is a known P partition. B,E,{t0},{t1} is a
    # known C partition. Only the tile (A,B) is required explicitly;
    # relaxing the other partition-existence requirements is safe.
    a, d, p_singletons = 7, 24, 96
    b, e, c_singletons = (
        (104, 17, 6), (41, 80, 6), (41, 68, 18), (97, 20, 10)
    )[case]
    required = a, b

    def forbidden(left, right):
        p, c = left
        q, f = right
        p_size, c_size, q_size, f_size = map(int.bit_count, (p, c, q, f))
        return (
            # Boundary containment: Q subset P, Q meeting known S_C.
            (q & ~p == 0 and q & c_singletons and c_size >= 2
             and (f_size >= 2 or c_size >= 3))
            # Its dual, using only the known actual singleton-P labels.
            or (f & ~c == 0 and f & p_singletons and p_size >= 2
                and (q_size >= 2 or p_size >= 3))
            # All actual singleton labels must be disjoint globally.
            or (p_size == f_size == 1 and p == f)
            or (q_size == c_size == 1 and q == c)
        )

    subsets = [mask for mask in range(1, 128) if mask.bit_count() <= 3]
    rectangles = []
    for p in subsets:
        for c in subsets:
            p_size, c_size = p.bit_count(), c.bit_count()
            if (p & c).bit_count() > 1:
                continue
            if p_size == 1 and p & c_singletons or c_size == 1 and c & p_singletons:
                continue
            if p_size == c_size == 1 and p == c:
                continue
            if any((p & block).bit_count() > 1 for block in (b, e)):
                continue
            if any((c & block).bit_count() > 1 for block in (a, d)):
                continue
            if (p, c) != required:
                if p & a and c & b:
                    continue
                if forbidden((p, c), required) or forbidden(required, (p, c)):
                    continue
            rectangles.append((p, c))
    search = AllCrownSearch(rectangles, audit_limit)
    for index, left in enumerate(rectangles):
        for other, right in enumerate(rectangles[:index]):
            if forbidden(left, right) or forbidden(right, left):
                search.compatible[index] &= ~(1 << other)
                search.compatible[other] &= ~(1 << index)
    return search, [required]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-witnesses", type=int, default=100,
                        help="compare this many calls per case with the direct crown enumerator")
    args = parser.parse_args()
    if args.audit_witnesses < 0:
        parser.error("--audit-witnesses must be nonnegative")
    # Shared controls include a valid central rectangle cover, an existing
    # crown, and a missing crown, checked by both witness implementations.
    SHARED["controls"]()
    expected = (
        (419, 72890, 0), (501, 337621, 1870),
        (538, 347821, 5552), (501, 378210, 1870),
    )
    for case, (candidates, nodes, covers) in enumerate(expected):
        start = perf_counter()
        search, required = normalized_case(case, args.audit_witnesses)
        assert len(search.rectangles) == candidates
        assert not search.has_cover(required)
        assert search.nodes == nodes
        assert search.incidence_covers == covers
        assert sum(search.rejections) == covers
        assert search.audits == min(args.audit_witnesses, search.witness_calls)
        print(
            f"case {case + 1}: {candidates} rectangles; {nodes} states; "
            f"{covers} incidence covers, all rejected; "
            f"forward/dual failures {search.rejections}; "
            f"{search.audits} witness audits; {perf_counter() - start:.3f}s"
        )


if __name__ == "__main__":
    main()
