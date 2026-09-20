#!/usr/bin/env python3
"""Exclude a (3,1) central top profile when r=4 and m=p=7.

This solver-free necessary-incidence check assumes the established
exclusion of (3,3). See docs/1485_seven_central_three_by_one.md.
"""

import argparse
from pathlib import Path
from runpy import run_path
from time import perf_counter


SHARED = run_path(str(Path(__file__).with_name("1485_m7_three_by_three_check.py")))
AllCrownSearch = SHARED["AllCrownSearch"]
RectangleSearch = SHARED["RectangleSearch"]


class CrownFirstSearch(AllCrownSearch):
    """Select a crown for one required singleton-C source before completion."""

    def __init__(self, rectangles, source, audit_limit=0):
        super().__init__(rectangles, audit_limit)
        self.first_source = rectangles.index(source)
        assert source[1].bit_count() == 1
        self.first_label = source[1].bit_length() - 1
        self.first_calls = 0
        self.first_audits = 0

    def search(self, active, uncovered, row_counts, column_counts, selected, stage):
        if stage:
            return super().search(active, uncovered, row_counts, column_counts, selected, stage)
        previous = self.selected, self.stage
        self.selected, self.stage = selected, stage
        label = self.first_label
        try:
            if row_counts[label] < 4:
                self.nodes += 1
                cells = uncovered & (127 << (7 * label))
                choices, minimum = 0, len(self.rectangles) + 1
                while cells:
                    bit = cells & -cells
                    cells ^= bit
                    options = active & self.cells[bit.bit_length() - 1]
                    if options.bit_count() < minimum:
                        choices, minimum = options, options.bit_count()
                while choices:
                    bit = choices & -choices
                    choices ^= bit
                    state = self.add(bit.bit_length() - 1, active, uncovered, row_counts, column_counts)
                    if state is not None and self.search(*state):
                        return True
                return False

            self.nodes += 1
            omitted = min(
                index for index in selected
                if self.rectangles[index][0] >> label & 1
                and self.rectangles[index][1].bit_count() == 1
            )
            witnesses = self.witnesses(active, self.first_source, omitted, label)
            self.first_calls += 1
            if self.first_audits < self.audit_limit:
                fast = list(witnesses)
                direct = list(self.reference_witnesses(active, self.first_source, omitted, label))
                assert set(fast) == set(direct)
                self.first_audits += 1
                witnesses = iter(fast)
            for witness in witnesses:
                self.witness_count += 1
                state = active, uncovered, row_counts, column_counts
                next_selected = list(selected)
                for index in witness:
                    if index in next_selected:
                        continue
                    state = RectangleSearch.add(self, index, *state)
                    if state is None:
                        break
                    next_selected.append(index)
                if state is not None and self.search(*state, tuple(next_selected), 1):
                    return True
            return False
        finally:
            self.selected, self.stage = previous


def normalized_case(label, audit_limit=0):
    """Known column P partition A={0,1,2}, D={3,4}, {5}, {6}."""
    assert label in (0, 3)
    triple, double, p_singletons = 7, 24, 96
    c_singletons = 1 << label
    partition = (triple, double, 32, 64)
    required = triple, c_singletons

    def forbidden(left, right):
        p, c = left
        q, f = right
        p_size, c_size, q_size, f_size = map(int.bit_count, (p, c, q, f))
        return (
            # Boundary containment, using the known actual C singleton.
            (q & ~p == 0 and q & c_singletons and c_size >= 2
             and (f_size >= 2 or c_size >= 3))
            # Dual containment, using the known actual P singletons.
            or (f & ~c == 0 and f & p_singletons and p_size >= 2
                and (q_size >= 2 or p_size >= 3))
            # Conflicting actual singleton labels on two selected tiles.
            or (p_size == f_size == 1 and p == f)
            or (q_size == c_size == 1 and q == c)
        )

    subsets = [mask for mask in range(1, 128) if mask.bit_count() <= 3]
    rectangles = []
    for p in subsets:
        for c in subsets:
            p_size, c_size = p.bit_count(), c.bit_count()
            if p_size == c_size == 3 or (p & c).bit_count() > 1:
                continue
            if p_size == 1 and p & c_singletons or c_size == 1 and c & p_singletons:
                continue
            if any((c & block).bit_count() > 1 for block in (triple, double)):
                continue
            # The selected central column has exactly this P partition.
            if c & c_singletons and p not in partition:
                continue
            rectangle = p, c
            if rectangle != required:
                if p & triple and c & c_singletons:
                    continue
                if forbidden(rectangle, required) or forbidden(required, rectangle):
                    continue
            rectangles.append(rectangle)
    search = CrownFirstSearch(rectangles, required, audit_limit)
    for index, left in enumerate(rectangles):
        for other, right in enumerate(rectangles[:index]):
            if forbidden(left, right) or forbidden(right, left):
                search.compatible[index] &= ~(1 << other)
                search.compatible[other] &= ~(1 << index)
    return search, [required]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-witnesses", type=int, default=100,
                        help="audit this many partial and complete witness calls per case")
    args = parser.parse_args()
    if args.audit_witnesses < 0:
        parser.error("--audit-witnesses must be nonnegative")
    SHARED["SHARED"]["controls"]()
    expected = (
        (0, 1295, 1116058, 808021, 9504),
        (3, 1200, 339202, 108771, 0),
    )
    for label, candidates, nodes, crowns, covers in expected:
        start = perf_counter()
        search, required = normalized_case(label, args.audit_witnesses)
        assert len(search.rectangles) == candidates
        assert not search.has_cover(required)
        assert (search.nodes, search.witness_count, search.incidence_covers) == (nodes, crowns, covers)
        assert sum(search.rejections) == covers
        assert search.first_audits == min(args.audit_witnesses, search.first_calls)
        assert search.audits == min(args.audit_witnesses, search.witness_calls)
        print(
            f"label {label}: {candidates} rectangles; {nodes} states; "
            f"{crowns} first-crown choices; {covers} incidence covers, all rejected; "
            f"partial/complete witness audits {search.first_audits}/{search.audits}; "
            f"{perf_counter()-start:.3f}s", flush=True
        )


if __name__ == "__main__":
    main()
