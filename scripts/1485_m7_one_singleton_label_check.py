#!/usr/bin/env python3
"""Exclude a single singleton-label orientation at r=4, m=p=7.

This enumerates central rectangle systems and necessary replacement crowns,
not multiplication tables. It uses no solver.
"""

import argparse
from pathlib import Path
from runpy import run_path
from time import perf_counter


helpers = run_path(str(Path(__file__).with_name("1485_m7_overlap_one_check.py")))
RectangleSearch = helpers["RectangleSearch"]
TwoCrownSearch = helpers["TwoCrownSearch"]


def all_crowns(rectangles, dual=False):
    """Directly test every singleton-source/singleton-omission crown."""
    oriented = [(c, p) for p, c in rectangles] if dual else rectangles
    predecessors, successors = zip(*oriented)
    size = len(oriented)
    for source in range(size):
        if successors[source].bit_count() != 1:
            continue
        label = successors[source].bit_length() - 1
        row = [v for v in range(size) if predecessors[v] >> label & 1]
        assert len(row) == 4
        for omitted in row:
            if successors[omitted].bit_count() != 1:
                continue
            found = False
            for replacement in range(size):
                if replacement in row or successors[replacement] != successors[omitted]:
                    continue
                columns = [v for v in row if v != omitted] + [replacement]
                groups = [[], [], []]
                for candidate in range(size):
                    if predecessors[candidate] & predecessors[source]:
                        continue
                    entries = [
                        (successors[candidate] & predecessors[column]).bit_count()
                        for column in columns
                    ]
                    if sorted(entries) == [0, 1, 1, 1] and entries[3] == 1:
                        groups[entries.index(0)].append(candidate)
                for x in groups[0]:
                    for y in groups[1]:
                        if predecessors[x] & predecessors[y]:
                            continue
                        union = predecessors[source] | predecessors[x] | predecessors[y]
                        for z in groups[2]:
                            if not union & predecessors[z] and union | predecessors[z] == 127:
                                found = True
                                break
                        if found:
                            break
                    if found:
                        break
                if found:
                    break
            if not found:
                return False
    return True


class SingleLabelSearch(TwoCrownSearch):
    """Select one required crown, then check all crowns on complete covers."""

    def search(self, active, uncovered, row_counts, column_counts, selected, stage):
        previous = self.selected, self.stage
        self.selected, self.stage = selected, stage
        try:
            if not uncovered:
                self.nodes += 1
                if not all(count == 4 for count in row_counts + column_counts):
                    return False
                self.complete_covers += 1
                cover = [self.rectangles[index] for index in selected]
                return all_crowns(cover) and all_crowns(cover, dual=True)
            if stage == 0:
                if row_counts[0] < 4:
                    self.nodes += 1
                    cells = uncovered & 127
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
                source = self.sources[0]
                witnesses = self.witnesses(active, source, source, 0)
                self.witness_calls += 1
                if self.audits < self.audit_limit:
                    fast = list(witnesses)
                    direct = list(self.reference_witnesses(active, source, source, 0))
                    assert set(fast) == set(direct)
                    self.audits += 1
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
            return RectangleSearch.search(self, active, uncovered, row_counts, column_counts)
        finally:
            self.selected, self.stage = previous

    def has_cover(self, required):
        self.sources = tuple(self.rectangles.index(rectangle) for rectangle in required)
        state = (1 << len(self.rectangles)) - 1, (1 << 49) - 1, (0,) * 7, (0,) * 7
        for index in self.sources:
            state = RectangleSearch.add(self, index, *state)
            assert state is not None
        return self.search(*state, self.sources, 0)


def normalized_case(shape, audit_limit=0):
    """The four C={0} blocks partition Z; the first P block contains 0."""
    predecessor_partitions = {
        "3211": [7, 24, 32, 64],
        "2311": [3, 28, 32, 64],
        "2221": [3, 12, 48, 64],
    }
    required = [(predecessors, 1) for predecessors in predecessor_partitions[shape]]
    rectangles = []
    for predecessors in range(1, 128):
        if predecessors == 1 or predecessors.bit_count() > 3:
            continue
        for successors in range(1, 128):
            if successors != 1 and (successors & 1 or successors.bit_count() != 2):
                continue
            if (predecessors & successors).bit_count() > 1:
                continue
            rectangle = predecessors, successors
            if any(
                predecessors & other[0] and successors & other[1] and rectangle != other
                for other in required
            ):
                continue
            rectangles.append(rectangle)
    return SingleLabelSearch(rectangles, audit_limit), required


def controls():
    # A valid central-incidence cover, NOT a magma: all forward crowns exist,
    # but some dual crowns fail. This checks that the dual test is substantive.
    fixture = [
        (7, 1), (7, 10), (17, 36), (67, 80), (24, 1), (16, 80),
        (64, 10), (40, 20), (32, 1), (64, 1), (4, 20), (66, 36),
        (4, 96), (40, 96), (24, 10), (32, 10),
    ]
    assert RectangleSearch(7, 4, fixture).has_cover(fixture)
    assert all_crowns(fixture)
    assert not all_crowns(fixture, dual=True)
    # Independently compare the completed-cover test with the existing
    # fast and reference witness implementations, in both orientations.
    for dual in (False, True):
        oriented = [(c, p) for p, c in fixture] if dual else fixture
        search = TwoCrownSearch(oriented)
        search.selected = tuple(range(len(fixture)))
        every = True
        for source, (_, successors) in enumerate(oriented):
            if successors.bit_count() != 1:
                continue
            label = successors.bit_length() - 1
            for omitted, (predecessors, block) in enumerate(oriented):
                if not predecessors >> label & 1 or block.bit_count() != 1:
                    continue
                fast = set(search.witnesses(0, source, omitted, label))
                direct = set(search.reference_witnesses(0, source, omitted, label))
                assert fast == direct
                every &= bool(fast)
        assert every == all_crowns(fixture, dual=dual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-witnesses", type=int, default=0,
                        help="compare this many partial-cover witness calls per case")
    args = parser.parse_args()
    if args.audit_witnesses < 0:
        parser.error("--audit-witnesses must be nonnegative")
    controls()
    cases = (
        ("3211", 338182, 27104, 59176),
        ("2311", 629971, 65340, 108024),
        ("2221", 407493, 56128, 61504),
    )
    for shape, nodes, crowns, covers in cases:
        start = perf_counter()
        search, required = normalized_case(shape, args.audit_witnesses)
        assert len(search.rectangles) == 844
        assert not search.has_cover(required)
        assert (search.nodes, search.witness_count, search.complete_covers) == (nodes, crowns, covers)
        assert search.audits == min(args.audit_witnesses, search.witness_calls)
        print(
            f"{shape}: 844 rectangles; {search.nodes} states; "
            f"{search.witness_count} crown choices; {search.complete_covers} raw covers; "
            f"no cover with all crowns; {perf_counter()-start:.3f}s", flush=True
        )


if __name__ == "__main__":
    main()
