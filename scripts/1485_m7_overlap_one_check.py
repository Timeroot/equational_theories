#!/usr/bin/env python3
"""Exclude one common singleton label at r=4, m=p=7, without a solver.

Two necessary crowns are selected before completing a central rectangle
cover. No search timeout or external ATP output is used.
"""

import argparse
from pathlib import Path
from runpy import run_path
from time import perf_counter


RectangleSearch = run_path(
    str(Path(__file__).with_name("1485_m7_overlap_three_check.py"))
)["RectangleSearch"]


class TwoCrownSearch(RectangleSearch):
    def __init__(self, rectangles, audit_limit=0):
        super().__init__(7, 4, rectangles)
        self.selected = ()
        self.stage = 0
        self.witness_count = 0
        self.witness_calls = 0
        self.complete_covers = 0
        self.audit_limit = audit_limit
        self.audits = 0
        self.exact_p = [0] * 128
        self.exact_c = [0] * 128
        for index, (predecessors, successors) in enumerate(rectangles):
            self.exact_p[predecessors] |= 1 << index
            self.exact_c[successors] |= 1 << index
        self.disjoint_p = [0] * 128
        self.hit_c = [0] * 128
        for mask in range(128):
            for index, (predecessors, successors) in enumerate(rectangles):
                if not predecessors & mask:
                    self.disjoint_p[mask] |= 1 << index
                if successors & mask:
                    self.hit_c[mask] |= 1 << index

    def add(self, index, *state):
        result = super().add(index, *state)
        if result is None:
            return None
        return (*result, self.selected + (index,), self.stage)

    def witness_data(self, active, source, omitted, label):
        chosen = set(self.selected)
        chosen_mask = sum(1 << index for index in chosen)
        row = [index for index in chosen if self.rectangles[index][0] >> label & 1]
        assert len(row) == 4 and omitted in row and source in chosen
        assert self.rectangles[source][1] == 1 << label
        assert self.rectangles[omitted][1].bit_count() == 1
        retained = [index for index in row if index != omitted]
        replacements = (active | chosen_mask) & self.exact_c[self.rectangles[omitted][1]]
        return chosen_mask, row, retained, replacements

    def witnesses(self, active, source, omitted, label):
        """Enumerate ALL compatible (replacement, other three U rows)."""
        chosen_mask, row, retained, replacements = self.witness_data(active, source, omitted, label)
        source_p = self.rectangles[source][0]
        hits = [self.hit_c[self.rectangles[index][0]] for index in retained]
        # Other crown rows hit the replacement and exactly two retained columns.
        bases = (
            hits[1] & hits[2] & ~hits[0],
            hits[0] & hits[2] & ~hits[1],
            hits[0] & hits[1] & ~hits[2],
        )
        while replacements:
            bit = replacements & -replacements
            replacements ^= bit
            replacement = bit.bit_length() - 1
            if replacement in row:
                continue
            assert not self.rectangles[replacement][0] >> label & 1
            available = chosen_mask | bit | (active & self.compatible[replacement])
            available &= self.disjoint_p[source_p]
            available &= self.hit_c[self.rectangles[replacement][0]]
            first, second, third = (available & base for base in bases)
            while first:
                x_bit = first & -first
                first ^= x_bit
                x = x_bit.bit_length() - 1
                x_p = self.rectangles[x][0]
                ys = second & self.compatible[x] & self.disjoint_p[x_p]
                while ys:
                    y_bit = ys & -ys
                    ys ^= y_bit
                    y = y_bit.bit_length() - 1
                    remaining = 127 ^ (source_p | x_p | self.rectangles[y][0])
                    zs = third & self.exact_p[remaining] & self.compatible[x] & self.compatible[y]
                    while zs:
                        z_bit = zs & -zs
                        zs ^= z_bit
                        yield replacement, x, y, z_bit.bit_length() - 1

    def reference_witnesses(self, active, source, omitted, label):
        """Slower, direct set-intersection version for independent controls."""
        chosen_mask, row, retained, replacements = self.witness_data(active, source, omitted, label)
        source_p = self.rectangles[source][0]
        while replacements:
            bit = replacements & -replacements
            replacements ^= bit
            replacement = bit.bit_length() - 1
            if replacement in row:
                continue
            columns = retained + [replacement]
            available = chosen_mask | bit | (active & self.compatible[replacement])
            groups = [[], [], []]
            while available:
                candidate_bit = available & -available
                available ^= candidate_bit
                index = candidate_bit.bit_length() - 1
                predecessors, successors = self.rectangles[index]
                if predecessors & source_p:
                    continue
                entries = [(successors & self.rectangles[column][0]).bit_count() for column in columns]
                if sorted(entries) != [0, 1, 1, 1] or entries[3] == 0:
                    continue
                groups[entries.index(0)].append(index)
            for x in groups[0]:
                for y in groups[1]:
                    if self.rectangles[x][0] & self.rectangles[y][0]:
                        continue
                    if not self.compatible[x] >> y & 1:
                        continue
                    union = source_p | self.rectangles[x][0] | self.rectangles[y][0]
                    for z in groups[2]:
                        if union & self.rectangles[z][0] or union | self.rectangles[z][0] != 127:
                            continue
                        if self.compatible[x] >> z & 1 and self.compatible[y] >> z & 1:
                            yield replacement, x, y, z

    def search(self, active, uncovered, row_counts, column_counts, selected, stage):
        previous = self.selected, self.stage
        self.selected, self.stage = selected, stage
        try:
            if not uncovered:
                self.nodes += 1
                complete = all(count == 4 for count in row_counts + column_counts)
                self.complete_covers += int(complete)
                return complete
            if stage < 2:
                source = self.sources[stage]
                label = self.rectangles[source][1].bit_length() - 1
                if row_counts[label] < 4:
                    # Finish the central row needed by this crown first.
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
                # Every seven-label, four-block partition has a singleton.
                omitted = min(
                    index for index in selected
                    if self.rectangles[index][0] >> label & 1
                    and self.rectangles[index][1].bit_count() == 1
                )
                witnesses = self.witnesses(active, source, omitted, label)
                self.witness_calls += 1
                if self.audits < self.audit_limit:
                    fast = list(witnesses)
                    reference = list(self.reference_witnesses(active, source, omitted, label))
                    assert set(fast) == set(reference)
                    self.audits += 1
                    witnesses = iter(fast)
                for witness in witnesses:
                    self.witness_count += 1
                    state = active, uncovered, row_counts, column_counts
                    next_selected = list(selected)
                    for index in witness:
                        if index in next_selected:
                            continue
                        state = super().add(index, *state)
                        if state is None:
                            break
                        next_selected.append(index)
                    if state is not None and self.search(*state, tuple(next_selected), stage + 1):
                        return True
                return False
            return super().search(active, uncovered, row_counts, column_counts)
        finally:
            self.selected, self.stage = previous

    def has_cover(self, required):
        self.sources = tuple(self.rectangles.index(rectangle) for rectangle in required)
        assert len(self.sources) == 2
        state = (1 << len(self.rectangles)) - 1, (1 << 49) - 1, (0,) * 7, (0,) * 7
        for index in self.sources:
            state = super().add(index, *state)
            assert state is not None
        return self.search(*state, self.sources, 0)


def normalized_case(a, audit_limit=0):
    """One common label 0; allowed P-only labels 1..a; C-only labels a+1..6."""
    assert a in (1, 2, 3)
    p_only = sum(1 << label for label in range(1, a + 1))
    c_only = sum(1 << label for label in range(a + 1, 7))
    required = [(2, 1), (1, 1 << (a + 1))]
    subsets = [mask for mask in range(1, 128) if mask.bit_count() <= 4]
    rectangles = []
    for predecessors in subsets:
        for successors in subsets:
            p, c = predecessors.bit_count(), successors.bit_count()
            if (predecessors & successors).bit_count() > 1:
                continue
            if p == 1 and predecessors & ~(p_only | 1):
                continue
            if c == 1 and successors & ~(c_only | 1):
                continue
            if (p, c) in ((1, 4), (4, 1)):
                continue
            if predecessors & 1 and c > 2:
                continue
            if successors & 1 and p > 2:
                continue
            rectangle = predecessors, successors
            if p == 1 and predecessors & 1 and rectangle not in required:
                continue
            if c == 1 and successors & 1 and rectangle not in required:
                continue
            if any(
                predecessors & other[0] and successors & other[1] and rectangle != other
                for other in required
            ):
                continue
            rectangles.append(rectangle)
    return TwoCrownSearch(rectangles, audit_limit), required


def controls():
    # A central rectangle system, NOT a magma model: the first crown exists,
    # but the next singleton source has no crown for the specified omission.
    fixture = [
        (2, 1), (1, 4), (5, 9), (17, 34), (65, 80), (66, 4),
        (12, 22), (48, 68), (12, 64), (24, 9), (48, 16),
        (2, 80), (2, 42), (12, 32), (96, 3), (96, 40),
    ]
    assert RectangleSearch(7, 4, fixture).has_cover(fixture)
    search = TwoCrownSearch(fixture)
    search.selected = tuple(range(len(fixture)))
    fast = list(search.witnesses(0, 0, 1, 0))
    reference = list(search.reference_witnesses(0, 0, 1, 0))
    assert len(fast) == 1 and set(fast) == set(reference)
    assert not list(search.witnesses(0, 1, 8, 2))
    assert not list(search.reference_witnesses(0, 1, 8, 2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-witnesses", type=int, default=0,
                        help="compare this many witness calls per case with the direct implementation")
    args = parser.parse_args()
    if args.audit_witnesses < 0:
        parser.error("--audit-witnesses must be nonnegative")
    controls()
    for a, candidates, nodes in ((1, 2322, 455715), (2, 2325, 698286), (3, 2326, 634463)):
        start = perf_counter()
        search, required = normalized_case(a, args.audit_witnesses)
        assert len(search.rectangles) == candidates
        assert not search.has_cover(required)
        assert search.nodes == nodes
        assert search.complete_covers == 0
        assert search.audits == min(args.audit_witnesses, search.witness_calls)
        print(
            f"a={a}, b={6-a}: {candidates} rectangles; {nodes} states; "
            f"{search.witness_count} crown witnesses; no cover; {perf_counter()-start:.3f}s"
        )


if __name__ == "__main__":
    main()
