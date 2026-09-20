#!/usr/bin/env python3
"""Exclude two common singleton labels at r=4, m=p=7, without a solver.

See docs/1485_seven_central_overlap_two.md for the normalization, the
joint-map case excluded analytically, and the outside-label multiplicity.
"""

from pathlib import Path
from runpy import run_path
from time import perf_counter


RectangleSearch = run_path(
    str(Path(__file__).with_name("1485_m7_overlap_three_check.py"))
)["RectangleSearch"]


class MultiplicitySearch(RectangleSearch):
    """Add the selected rectangle list to the otherwise unchanged search state."""

    def __init__(self, size, degree, rectangles):
        super().__init__(size, degree, rectangles)
        self.selected = ()
        self.raw_covers = 0
        self.multiplicities = {}

    def add(self, index, *state):
        result = super().add(index, *state)
        if result is None:
            return None
        return (*result, self.selected + (index,))

    def search(self, active, uncovered, row_counts, column_counts, selected):
        previous = self.selected
        self.selected = selected
        try:
            if not uncovered:
                self.nodes += 1
                if not all(count == self.degree for count in row_counts + column_counts):
                    return False
                self.raw_covers += 1
                rectangles = [self.rectangles[index] for index in selected]
                counts = tuple(sum(p == 1 << label for p, c in rectangles) for label in (2, 3))
                counts += tuple(sum(c == 1 << label for p, c in rectangles) for label in (4, 5))
                self.multiplicities[counts] = self.multiplicities.get(counts, 0) + 1
                return all(count >= 2 for count in counts)
            return super().search(active, uncovered, row_counts, column_counts)
        finally:
            self.selected = previous

    def has_cover(self, required=()):
        state = (
            (1 << len(self.rectangles)) - 1,
            (1 << (self.size * self.size)) - 1,
            (0,) * self.size,
            (0,) * self.size,
        )
        selected = []
        for rectangle in required:
            index = self.rectangles.index(rectangle)
            state = super().add(index, *state)
            if state is None:
                return False
            selected.append(index)
        return self.search(*state, tuple(selected))


def normalized_case(a, b, distinct_y, require_multiplicity=False):
    """Common labels 0,1; a allowed P-only labels; b allowed C-only labels."""
    assert a + b == 5 and a >= 1 and b >= 2
    common = 3
    p_only = sum(1 << label for label in range(2, 2 + a))
    c_only = sum(1 << label for label in range(2 + a, 7))
    y = (2, 3 if distinct_y else 2)
    z = (2 + a, 3 + a)
    required = [(1 << y[c], 1 << c) for c in range(2)]
    required += [(1 << c, 1 << z[c]) for c in range(2)]
    subsets = [mask for mask in range(1, 128) if mask.bit_count() <= 4]
    rectangles = []
    for predecessors in subsets:
        for successors in subsets:
            p, c = predecessors.bit_count(), successors.bit_count()
            if (predecessors & successors).bit_count() > 1:
                continue
            if p == 1 and predecessors & ~(p_only | common):
                continue
            if c == 1 and successors & ~(c_only | common):
                continue
            if (p, c) in ((1, 4), (4, 1)):
                continue
            if predecessors & common and c > 2:
                continue
            if successors & common and p > 2:
                continue
            rectangle = predecessors, successors
            if p == 1 and predecessors & common and rectangle not in required:
                continue
            if c == 1 and successors & common and rectangle not in required:
                continue
            if any(
                predecessors & other[0] and successors & other[1] and rectangle != other
                for other in required
            ):
                continue
            rectangles.append(rectangle)
    search_type = MultiplicitySearch if require_multiplicity else RectangleSearch
    return search_type(7, 4, rectangles), required


def main():
    # Exercise the inherited recursion and the selected-rectangle recorder
    # on a complete cover that satisfies the multiplicity test.
    unit_grid = [(1 << x, 1 << y) for x in range(7) for y in range(7)]
    control = MultiplicitySearch(7, 7, unit_grid)
    assert control.has_cover(unit_grid[:4])
    assert control.raw_covers == 1
    assert control.multiplicities == {(7, 7, 7, 7): 1}
    assert not MultiplicitySearch(7, 7, unit_grid[:-1]).has_cover()

    cases = (
        (1, 4, False, False, 1221, 729097),
        (2, 3, False, False, 1223, 754820),
        (3, 2, False, False, 1223, 800282),
        (2, 3, True, True, 1170, 528692),
    )
    for a, b, distinct_y, multiplicity, candidates, nodes in cases:
        start = perf_counter()
        search, required = normalized_case(a, b, distinct_y, multiplicity)
        assert len(search.rectangles) == candidates
        assert not search.has_cover(required)
        assert search.nodes == nodes
        if multiplicity:
            assert search.raw_covers == 20
            assert search.multiplicities == {(2, 2, 1, 2): 10, (2, 2, 2, 1): 10}
        covers = f"; {search.raw_covers} raw covers" if multiplicity else ""
        print(
            f"a={a}, b={b}, distinct_y={distinct_y}: {candidates} rectangles; "
            f"{nodes} states{covers}; no survivor; {perf_counter()-start:.3f}s"
        )


if __name__ == "__main__":
    main()
