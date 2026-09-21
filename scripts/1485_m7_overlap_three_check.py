#!/usr/bin/env python3
"""Exclude three common singleton labels when r=4, |Z|=7, p=7.

This enumerates necessary central rectangle systems, not multiplication
tables. No solver is used.
"""

from time import perf_counter


class RectangleSearch:
    """Exact covers with fixed row/column rectangle counts and orthogonality."""

    def __init__(self, size, degree, rectangles):
        self.size = size
        self.degree = degree
        self.rectangles = rectangles
        self.nodes = 0
        self.rows = [0] * size
        self.columns = [0] * size
        self.cells = [0] * (size * size)
        self.covers = []
        for index, (predecessors, successors) in enumerate(rectangles):
            bit = 1 << index
            covered = 0
            for x in range(size):
                if predecessors >> x & 1:
                    self.rows[x] |= bit
                    for y in range(size):
                        if successors >> y & 1:
                            self.cells[size * x + y] |= bit
                            covered |= 1 << (size * x + y)
                if successors >> x & 1:
                    self.columns[x] |= bit
            self.covers.append(covered)
        self.compatible = []
        for predecessors, successors in rectangles:
            mask = 0
            for index, (other_predecessors, other_successors) in enumerate(rectangles):
                if predecessors & other_predecessors and successors & other_successors:
                    continue
                if (predecessors & other_successors).bit_count() > 1:
                    continue
                if (other_predecessors & successors).bit_count() > 1:
                    continue
                mask |= 1 << index
            self.compatible.append(mask)

    def add(self, index, active, uncovered, row_counts, column_counts):
        """Select a rectangle; eliminate overlaps and incompatible rectangles."""
        if not (active >> index & 1):
            return None
        predecessors, successors = self.rectangles[index]
        active &= self.compatible[index]
        uncovered ^= self.covers[index]
        row_counts = list(row_counts)
        column_counts = list(column_counts)
        for x in range(self.size):
            if predecessors >> x & 1:
                row_counts[x] += 1
                if row_counts[x] > self.degree:
                    return None
                if row_counts[x] == self.degree:
                    active &= ~self.rows[x]
            if successors >> x & 1:
                column_counts[x] += 1
                if column_counts[x] > self.degree:
                    return None
                if column_counts[x] == self.degree:
                    active &= ~self.columns[x]
        return active, uncovered, tuple(row_counts), tuple(column_counts)

    def search(self, active, uncovered, row_counts, column_counts):
        self.nodes += 1
        if not uncovered:
            return all(count == self.degree for count in row_counts + column_counts)

        # Each still-needed rectangle covers at least one cell on its line.
        # If only one rectangle remains, it must cover every remaining cell.
        full_line = (1 << self.size) - 1
        max_block = self.size - self.degree + 1
        for x in range(self.size):
            row_cells = (uncovered >> (self.size * x) & full_line).bit_count()
            column_cells = sum(
                uncovered >> (self.size * y + x) & 1 for y in range(self.size)
            )
            row_slots = self.degree - row_counts[x]
            column_slots = self.degree - column_counts[x]
            if not row_slots <= row_cells <= max_block * row_slots:
                return False
            if not column_slots <= column_cells <= max_block * column_slots:
                return False
            for slots, cells, line, side in (
                (row_slots, row_cells, self.rows[x], 1),
                (column_slots, column_cells, self.columns[x], 0),
            ):
                if slots != 1:
                    continue
                possible = active & line
                while possible:
                    bit = possible & -possible
                    possible ^= bit
                    index = bit.bit_length() - 1
                    if self.rectangles[index][side].bit_count() != cells:
                        active &= ~bit

        # Every completion covers the chosen uncovered cell once. Branch
        # over ALL its compatible rectangles; minimizing choices is optional.
        remaining = uncovered
        choices = 0
        minimum = len(self.rectangles) + 1
        while remaining:
            cell_bit = remaining & -remaining
            remaining ^= cell_bit
            cell = cell_bit.bit_length() - 1
            possible = active & self.cells[cell]
            count = possible.bit_count()
            if count < minimum:
                choices, minimum = possible, count
            if count <= 1:
                break
        while choices:
            bit = choices & -choices
            choices ^= bit
            state = self.add(bit.bit_length() - 1, active, uncovered, row_counts, column_counts)
            if state is not None and self.search(*state):
                return True
        return False

    def has_cover(self, required=()):
        state = (
            (1 << len(self.rectangles)) - 1,
            (1 << (self.size * self.size)) - 1,
            (0,) * self.size,
            (0,) * self.size,
        )
        for rectangle in required:
            state = self.add(self.rectangles.index(rectangle), *state)
            if state is None:
                return False
        return self.search(*state)


def normalized_case(different):
    """Labels: predecessor-only 0,1; common 2,3,4; successor-only 5,6."""
    common = 0b0011100
    predecessor_only = 0b0000011
    successor_only = 0b1100000
    predecessor_map = {2: 0, 3: 0, 4: 1}
    successor_map = {2: 5, 3: 6 if different else 5, 4: 5 if different else 6}
    required = [(1 << predecessor_map[c], 1 << c) for c in predecessor_map]
    required += [(1 << c, 1 << successor_map[c]) for c in successor_map]
    subsets = [mask for mask in range(1, 1 << 7) if mask.bit_count() <= 4]
    rectangles = []
    for predecessors in subsets:
        for successors in subsets:
            p, c = predecessors.bit_count(), successors.bit_count()
            if (predecessors & successors).bit_count() > 1:
                continue
            if p == 1 and predecessors & successor_only:
                continue
            if c == 1 and successors & predecessor_only:
                continue
            if (p, c) in ((4, 1), (1, 4)):
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
                predecessors & other_p and successors & other_c and rectangle != other
                for other in required
                for other_p, other_c in (other,)
            ):
                continue
            rectangles.append(rectangle)
    return RectangleSearch(7, 4, rectangles), required


def main():
    # Positive and negative controls for exact cover and line-count pruning.
    unit_grid = [(1 << x, 1 << y) for x in range(2) for y in range(2)]
    assert RectangleSearch(2, 2, unit_grid).has_cover()
    assert not RectangleSearch(2, 2, unit_grid[:-1]).has_cover()
    for different, expected_nodes in ((False, 8112), (True, 16838)):
        start = perf_counter()
        search, required = normalized_case(different)
        assert len(search.rectangles) == 605
        assert not search.has_cover(required)
        assert search.nodes == expected_nodes
        case = "different doubled pairs" if different else "same doubled pair"
        print(f"{case}: 605 rectangles; {search.nodes} states; no cover; {perf_counter()-start:.3f}s")


if __name__ == "__main__":
    main()
