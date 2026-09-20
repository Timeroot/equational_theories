#!/usr/bin/env python3
"""Encode the eight ten-vertex expansion obstructions without auxiliaries.

This is a necessary-incidence encoding, not a magma-table search. A solver
report alone is not a proof: check its LRAT refutation independently. See
docs/1485_order_forty_ten_profile_expansion.md for the mathematical reduction.
"""

import argparse
from itertools import combinations, product
from pathlib import Path
from time import perf_counter


N = 10
D = [[1 + N * i + j for j in range(N)] for i in range(N)]
C = [[1 + N * N + N * i + j for j in range(N)] for i in range(N)]


def clause(literals):
    """Remove duplicate literals; a tautology needs no clause."""
    values = set(literals)
    if any(-literal in values for literal in values):
        return None
    return tuple(sorted(values))


def exact(literals, count):
    """Direct subset encoding: no counters, gates, or solver conversion."""
    return [tuple(-v for v in part) for part in combinations(literals, count + 1)] + [
        part for part in combinations(literals, len(literals) - count + 1)
    ]


def base_clauses():
    result = []

    def add(literals):
        normalized = clause(literals)
        if normalized is not None:
            result.append(normalized)

    for matrix, degree in ((D, 3), (C, 1)):
        for i in range(N):
            result.extend(exact(matrix[i], degree))
            result.extend(exact([matrix[j][i] for j in range(N)], degree))

    # Two distinct internal middles force a sharp A middle.
    for a, c in product(range(N), repeat=2):
        for b, d in combinations(range(N), 2):
            add([-D[a][b], -D[b][c], -D[a][d], -D[d][c], C[a][c]])

    for a, b, c, d in product(range(N), repeat=4):
        # C is a permutation. C[a,c] and C[d,b] identify the unique
        # possible bad successor and predecessor on the edge a D b.
        guards = [-D[a][b], -C[a][c], -C[d][b]]
        add(guards + [-D[b][c], D[d][a]])
        add(guards + [D[b][c], -D[d][a]])
        # The closed walk a D b D c D d C a has one sharp A middle.
        # Its only possibly bad positions must agree, also with repeats.
        guards = [-D[a][b], -D[b][c], -D[c][d], -C[d][a]]
        add(guards + [-C[a][c], C[b][d]])
        add(guards + [C[a][c], -C[b][d]])
    return result


def normalization(size, overlap):
    """S={0,1,2}, and its exact predecessor set P, modulo relabeling."""
    assert size in (3, 4) and overlap in range(4)
    predecessors = set(range(overlap)) | set(range(3, 3 + size - overlap))
    assert len(predecessors) == size
    assert len(predecessors & set(range(3))) == overlap
    result = []
    for b in range(N):
        if b in predecessors:
            result.append(tuple(D[b][d] for d in range(3)))
        else:
            result.extend((-D[b][d],) for d in range(3))
    return result


def satisfies(clauses, values):
    return all(any(values[abs(literal)] == (literal > 0) for literal in row)
               for row in clauses)


def controls(clauses):
    # Exhaustive truth tables audit both direct cardinality encodings.
    variables = tuple(range(1, N + 1))
    for count in (1, 3):
        encoded = exact(variables, count)
        for assignment in product((False, True), repeat=N):
            assert satisfies(encoded, dict(zip(variables, assignment))) == (sum(assignment) == count)

    # Genuine positive control for ALL unnormalized incidence constraints:
    # Petersen adjacency, C=identity. This is not claimed to be a magma.
    vertices = list(combinations(range(5), 2))
    rows = [{j for j, other in enumerate(vertices) if not set(vertex) & set(other)}
            for vertex in vertices]
    values = {D[i][j]: j in rows[i] for i, j in product(range(N), repeat=2)}
    values.update({C[i][j]: i == j for i, j in product(range(N), repeat=2)})
    assert all(len(row) == 3 for row in rows)
    assert all(sum(j in row for row in rows) == 3 for j in range(N))
    assert satisfies(clauses, values)
    assert min(len(set().union(*(rows[j] for j in subset)))
               for subset in combinations(range(N), 3)) == 6
    for size, overlap in product((3, 4), range(4)):
        assert not satisfies(normalization(size, overlap), values)
    # A missing degree entry and a non-permutation C are detected.
    broken = dict(values)
    broken[D[0][next(iter(rows[0]))]] = False
    assert not satisfies(clauses, broken)
    broken = dict(values)
    broken[C[0][0]] = False
    assert not satisfies(clauses, broken)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--predecessors', type=int, choices=(3, 4), required=True)
    parser.add_argument('--overlap', type=int, choices=range(4), required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    start = perf_counter()
    clauses = base_clauses()
    controls(clauses)
    clauses.extend(normalization(args.predecessors, args.overlap))
    with args.output.open('w') as stream:
        stream.write(f'c E1485 A10 expansion, predecessor size {args.predecessors}, overlap {args.overlap}\n')
        stream.write(f'p cnf {2 * N * N} {len(clauses)}\n')
        for row in clauses:
            stream.write(' '.join(map(str, row)) + ' 0\n')
    print(f'{2 * N * N} variables; {len(clauses)} clauses; '
          f'controls passed; {perf_counter() - start:.3f}s; {args.output}')


if __name__ == '__main__':
    main()
