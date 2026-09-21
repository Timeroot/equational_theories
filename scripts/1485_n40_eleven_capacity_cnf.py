#!/usr/bin/env python3
"""Deterministic necessary-incidence/profile CNFs for A11/B9 at order40.

A negative solver report is not a certificate. Independently check the
LRAT refutation before claiming an exclusion of the encoded constraints.
"""

import argparse
from itertools import combinations, product
from pathlib import Path
from runpy import run_path
from time import perf_counter


SHARED = run_path(str(Path(__file__).with_name("1485_n40_twelve_one_high_cnf.py")))
CNF = SHARED["CNF"]
N = 9


def common(sharp):
    cnf = CNF()
    D = [[cnf.variable() for _ in range(N)] for _ in range(N)]
    C = [[cnf.variable() for _ in range(N)] for _ in range(N)]
    eta = [[None] * N for _ in range(N)]
    eta_ge = [[None] * N for _ in range(N)]
    for i in range(N):
        for table, degree in ((D, 4 - sharp[i]), (C, sharp[i])):
            cnf.exact(table[i], degree)
            cnf.exact([table[j][i] for j in range(N)], degree)
    for a, c in product(range(N), repeat=2):
        if sharp[a] + sharp[c] > 5:
            cnf.clause([C[a][c]])
        for b, d in combinations(range(N), 2):
            cnf.imply([D[a][b], D[b][c], D[a][d], D[d][c]], [C[a][c]])
    for b, d in product(range(N), repeat=2):
        beta = [cnf.conjunction([C[b][x], D[d][x]]) for x in range(N)]
        eta[b][d] = [cnf.conjunction([D[y][b], C[y][d]]) for y in range(N)]
        # The margins imply beta<=j_b and eta<=j_d. Equality therefore
        # needs only these thresholds, not an unbounded counting assertion.
        limit = max(sharp[b], sharp[d])
        beta_ge = cnf.thresholds(beta, limit)
        eta_ge[b][d] = cnf.thresholds(eta[b][d], limit)
        for k in range(1, limit + 1):
            cnf.imply([D[b][d], beta_ge[k]], [eta_ge[b][d][k]])
            cnf.imply([D[b][d], eta_ge[b][d][k]], [beta_ge[k]])
    for a, b, c, d in product(range(N), repeat=4):
        guards = [D[a][b], D[b][c], D[c][d], C[d][a]]
        cnf.imply(guards + [C[a][c]], [C[b][d]])
        cnf.imply(guards + [C[b][d]], [C[a][c]])
    return cnf, D, C, eta, eta_ge


def parameters(mode, size, high_count, overlap):
    high = 1 if mode == "onehigh" else 2
    if mode not in ("onehigh", "exceptional", "single"):
        raise ValueError("unknown mode")
    if size not in (3, 4) or mode == "exceptional" and size != 3:
        raise ValueError("invalid predecessor size")
    remaining = size - high_count - overlap
    if not (0 <= high_count <= high and 0 <= overlap <= 2 and 0 <= remaining <= 7 - high):
        raise ValueError("invalid overlap parameters")
    sharp = (3,) + (1,) * 8 if high == 1 else (2, 2) + (1,) * 7
    pair = (high, high + 1)
    predecessors = (set(range(high_count)) | set(range(high, high + overlap))
                    | set(range(high + 2, high + 2 + remaining)))
    assert len(predecessors) == size
    return sharp, pair, predecessors


def cases():
    for mode in ("onehigh", "exceptional", "single"):
        for size in (3, 4):
            for high_count in range(3):
                for overlap in range(3):
                    try:
                        parameters(mode, size, high_count, overlap)
                    except ValueError:
                        continue
                    yield mode, size, high_count, overlap


def profile_pair(cnf, D, eta_ge, pair, predecessors, capacity):
    d, e = pair
    epsilon = []
    for b in range(N):
        # Both selected targets have C-column sum1, so these are the
        # exact Boolean eta values, not merely lower-bound indicators.
        first, second = eta_ge[b][d][1], eta_ge[b][e][1]
        cnf.imply([D[b][d], D[b][e], first], [second])
        cnf.imply([D[b][d], D[b][e], second], [first])
        epsilon.append(cnf.disjunction([
            cnf.conjunction([D[b][d], first]),
            cnf.conjunction([D[b][e], second]),
        ]))
    required = 3 * len(predecessors) - capacity
    events = [epsilon[b] for b in sorted(predecessors)]
    cnf.clause([cnf.thresholds(events, required)[required]])


def single_coset(cnf, D, eta, sharp, pair):
    colors = [[cnf.variable() for _ in range(4)] for _ in range(N)]
    # M[b][p][k] says that the integer intersection M_bp is at least k+1.
    M = [[[cnf.variable() for _ in range(3)] for _ in range(4)] for _ in range(N)]
    for d in range(N):
        cnf.exact(colors[d], sharp[d])
    for p, total in enumerate((3, 3, 3, 2)):
        cnf.exact([colors[d][p] for d in range(N)], total)
    for b in range(N):
        for p in range(4):
            cnf.imply([M[b][p][1]], [M[b][p][0]])
            cnf.imply([M[b][p][2]], [M[b][p][1]])
        cnf.exact([M[b][p][k] for p in range(4) for k in range(3)], 4)
    for p, total in enumerate((8, 8, 8, 12)):
        cnf.exact([M[b][p][k] for b in range(N) for k in range(3)], total)
    for d in pair:
        cnf.clause([colors[d][0]])
    for b, d in product(range(N), repeat=2):
        count = [cnf.conjunction([colors[d][p], M[b][p][k]])
                 for p in range(4) for k in range(3)] + eta[b][d]
        ge = cnf.thresholds(count, 4)
        cnf.imply([D[b][d]], [ge[3]])
        cnf.imply([D[b][d]], [-ge[4]])
    return colors, M


def build(mode, size, high_count, overlap):
    sharp, pair, predecessors = parameters(mode, size, high_count, overlap)
    cnf, D, C, eta, eta_ge = common(sharp)
    for b in range(N):
        if b in predecessors:
            cnf.clause([D[b][d] for d in pair])
        else:
            for d in pair:
                cnf.clause([-D[b][d]])
    if mode != "onehigh":
        profile_pair(cnf, D, eta_ge, pair, predecessors, 7 if mode == "exceptional" else 8)
    if mode == "single":
        single_coset(cnf, D, eta, sharp, pair)
    return cnf


def controls():
    SHARED["test_counter_encoding"]()
    inventory = list(cases())
    assert len(inventory) == 37
    assert [sum(case[0] == mode for case in inventory)
            for mode in ("onehigh", "exceptional", "single")] == [12, 8, 17]

    # This necessary-incidence cover genuinely passes the common graph
    # constraints and capacity8 for a repeated low pair. It is NOT a magma.
    Drows = ((2, 3), (5, 8), (4, 6, 7), (1, 5, 8), (0, 2, 3),
             (2, 3, 4), (4, 6, 7), (1, 5, 8), (0, 6, 7))
    Crows = ((5, 6), (0, 1), (7,), (4,), (2,), (0,), (1,), (8,), (3,))
    cnf, D, C, _, eta_ge = common((2, 2) + (1,) * 7)
    inputs = {table[i][j]: j in rows[i]
              for table, rows in ((D, Drows), (C, Crows))
              for i, j in product(range(N), repeat=2)}
    _, truth = cnf.evaluate_extension(inputs)
    assert all(any(truth(lit) for lit in row) for row in cnf.clauses)
    profile_pair(cnf, D, eta_ge, (2, 3), {0, 4, 5}, 8)
    _, truth = cnf.evaluate_extension(inputs)
    assert all(any(truth(lit) for lit in row) for row in cnf.clauses)
    # Its pair intersections sum to exactly8: the stronger exceptional
    # capacity7 must reject it, providing an off-by-one negative control.
    profile_pair(cnf, D, eta_ge, (2, 3), {0, 4, 5}, 7)
    _, truth = cnf.evaluate_extension(inputs)
    assert not all(any(truth(lit) for lit in row) for row in cnf.clauses)

    # Audit the unary representation and every possible selected-color
    # intersection count against direct arithmetic, independently of a solver.
    for values in product(range(4), repeat=4):
        unary = [[value >= k + 1 for k in range(3)] for value in values]
        assert sum(sum(bits) for bits in unary) == sum(values)
        for selected in product((False, True), repeat=4):
            encoded = sum(selected[p] and unary[p][k] for p in range(4) for k in range(3))
            assert encoded == sum(value for value, include in zip(values, selected) if include)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("onehigh", "exceptional", "single"), required=True)
    parser.add_argument("--predecessors", type=int, choices=(3, 4), required=True)
    parser.add_argument("--highs", type=int, choices=(0, 1, 2), required=True)
    parser.add_argument("--overlap", type=int, choices=(0, 1, 2), required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        parameters(args.mode, args.predecessors, args.highs, args.overlap)
    except ValueError as error:
        parser.error(str(error))
    start = perf_counter()
    controls()
    cnf = build(args.mode, args.predecessors, args.highs, args.overlap)
    with args.output.open("w") as stream:
        stream.write(f"c E1485 A11 {args.mode}, predecessors {args.predecessors}, "
                     f"highs {args.highs}, overlap {args.overlap}\n")
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for row in cnf.clauses:
            stream.write(" ".join(map(str, row)) + " 0\n")
    print(f"{cnf.variables} variables; {len(cnf.clauses)} clauses; controls passed; "
          f"{perf_counter()-start:.3f}s; {args.output}", flush=True)


if __name__ == "__main__":
    main()
