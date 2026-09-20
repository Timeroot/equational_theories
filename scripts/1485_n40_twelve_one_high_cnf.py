#!/usr/bin/env python3
"""Encode necessary A12/B8 one-high incidence conditions as Boolean CNF.

This does not solve or certify the CNF. Use a separately checked SAT
refutation before claiming an exclusion. The two no-loop cases normalize
the unique high vertex's successor to medium vertex 1 or low vertex 3.
All cardinalities are encoded here, without an SMT-to-CNF conversion.
"""

import argparse
from itertools import product
from pathlib import Path
from time import perf_counter


N = 8
SHARP = (3, 2, 2, 1, 1, 1, 1, 1)
DEGREE = tuple(4 - value for value in SHARP)


class CNF:
    """Literal 1 is true; -1 is false. Other variables start at 2."""

    def __init__(self):
        self.variables = 1
        self.clauses = [(1,)]
        self.gates = {}
        self.definitions = []
        self.counters = {}

    def variable(self):
        self.variables += 1
        return self.variables

    def clause(self, literals):
        values = set(literals)
        if 1 in values or any(-value in values for value in values):
            return
        values.discard(-1)
        self.clauses.append(tuple(sorted(values)))

    def imply(self, guards, literals):
        self.clause([-guard for guard in guards] + list(literals))

    def conjunction(self, literals):
        values = set(literals)
        if -1 in values or any(-value in values for value in values):
            return -1
        values.discard(1)
        key = tuple(sorted(values))
        if not key:
            return 1
        if len(key) == 1:
            return key[0]
        if key not in self.gates:
            output = self.variable()
            self.gates[key] = output
            self.definitions.append((output, key))
            for literal in key:
                self.clause([-output, literal])
            self.clause([output] + [-literal for literal in key])
        return self.gates[key]

    def disjunction(self, literals):
        return -self.conjunction([-literal for literal in literals])

    def thresholds(self, literals, limit):
        """Return ge[k] iff at least k listed events hold, for 0<=k<=limit.

        Repeated literals remain repeated: distinct paths can have the same
        Boolean event, but still contribute separately to the path count.
        """
        key = tuple(sorted(literals))
        if key in self.counters and len(self.counters[key]) > limit:
            return self.counters[key][:limit + 1]
        previous = [1] + [-1] * limit
        for literal in key:
            following = [1]
            for k in range(1, limit + 1):
                both = self.conjunction([literal, previous[k - 1]])
                following.append(self.disjunction([previous[k], both]))
            previous = following
        self.counters[key] = previous
        return previous

    def at_most(self, literals, bound):
        if bound < 0:
            return -1
        return -self.thresholds(literals, bound + 1)[bound + 1]

    def exact(self, literals, count):
        ge = self.thresholds(literals, count + 1)
        self.clause([ge[count]])
        self.clause([-ge[count + 1]])

    def evaluate_extension(self, inputs):
        values = {1: True, **inputs}

        def truth(literal):
            return values[abs(literal)] == (literal > 0)

        for output, literals in self.definitions:
            values[output] = all(truth(literal) for literal in literals)
        return values, truth


def test_counter_encoding():
    for count in range(1, 5):
        cnf = CNF()
        inputs = [cnf.variable() for _ in range(count)]
        events = inputs + [inputs[0], -inputs[-1], 1, -1]
        ge = cnf.thresholds(events, len(events) + 1)
        for assignment in product((False, True), repeat=count):
            _, truth = cnf.evaluate_extension(dict(zip(inputs, assignment)))
            assert all(any(truth(lit) for lit in clause) for clause in cnf.clauses)
            actual = sum(truth(lit) for lit in events)
            assert all(truth(lit) == (actual >= k) for k, lit in enumerate(ge))

    # Check the optional five-cycle Boolean pattern encoding independently.
    for bad in product((False, True), repeat=5):
        encoded = all(not (bad[i] and not bad[(i + 1) % 5]) or
                      (bad[(i - 1) % 5] and not bad[(i - 2) % 5]
                       and not bad[(i + 2) % 5]) for i in range(5))
        expected = (sum(bad) in (0, 5) or
                    (sum(bad) == 2 and any(bad[i] and bad[(i + 1) % 5]
                                           for i in range(5))))
        assert encoded == expected


def build(successor, five_cycle=False):
    cnf = CNF()
    D = [[cnf.variable() for _ in range(N)] for _ in range(N)]
    C = [[cnf.variable() for _ in range(N)] for _ in range(N)]
    conjunction = cnf.conjunction
    beta = [[None] * N for _ in range(N)]
    eta = [[None] * N for _ in range(N)]
    square = [[None] * N for _ in range(N)]

    for i in range(N):
        cnf.exact(D[i], DEGREE[i])
        cnf.exact([D[x][i] for x in range(N)], DEGREE[i])
        cnf.exact(C[i], SHARP[i])
        cnf.exact([C[x][i] for x in range(N)], SHARP[i])

    for b, d in product(range(N), repeat=2):
        paths = [conjunction([D[b][x], D[x][d]]) for x in range(N)]
        square[b][d] = cnf.disjunction(paths)
        cnf.imply([-C[b][d]], [cnf.at_most(paths, 1)])
        if SHARP[b] + SHARP[d] > 5:
            cnf.clause([C[b][d]])
        if SHARP[b] + SHARP[d] > 4:
            cnf.clause([C[b][d], square[b][d]])
        beta[b][d] = [conjunction([C[b][x], D[d][x]]) for x in range(N)]
        eta[b][d] = [conjunction([D[x][b], C[x][d]]) for x in range(N)]
        first = cnf.thresholds(beta[b][d], N)
        second = cnf.thresholds(eta[b][d], N)
        for k in range(1, N + 1):
            cnf.imply([D[b][d], first[k]], [second[k]])
            cnf.imply([D[b][d], second[k]], [first[k]])

    for b, d in product(range(N), repeat=2):
        good_B = [conjunction([D[d][x], D[x][y], D[y][b],
                               -C[d][y], -C[x][b]])
                  for x, y in product(range(N), repeat=2)]
        sharp_sum = SHARP[b] + SHARP[d]
        cnf.imply([C[b][d]], [cnf.at_most(good_B, 8 - sharp_sum)])
        cnf.imply([-C[b][d], square[b][d]],
                  [cnf.at_most(good_B, 5 - sharp_sum)])
        cnf.imply([-C[b][d], -square[b][d]],
                  [cnf.at_most(good_B, 4 - sharp_sum)])

        mixed = good_B + [conjunction([C[d][x], D[x][b]]) for x in range(N)]
        mixed += [conjunction([D[d][x], C[x][b]]) for x in range(N)]
        mixed_ge = cnf.thresholds(mixed, 5)
        cnf.clause([-mixed_ge[5]])  # K<=4 for EVERY return, including Top.
        for e in range(N):
            guards = [-C[b][d], D[b][e], D[e][d]]
            beta_ge = cnf.thresholds(beta[e][d], 5)
            eta_ge = cnf.thresholds(eta[b][e], 5)
            # K+beta<=4 and K+eta<=4: forbid every split of five.
            for k in range(6):
                cnf.imply(guards, [-mixed_ge[k], -beta_ge[5 - k]])
                cnf.imply(guards, [-mixed_ge[k], -eta_ge[5 - k]])
            # K+beta+eta>=3; unary prefixes preserve this threshold.
            small = mixed_ge[1:4] + beta_ge[1:4] + eta_ge[1:4]
            cnf.imply(guards, [cnf.thresholds(small, 3)[3]])

    # This consequence is analytic, not dependent on the high-loop checker.
    for p, q in product(range(N), repeat=2):
        cnf.imply([D[p][0], D[0][q]], [C[p][q]])

    # Positive control: a near-candidate satisfying every preceding condition.
    # It is deliberately rejected by the one-A closure added next.
    control_C = ((0, 1, 2), (0, 1), (0, 2), (3,), (4,), (5,), (6,), (7,))
    control_D = ((0,), (3, 7), (3, 4), (1, 2, 6), (2, 5, 7),
                 (4, 6, 7), (3, 5, 6), (1, 4, 5))
    inputs = {table[i][j]: j in rows[i]
              for table, rows in ((D, control_D), (C, control_C))
              for i, j in product(range(N), repeat=2)}
    _, truth = cnf.evaluate_extension(inputs)
    assert all(any(truth(lit) for lit in clause) for clause in cnf.clauses)

    before_closure = len(cnf.clauses)
    for a, b, c, d in product(range(N), repeat=4):
        guards = [D[a][b], D[b][c], D[c][d], C[d][a]]
        cnf.imply(guards + [C[a][c]], [C[b][d]])
        cnf.imply(guards + [C[b][d]], [C[a][c]])
    assert not all(any(truth(lit) for lit in clause)
                   for clause in cnf.clauses[before_closure:])

    if five_cycle:
        # The general four-degree cycle lemma permits exactly 0, two
        # adjacent, or 5 bad positions. One cyclic representative suffices.
        for cycle in product(range(N), repeat=5):
            if cycle != min(cycle[i:] + cycle[:i] for i in range(5)):
                continue
            edges = [D[cycle[i]][cycle[(i + 1) % 5]] for i in range(5)]
            bad = [C[cycle[i]][cycle[(i + 2) % 5]] for i in range(5)]
            for i in range(5):
                guards = edges + [bad[i], -bad[(i + 1) % 5]]
                for conclusion in (bad[(i - 1) % 5], -bad[(i - 2) % 5],
                                   -bad[(i + 2) % 5]):
                    cnf.imply(guards, [conclusion])

    cnf.clause([D[0][successor]])
    return cnf, D, C


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--successor', choices=('medium', 'low'), required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--five-cycle', action='store_true',
                        help='also enforce the all-B five-cycle pattern theorem')
    args = parser.parse_args()
    started = perf_counter()
    test_counter_encoding()
    cnf, D, C = build(1 if args.successor == 'medium' else 3, args.five_cycle)
    with args.output.open('w') as stream:
        stream.write('c E1485 order40 A12/B8, one high, successor ' + args.successor + '\n')
        for name, table in (('D', D), ('C', C)):
            for i, row in enumerate(table):
                stream.write(f'c {name}[{i}] ' + ' '.join(map(str, row)) + '\n')
        stream.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            stream.write(' '.join(map(str, clause)) + ' 0\n')
    print(f'{args.successor}: {cnf.variables} variables, {len(cnf.clauses)} clauses')
    print(f'Counter truth tables and pre-closure near-candidate passed; {perf_counter()-started:.3f}s')
    print(args.output)


if __name__ == '__main__':
    main()
