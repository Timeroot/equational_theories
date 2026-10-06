#!/usr/bin/env python3
"""Use a nearly satisfying Latin table as SAT phases, without fixing its entries.

The search covers all E667 models of the requested order. The initial table
need not satisfy E667. It only suggests branching phases; no isotope, symmetry
of the operation, or agreement with the input table is required.
"""
import argparse
import itertools
import json
import time

from pysat.solvers import Solver
from pysat.card import CardEnc
from spectrum_667_incremental import clauses
from spectrum_small_pair_search import load_equations, satisfies


def canonicalize(table, n):
    op = lambda x, y: table[x * n + y]
    zero = next((x for x in range(n) if op(x, x) != x), 0)
    unseen = set(range(n))

    def cycle(x):
        out = []
        while x not in out:
            out.append(x)
            unseen.remove(x)
            x = op(zero, x)
        assert x == out[0]
        return out

    first = cycle(zero)
    rest = []
    while unseen:
        rest.append(cycle(min(unseen)))
    labels = first + sum(sorted(rest, key=lambda c: (len(c), c)), [])
    inv = {x: i for i, x in enumerate(labels)}
    return [inv[op(x, y)] for x, y in itertools.product(labels, repeat=2)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument(
        "--record-index",
        type=int,
        help="Select an entry from a saved near-model records bundle",
    )
    parser.add_argument("--budget", type=int, default=2000000)
    parser.add_argument(
        "--max-changes",
        type=int,
        help="Restrict to tables differing in at most this many cells",
    )
    args = parser.parse_args()
    source = json.load(open(args.input))
    if args.record_index is not None:
        source = source["records"][args.record_index]
    table = source["table"]
    if isinstance(table[0], list):
        table = sum(table, [])
    n = int(len(table) ** 0.5)
    assert n in (12, 15) and len(table) == n * n
    assert all(sorted(table[x * n : (x + 1) * n]) == list(range(n)) for x in range(n))
    assert all(
        sorted(table[x * n + y] for x in range(n)) == list(range(n)) for y in range(n)
    )
    table = canonicalize(table, n)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    ones = {p(x, y, table[x * n + y]) for x, y in itertools.product(range(n), repeat=2)}
    ones |= {
        n**3 + p(x, y, table[table[x * n + x] * n + y])
        for x, y in itertools.product(range(n), repeat=2)
    }
    phases = [v if v in ones else -v for v in range(1, 2 * n**3 + 1)]
    # A local Hamming ball is not invariant under arbitrary relabeling of its
    # candidate tables. Omit the canonical-row constraints for local repairs.
    cs = clauses(n, "normalized" if args.max_changes is None else "unnormalized")
    if args.max_changes is not None:
        if not 0 <= args.max_changes <= n * n:
            parser.error("max-changes must be between zero and the number of cells")
        cs += CardEnc.atmost(
            lits=[
                -p(x, y, table[x * n + y])
                for x, y in itertools.product(range(n), repeat=2)
            ],
            bound=args.max_changes,
            top_id=2 * n**3,
        ).clauses
    with Solver(name="cadical195", bootstrap_with=cs) as solver:
        solver.set_phases(phases)
        solver.conf_budget(args.budget)
        start = time.monotonic()
        answer = solver.solve_limited()
        result = dict(
            order=n,
            input=args.input,
            canonical_seed=table,
            scope="All E667 models; input table supplies phases only",
            budget=args.budget,
            seconds=time.monotonic() - start,
            status="SAT" if answer else "UNSAT" if answer is False else "UNKNOWN",
            stats=solver.accum_stats(),
        )
        if args.record_index is not None:
            result["record_index"] = args.record_index
        if args.max_changes is not None:
            result["max_changes"] = args.max_changes
            result["scope"] = (
                "Only tables within the specified Hamming distance; "
                "UNSAT does not exclude arbitrary models"
            )
        if answer:
            vals = set(solver.get_model())
            witness = [
                next(z for z in range(n) if p(x, y, z) in vals)
                for x, y in itertools.product(range(n), repeat=2)
            ]
            assert satisfies(*load_equations()[666], witness, n)
            result["table"] = witness
    with open(args.output, "w") as dest:
        json.dump(result, dest, indent=2)
        dest.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k != "canonical_seed"}))


if __name__ == "__main__":
    main()
