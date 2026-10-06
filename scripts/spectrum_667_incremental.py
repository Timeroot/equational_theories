#!/usr/bin/env python3
"""Bounded E667 model searches with reusable learned clauses.

The extra constraints are proved in Equation667ConstantDiagonal.lean and the
Equation667IdempotentTwelve/RightIdentityTwelve certificate modules. Results
are exploratory: UNKNOWN is not an exclusion, and UNSAT is not a Lean proof.
The normalized mode chooses a non-idempotent zero when one exists. Consequently
its first-cycle-one cases describe *fully* idempotent models. The separate
one-idempotent mode does not impose that normalization and includes mixed
idempotent/non-idempotent models.
"""
import argparse
import concurrent.futures
import itertools
import json
import time
from pathlib import Path

from pysat.solvers import Solver
from spectrum_small_pair_search import encode, load_equations, satisfies


def partitions(n, lo=1):
    if not n:
        yield []
    for k in range(lo, n + 1):
        for tail in partitions(n - k, k):
            yield [k] + tail


def clauses(n, mode):
    top, cs = encode(667, n, right=True, normalize=(mode == "normalized"))
    assert top == 2 * n**3
    r = range(n)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    q = lambda x, y, z: 1 + n**3 + (x * n + y) * n + z
    # The intermediate operation is q(x,y) = (x*x)*y, so every row is Latin.
    for x, z in itertools.product(r, repeat=2):
        row = [q(x, y, z) for y in r]
        cs.append(row)
        cs.extend([-a, -b] for a, b in itertools.combinations(row, 2))
    # A constant diagonal is impossible at orders divisible by three.
    assert n % 3 == 0
    for z in r:
        cs.append([-p(x, x, z) for x in r])
    if mode == "idempotent-free":
        cs.extend([[-p(x, x, x)] for x in r])
    # Complete Lean exclusions at order 12, proved in the two
    # Equation667*Twelve certificate modules (both have LRAT replays).
    # These forbid only the subclasses, not arbitrary order-12 models.
    if n == 12:
        cs.append([-p(x, x, x) for x in r])
        for e in r:
            cs.append([-p(x, e, x) for x in r])
    # Three-cycle, two-cycle, and square-fiber lemmas.
    for x, a, b in itertools.product(r, repeat=3):
        cs.append([-p(x, x, a), -p(x, a, b), -p(x, b, x), p(x, x, x)])
    for x, a in itertools.product(r, repeat=2):
        cs.append([-p(x, x, a), -p(x, a, x), p(a, a, a)])
    for e, x, y in itertools.product(r, repeat=3):
        cs.append([-p(e, e, e), -p(x, x, e), -p(e, x, y), p(e, y, x)])
        cs.append([-p(e, e, e), -p(e, x, y), -p(e, y, x), p(x, x, e)])
        cs.append([-p(e, e, e), -p(x, x, e), -p(e, x, y), p(y, y, e)])
    return cs


def work(task):
    n, mode, budget, worker, output, jobs = task
    cs = clauses(n, mode)
    r = range(n)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    dest = output / f"n{n}-{mode}-b{budget}-w{worker}.jsonl"
    with Solver(name="cadical195", bootstrap_with=cs) as solver, dest.open("w") as log:
        solver.configure({"seed": worker})
        for lengths in jobs:
            row, offset = [], 0
            for length in lengths:
                row += list(range(offset + 1, offset + length)) + [offset]
                offset += length
            assumptions = [p(0, y, z) for y, z in enumerate(row)]
            solver.conf_budget(budget)
            start = time.monotonic()
            answer = solver.solve_limited(assumptions=assumptions)
            record = dict(
                order=n,
                mode=mode,
                cycles=lengths,
                budget=budget,
                status="SAT" if answer else "UNSAT" if answer is False else "UNKNOWN",
                seconds=time.monotonic() - start,
                stats=solver.accum_stats(),
            )
            if answer:
                vals = set(solver.get_model())
                table = [
                    next(z for z in r if p(x, y, z) in vals)
                    for x, y in itertools.product(r, repeat=2)
                ]
                assert satisfies(*load_equations()[666], table, n)
                record["table"] = table
            elif answer is False:
                record["core"] = solver.get_core()
            line = json.dumps(record)
            log.write(line + "\n")
            log.flush()
            print(line, flush=True)
    return str(dest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("order", type=int, choices=(12, 15))
    parser.add_argument(
        "--mode",
        choices=("normalized", "one-idempotent", "idempotent-free"),
        default="normalized",
    )
    parser.add_argument(
        "--budget", type=int, default=50000, help="Conflicts per cycle case"
    )
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--output", type=Path, default=Path(".cache/e667-incremental"))
    args = parser.parse_args()
    if args.workers < 1 or args.budget < 1:
        parser.error("workers and budget must be positive")
    args.output.mkdir(parents=True, exist_ok=True)
    n = args.order
    first = (
        [1]
        if args.mode == "one-idempotent"
        else (
            range(4, n + 1)
            if args.mode == "idempotent-free"
            else [k for k in range(1, n + 1) if k != 3]
        )
    )
    # Any Latin square has some row with a fixed point: solve a*x=x.
    # In the idempotent-free subclass its row index is not that fixed point,
    # so we may choose it as zero and require a one-cycle in the tail.
    jobs = [
        [k] + tail
        for k in first
        for tail in partitions(n - k)
        if args.mode != "idempotent-free" or 1 in tail
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        list(
            pool.map(
                work,
                [
                    (n, args.mode, args.budget, i, args.output, jobs[i :: args.workers])
                    for i in range(args.workers)
                ],
            )
        )


if __name__ == "__main__":
    main()
