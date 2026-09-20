#!/usr/bin/env python3
"""Search odd-order E1483 models with a specified minimum translation rank.

UNSAT is exploratory, not a Lean refutation. The translation and constant-row
certificates justify the extra constraints. Relabeling chooses row 0 to have
minimum rank, and the first-row symmetry break respects input labels.
"""

import argparse
import itertools
import json
import math
import time
from pathlib import Path

import numpy as np

from definability_twisted_check import satisfies
from spectrum_generate import load_equations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def search(
    n,
    rank,
    seconds,
    solver_name="cadical195",
    constraints="collisions",
    normalize_first_row=False,
):
    """Return (status, table) for the minimum-rank case, verifying any model."""
    assert n >= 3 and n % 2 == 1 and 2 <= rank < n and seconds > 0
    assert constraints in ("basic", "edges", "collisions")
    start = time.monotonic()
    pool = IDPool()
    solver = Solver(name=solver_name)
    truth = pool.id("true")
    solver.add_clause([truth])

    def add(clause):
        if truth not in clause:
            solver.add_clause([v for v in clause if v != -truth])

    def exactly(variables):
        for clause in CardEnc.equals(
            variables, 1, vpool=pool, encoding=EncType.seqcounter
        ):
            add(clause)

    p = lambda x, y, z: pool.id(("p", x, y, z))
    row = lambda x, z: pool.id(("row", x, z))
    col = lambda x, z: pool.id(("col", x, z))
    good = lambda x, a, b: pool.id(("good", x, a, b))
    dual = lambda x, a, b: pool.id(("dual", x, a, b))
    for x, y in itertools.product(range(n), repeat=2):
        exactly([p(x, y, z) for z in range(n)])

    # Fix 0. In a lexicographically least
    # first row, a new output z cannot precede z-1 while BOTH names have
    # not yet occurred as inputs or outputs: swapping them would reduce
    # that row. Input labels matter here; unrestricted output precedence
    # on a multiplication table is not a valid symmetry break.
    fixed = 1
    seen = lambda i, z: pool.id(("seen", i, z)) if i >= 0 else -truth
    for i in range(n):
        x, y = divmod(i, n)
        for z in range(fixed, n):
            old, new, value = seen(i - 1, z), seen(i, z), p(x, y, z)
            add([-old, new])
            add([-value, new])
            add([-new, old, value])
            if z > max(fixed, y + 1):
                add([-value, seen(i - 1, z - 1)])

    for y, z, b in itertools.product(range(n), repeat=3):
        add([-p(y, z, b), row(y, b)])
        add([-p(z, y, b), col(y, b)])
    for y, b in itertools.product(range(n), repeat=2):
        add([-row(y, b)] + [p(y, z, b) for z in range(n)])
        add([-col(y, b)] + [p(z, y, b) for z in range(n)])
    for x, a, b, c in itertools.product(range(n), repeat=4):
        add([-good(x, a, b), -p(x, b, c), p(a, c, x)])
        add([-dual(x, a, b), -p(b, x, c), p(c, a, x)])
    for x, y, a, b in itertools.product(range(n), repeat=4):
        add([-p(y, x, a), -row(y, b), good(x, a, b)])
        add([-p(x, y, a), -col(y, b), dual(x, a, b)])

    # Translation identities proved in check_definability_1483_dual.lean.
    for x, b, c in itertools.product(range(n), repeat=3):
        add([-col(x, b), -p(x, b, c), p(c, x, b)])
        add([-row(x, b), -p(b, x, c), p(x, c, b)])

    # Odd order excludes constant and bijective rows. By relabeling, row 0
    # can be chosen to have minimum rank k; translation images are equipotent.
    k = rank
    for x in range(n):
        for image in (row, col):
            for clause in CardEnc.atleast(
                [image(x, z) for z in range(n)],
                k,
                vpool=pool,
                encoding=EncType.seqcounter,
            ):
                add(clause)
            add([-image(x, z) for z in range(n)])
    for image in (row, col):
        for clause in CardEnc.atmost(
            [image(0, z) for z in range(n)], k, vpool=pool, encoding=EncType.seqcounter
        ):
            add(clause)

    if constraints != "basic":
        rk = lambda x, r: pool.id(("rank", x, r))
        for x in range(n):
            exactly([rk(x, r) for r in range(rank, n)])
            for r in range(rank, n):
                for image in (row, col):
                    for clause in CardEnc.equals(
                        [image(x, z) for z in range(n)],
                        r,
                        vpool=pool,
                        encoding=EncType.seqcounter,
                    ):
                        add([-rk(x, r)] + clause)
            for clause in CardEnc.atleast(
                [row(x, z) for z in range(n)],
                math.isqrt(n - 1) + 1,
                vpool=pool,
                encoding=EncType.seqcounter,
            ):
                add([-p(x, x, x)] + clause)
        add([rk(0, rank)])
        for x, y, r, s in itertools.product(
            range(n), range(n), range(rank, n), range(rank, n)
        ):
            if r * s < n:
                add([-row(x, y), -rk(x, r), -rk(y, s)])
                add([-col(x, y), -rk(x, r), -rk(y, s)])
    if constraints == "collisions":
        sameL = lambda a, x, y: pool.id(("sameL", a, x, y))
        sameR = lambda a, x, y: pool.id(("sameR", a, x, y))
        for a in range(n):
            for x, y in itertools.combinations(range(n), 2):
                l, r = sameL(a, x, y), sameR(a, x, y)
                for z in range(n):
                    add([-p(a, x, z), -p(a, y, z), l])
                    add([-l, -p(a, x, z), p(a, y, z)])
                    add([-p(x, a, z), -p(y, a, z), r])
                    add([-r, -p(x, a, z), p(y, a, z)])
        for a, b in itertools.product(range(n), repeat=2):
            for x, y in itertools.combinations(range(n), 2):
                add([-row(a, b), -sameL(a, x, y), -sameR(b, x, y)])
                add([-col(a, b), -sameL(b, x, y), -sameR(a, x, y)])
    if normalize_first_row:
        # Normalize the first-row image separately according to whether it contains 0.
        for y in range(n):
            add([-row(0, 0)] + [p(0, y, z) for z in range(rank)])
            add([row(0, 0)] + [p(0, y, z) for z in range(1, rank + 1)])
        # Labels beyond rank lie outside either normalized image and can be sorted.
        for y in range(rank + 1, n - 1):
            for z, w in itertools.product(range(rank + 1), repeat=2):
                if z > w:
                    add([-p(0, y, z), -p(0, y + 1, w)])
    try:
        # CaDiCaL can resume after a conflict budget. Small successive budgets
        # allow us to honor the wall-clock limit without an unsupported interrupt.
        result = None
        while time.monotonic() - start < seconds:
            solver.conf_budget(1000)
            result = solver.solve_limited()
            if result is not None:
                break
        if result is None:
            return "unknown", None
        if not result:
            return "unsat", None
        model = {v for v in solver.get_model() if v > 0}
        table = [
            [next(z for z in range(n) if p(x, y, z) in model) for y in range(n)]
            for x in range(n)
        ]
        array = np.array(table)
        assert satisfies(load_equations()[1482], array)
        ranks = [len(set(row_values)) for row_values in table]
        assert ranks[0] == min(ranks) == rank
        return "sat", table
    finally:
        solver.delete()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("order", type=int)
    parser.add_argument("minimum_rank", type=int)
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument(
        "--solver", choices=("cadical195", "maplecm", "glucose42"), default="cadical195"
    )
    parser.add_argument(
        "--constraints",
        choices=("basic", "edges", "collisions"),
        default="collisions",
        help="basic: image ranks; edges: exact rank/product bounds; collisions: also joint injectivity",
    )
    parser.add_argument(
        "--normalize-first-row",
        action="store_true",
        help="normalize the first row image, separately for whether it contains 0, and sort remaining inputs",
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if (
        args.order < 3
        or args.order % 2 != 1
        or not 2 <= args.minimum_rank < args.order
        or args.seconds <= 0
    ):
        parser.error(
            "require odd order >= 3, rank between 2 and order-1, and positive seconds"
        )
    status, table = search(
        args.order,
        args.minimum_rank,
        args.seconds,
        args.solver,
        args.constraints,
        args.normalize_first_row,
    )
    result = {
        "source": 1483,
        "order": args.order,
        "minimum_rank": args.minimum_rank,
        "status": status,
        "solver": args.solver,
        "constraints": args.constraints,
        "normalize_first_row": args.normalize_first_row,
        "seconds": args.seconds,
        "trust": "independently verified model if SAT; no formal UNSAT certificate",
    }
    if table is not None:
        result["table"] = table
    print(json.dumps(result), flush=True)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
