"""Finite countermodel search for the saved E1483 -> E1479 candidate.

This is an exploratory SAT calculation, not a Lean certificate. The factored
source constraints use E1483 and its separately proved dual identity. Value
precedence removes only permutations fixing the counterexample witnesses.
"""

import itertools
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def countermodel(term, n, seconds, diagonal, idempotent_case=None, regular=False):
    """Return (status, table); UNSAT covers the indicated witness type only."""
    assert n > 0 and seconds > 0
    if idempotent_case is not None:
        assert n >= 2 and not diagonal and idempotent_case in range(4)
    if n == 1 and not diagonal:
        return "unsat", None
    start = time.monotonic()
    pool = IDPool()
    solver = Solver(name="cadical195")
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

    # Fix 0 (and, in the distinct case, 1). In a lexicographically least
    # first row, a new output z cannot precede z-1 while BOTH names have
    # not yet occurred as inputs or outputs: swapping them would reduce
    # that row. Input labels matter here; unrestricted output precedence
    # on a multiplication table is not a valid symmetry break.
    fixed = 1 if diagonal else 2
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

    if regular:
        # The translation-image identities are proved in the dual certificate.
        for x, b, c in itertools.product(range(n), repeat=3):
            add([-col(x, b), -p(x, b, c), p(c, x, b)])
            add([-row(x, b), -p(b, x, c), p(x, c, b)])

    if idempotent_case is not None:
        # These four disjoint cases exhaust the distinct-input search.
        add([p(0, 0, 0) if idempotent_case & 1 else -p(0, 0, 0)])
        add([p(1, 1, 1) if idempotent_case & 2 else -p(1, 1, 1)])

    cache = {}

    def evaluate(tree):
        if isinstance(tree, int):
            return [truth if z == tree else -truth for z in range(n)]
        if tree in cache:
            return cache[tree]
        left, right = map(evaluate, tree)
        values = [pool.id(("term", tree, z)) for z in range(n)]
        exactly(values)
        for a, b, c in itertools.product(range(n), repeat=3):
            add([-left[a], -right[b], -p(a, b, c), values[c]])
            add([-left[a], -right[b], -values[c], p(a, b, c)])
        cache[tree] = values
        return values

    def substitute(tree, x, y):
        if isinstance(tree, str):
            return {"x": x, "y": y}[tree]
        return tuple(substitute(child, x, y) for child in tree)

    g = lambda x, y: substitute(term, x, y)
    y = 0 if diagonal else 1
    values = evaluate(g(g(y, 0), g(0, g(0, y))))
    add([-values[0]])
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
        return "sat", table
    finally:
        solver.delete()
