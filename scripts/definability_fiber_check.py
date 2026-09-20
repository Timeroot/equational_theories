#!/usr/bin/env python3
"""Check the saved fiber-family terms by exact integer linear arithmetic.

Each value has a base in Z/3 and a vector of coefficients of u, v, e.
Checking all nine base assignments proves the identities for every additive
commutative group. The standalone Lean certificate independently checks them.
This family result does not add a fact to the definability board.
"""

import itertools
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def operation(kind, x, y):
    a, u = x
    b, v = y
    d = (b - a) % 3
    p, q, r = {
        "source": [(0, 0, 0), (1, -1, 1), (-1, 1, 0)],
        "target": [(0, 0, 0), (-1, -1, 1), (0, -1, 1)],
        "middle": [(0, 0, 0), (1, -1, 2), (-1, 1, 1)],
    }[kind][d]
    return (1 - a - b) % 3, tuple(
        p * u[i] + q * v[i] + (r if i == 2 else 0) for i in range(3)
    )


def evaluate(term, kind, x, y):
    if term == "x":
        return x
    if term == "y":
        return y
    assert isinstance(term, list) and len(term) == 2
    return operation(kind, evaluate(term[0], kind, x, y), evaluate(term[1], kind, x, y))


def lean_term(term, kind):
    if isinstance(term, str):
        assert term in ("x", "y")
        return term
    return f"(({kind} e).op {lean_term(term[0], kind)} {lean_term(term[1], kind)})"


def leaves(term):
    return 1 if isinstance(term, str) else sum(map(leaves, term))


def main():
    data = json.loads((ROOT / "data/definability_fiber_recovery.json").read_text())
    assert (data["source"], data["target"]) == (3342, 4405)
    for a, b in itertools.product(range(3), repeat=2):
        x, y = (a, (1, 0, 0)), (b, (0, 1, 0))
        s = lambda u, v: operation("source", u, v)
        t = lambda u, v: operation("target", u, v)
        assert s(x, y) == s(y, s(x, s(x, x)))
        assert t(x, t(x, y)) == t(t(y, x), x)
        assert evaluate(data["forward"], "source", x, y) == t(x, y)
        assert evaluate(data["backward"], "target", x, y) == s(x, y)
    lean = (ROOT / "scripts/check_definability_fiber_recovery.lean").read_text()
    for name, kind in [("forward", "source"), ("backward", "target")]:
        body = re.search(rf"def {name} .*?:=\n(.*?)(?=\n\n)", lean, re.S)[1]
        assert body.split() == lean_term(data[name], kind).split()
    middle_data = json.loads(
        (ROOT / "data/definability_fiber_3545_recovery.json").read_text()
    )
    assert (middle_data["source"], middle_data["target"]) == (3342, 3545)
    for a, b in itertools.product(range(3), repeat=2):
        x, y = (a, (1, 0, 0)), (b, (0, 1, 0))
        s = lambda u, v: operation("source", u, v)
        m = lambda u, v: operation("middle", u, v)
        assert m(x, y) == m(y, m(m(x, x), x))
        assert evaluate(middle_data["forward"], "source", x, y) == m(x, y)
        assert evaluate(middle_data["backward"], "middle", x, y) == s(x, y)
    for name, kind in [("forward", "source"), ("backward", "middle")]:
        body = re.search(rf"def {name}3545 .*?:=\n(.*?)(?=\n\n)", lean, re.S)[1]
        assert body.split() == lean_term(middle_data[name], kind).split()
    print(
        "Verified E3545 and mutual terms on all 9 base pairs; "
        f"{leaves(middle_data['forward'])} forward / {leaves(middle_data['backward'])} backward leaves."
    )
    models = json.loads((ROOT / "data/definability_residual_models.json").read_text())
    table = next(m["table"] for m in models["square_families"] if m["source"] == 3342)

    def finite_value(term, x, y):
        if term == "x":
            return x
        if term == "y":
            return y
        return table[finite_value(term[0], x, y)][finite_value(term[1], x, y)]

    n = len(table)
    candidate = [
        [finite_value(data["forward"], x, y) for y in range(n)] for x in range(n)
    ]
    failures = sum(
        candidate[x][candidate[x][y]] != candidate[candidate[y][x]][x]
        for x, y in itertools.product(range(n), repeat=2)
    )
    assert (
        failures == 51
    ), "the family term must not be reported as a universal solution"
    print(
        "Verified source E3342, target E4405, and mutual terms on all 9 base pairs; "
        f"{leaves(data['forward'])} forward / {leaves(data['backward'])} backward leaves."
    )
    print(f"The forward term fails E4405 on {failures} pairs in the saved E3342 model.")


if __name__ == "__main__":
    main()
