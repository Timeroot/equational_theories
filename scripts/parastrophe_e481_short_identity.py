#!/usr/bin/env python3
"""Bounded search for single identities defining E481's finite left image.

This is research computation, not a Lean proof or a decision of SingleEquation.
Every sampled operation has a right identity e and satisfies x*(y*x)=e*y.
The exact finite image theorem is Eq481Image.characterizes_fin.

If a single defining identity has two composite sides, the constant two-point
magma satisfies it. If it is x=t and t's leftmost variable is x, the left
projection satisfies it. Neither magma has left division. Otherwise assign x
an arbitrary element and every other variable e. Then t is a term in x,e with
leftmost leaf e which evaluates to x in every sample. We enumerate precisely
these possibilities, merging terms only when all sampled values AND the
leftmost-leaf tag agree. An exhausted size bound therefore excludes all
single identities of that size, regardless of their number of variables.
"""

import argparse
import itertools
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent


def cross_inverse_model(prime=5):
    """CrossInverseLoops.division, with its four coordinates in lexicographic order."""
    inv3 = pow(3, -1, prime)

    def correction(x, y):
        if x == 0 or y == 0:
            return 0
        if (x + y) % prime == 0:
            return x
        return (x - y) * inv3 % prime

    def loop(a, b):
        return ((a[0] + b[0]) % prime,
                (a[1] + b[1] + correction(a[0], b[0])) % prime)

    def inverse(a):
        return (-a[0] % prime, (-a[1] - a[0]) % prime)

    points = list(itertools.product(range(prime), repeat=4))
    index = {a: i for i, a in enumerate(points)}
    table = [[index[loop(a[:2], b[2:]) + loop(a[2:], inverse(b[:2]))]
              for b in points] for a in points]
    return {"name": f"CrossInverseLoops.division over F{prime}",
            "table": table, "unit": 0}


def samples():
    old = json.loads((ROOT / "data/parastrophes/e481_image_basis_20261103.json").read_text())
    result = [{"name": f"saved order-{r['order']} model", "table": r["division_table"],
               "unit": r["right_identity"]} for r in old["countermodels"]]
    for n in [5, 13, 17]:
        for b in range(n):
            if (b * b + 1) % n == 0:
                result.append({"name": f"x+{b}y modulo {n}", "unit": 0,
                               "table": [[(x + b * y) % n for y in range(n)]
                                         for x in range(n)]})
    result.append(cross_inverse_model())
    return result


def small_loop_model():
    """A symbolic Cartesian square of the Lean-checked seven-element CI loop.

    Keep this separate from samples() so historical search reports retain
    their original sample set. New searches can opt in with --small-loop.
    """
    record = json.loads((ROOT / "data/parastrophes/e481_small_loop_20261104.json").read_text())
    q, j = record["loop_table"], record["inverse"]
    n = len(j)
    table = [[n * q[x // n][y % n] + q[x % n][j[y // n]]
              for y in range(n * n)] for x in range(n * n)]
    return {"name": "Eq481SmallLoop.division", "table": table, "unit": 0}


def check_model(model):
    """Check both image-basis conditions via the equivalent right-unital cross law."""
    table, e = model["table"], model["unit"]
    n = len(table)
    if any(len(row) != n or sorted(row) != list(range(n)) for row in table):
        raise ValueError(f"Non-permutation row in {model['name']}")
    for x in range(n):
        if table[x][e] != x:
            raise ValueError(f"Not a right identity in {model['name']}")
        for y in range(n):
            if table[x][table[y][x]] != table[e][y]:
                raise ValueError(f"Cross identity fails in {model['name']}")
    # Reconstruct the original operation and check E481 after its squares
    # have all been checked equal to e. This avoids a cubic loop over z.
    inverse = [[row.index(y) for y in range(n)] for row in table]
    if any(inverse[x][x] != e for x in range(n)):
        raise ValueError("The reconstructed source has nonconstant squares")
    for x in range(n):
        for y in range(n):
            if inverse[y][inverse[x][inverse[y][e]]] != x:
                raise ValueError("The reconstructed source fails E481")


def evaluate(term, table, x, e):
    if term == "x":
        return x
    if term == "e":
        return e
    return table[evaluate(term[0], table, x, e)][evaluate(term[1], table, x, e)]


def search(models, max_size, max_states):
    values, units, offsets, orders, flat = ([] for _ in range(5))
    for model in models:
        table, e = model["table"], model["unit"]
        n = len(table)
        offsets.extend([len(flat)] * n)
        orders.extend([n] * n)
        flat.extend(v for row in table for v in row)
        values.extend(range(n))
        units.extend([e] * n)
    flat = np.asarray(flat, dtype=np.uint16)
    offsets = np.asarray(offsets, dtype=np.int64)
    orders = np.asarray(orders, dtype=np.int64)
    x = np.asarray(values, dtype=np.uint16).tobytes()
    e = np.asarray(units, dtype=np.uint16).tobytes()
    levels = [{(x, False): "x", (e, True): "e"}]
    seen = dict(levels[0])
    layers = []
    report = {"status": "bounded_exclusion", "max_complete_size": 0,
              "candidate": None, "layers": layers,
              "samples": [{"name": m["name"], "order": len(m["table"]), "unit": m["unit"]}
                          for m in models]}
    for size in range(1, max_size + 1):
        new = {}
        for left_size in range(size):
            for (left, head), left_term in levels[left_size].items():
                indices = offsets + orders * np.frombuffer(left, dtype=np.uint16)
                for (right, _), right_term in levels[size - 1 - left_size].items():
                    result = flat[indices + np.frombuffer(right, dtype=np.uint16)].tobytes()
                    key = (result, head)
                    if key in seen or key in new:
                        continue
                    term = (left_term, right_term)
                    if key == (x, True):
                        report.update(status="candidate_only", candidate=term)
                        return report
                    new[key] = term
                    if len(seen) + len(new) >= max_states:
                        report.update(status="state_limit", partial_size=size,
                                      partial_new_states=len(new))
                        return report
        seen.update(new)
        levels.append(new)
        layers.append({"operations": size, "new_states": len(new), "states": len(seen)})
        report["max_complete_size"] = size
        print(f"Completed size {size}: {len(seen)} tagged signatures", flush=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-size", type=int, default=10)
    parser.add_argument("--max-states", type=int, default=400_000)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--small-loop", action="store_true",
                        help="Also use the seven-element CI loop's 49-element division")
    args = parser.parse_args()
    if args.max_size < 0 or args.max_states < 2:
        parser.error("Invalid search bounds")
    models = samples()
    for model in models:
        check_model(model)
    rejected = ["e", ["e", [["e", [["e", ["e", "x"]], "x"]], "x"]]]
    model = models[-1]
    got = evaluate(rejected, model["table"], 5, 0)
    if got != 57:
        raise ValueError(f"Unexpected independent check of the saved counterexample: {got}")
    if args.small_loop:
        extra = small_loop_model()
        check_model(extra)
        record = json.loads((ROOT / "data/parastrophes/e481_small_loop_20261104.json").read_text())
        if evaluate(record["candidate"], extra["table"], 1, 0) != 0:
            raise ValueError("The saved eleven-operation counterexample did not replay")
        models.append(extra)
    report = search(models, args.max_size, args.max_states)
    report.update(equation=481, scope="fin", side="left", proof_status="research_computation",
                  rejected_seven_operation_term={"term": rejected, "prime": 5,
                    "input": [0, 0, 1, 0], "output": [0, 2, 1, 2]})
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(report["status"], report["max_complete_size"], flush=True)


if __name__ == "__main__":
    main()
