#!/usr/bin/env python3
"""Check an unproved E1483 -> E1479 candidate on saved finite models.

Optionally emit the universal TPTP conjecture or seek a fresh countermodel.
Neither a finite pass nor a solver timeout settles a definability-table cell.
"""

import argparse
import json
from pathlib import Path

import numpy as np

from definability_twisted_check import satisfies
from spectrum_generate import load_equations


DATA = Path(__file__).resolve().parent.parent / "data"


def evaluate(term, operation, x, y):
    if isinstance(term, str):
        assert term in ("x", "y")
        return x if term == "x" else y
    return operation(
        evaluate(term[0], operation, x, y),
        evaluate(term[1], operation, x, y),
    )


def leaves(term):
    return 1 if isinstance(term, str) else sum(map(leaves, term))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tptp", type=Path, help="write the universal conjecture")
    parser.add_argument("--countermodel-order", type=int)
    parser.add_argument("--solver", choices=("z3", "cadical"), default="z3")
    parser.add_argument(
        "--regular",
        action="store_true",
        help="add the proved translation-image identities to the CaDiCaL encoding",
    )
    parser.add_argument(
        "--idempotent-case",
        type=int,
        choices=range(4),
        help="CaDiCaL distinct-input partition: bit 0 says x is idempotent, bit 1 says y is",
    )
    parser.add_argument("--seconds", type=int, default=90)
    parser.add_argument("--countermodel-output", type=Path)
    args = parser.parse_args()
    if args.regular and args.solver != "cadical":
        parser.error("--regular requires --solver cadical")
    if args.idempotent_case is not None and (
        args.solver != "cadical"
        or not args.countermodel_order
        or args.countermodel_order < 2
    ):
        parser.error(
            "--idempotent-case requires --solver cadical and an order at least 2"
        )
    data = json.loads((DATA / "definability_1483_term_candidate.json").read_text())
    term = data["term"]
    equations = load_equations()
    assert (data["source"], data["target"]) == (1483, 1479)
    models = [entry["table"] for entry in data["models"]]
    models.append(json.loads((DATA / data["additional_model"]).read_text())["table"])
    assert leaves(term) == 10
    for model in models:
        table = np.array(model, dtype=np.int32)
        assert satisfies(equations[1482], table)
        x, y = np.indices(table.shape)
        derived = evaluate(term, lambda a, b: table[a, b], x, y)
        assert satisfies(equations[1478], derived)
    print(
        f"Ten-leaf candidate passes {len(models)} saved models; universal status OPEN.",
        flush=True,
    )

    if args.tptp:
        multiply = lambda a, b: f"f({a},{b})"
        g = lambda a, b: evaluate(term, multiply, a, b)
        goal = g(g("Y", "X"), g("X", g("X", "Y")))
        args.tptp.write_text(
            "fof(source,axiom, ![X,Y,Z]: f(f(Y,X),f(X,f(Y,Z)))=X).\n"
            f"fof(goal,conjecture, ![X,Y]: {goal}=X).\n"
        )

    if args.countermodel_order is not None:
        if args.solver == "cadical":
            from definability_central_candidate_sat import countermodel

            witness_types = (True, False) if args.idempotent_case is None else (False,)
            for diagonal in witness_types:
                result, model = countermodel(
                    term,
                    args.countermodel_order,
                    args.seconds,
                    diagonal,
                    args.idempotent_case,
                    regular=args.regular,
                )
                kind = "equal" if diagonal else "distinct"
                if args.idempotent_case is not None:
                    kind += f"; idempotent case {args.idempotent_case}"
                print(f"Countermodel search ({kind} inputs): {result}", flush=True)
                if model is not None:
                    table = np.array(model)
                    assert satisfies(equations[1482], table)
                    xx, yy = np.indices(table.shape)
                    derived = evaluate(term, lambda a, b: table[a, b], xx, yy)
                    assert not satisfies(equations[1478], derived)
                    text = json.dumps({"source": 1483, "table": model}, indent=2)
                    if args.countermodel_output:
                        args.countermodel_output.write_text(text + "\n")
                    else:
                        print(text)
                    break
            return

        import z3

        n = args.countermodel_order
        assert n > 0 and args.seconds > 0
        carrier, values = z3.EnumSort("Carrier", [f"e{i}" for i in range(n)])
        operation = z3.Function("operation", carrier, carrier, carrier)
        solver = z3.Solver()
        solver.set(timeout=args.seconds * 1000)
        for x in values:
            for y in values:
                for z in values:
                    solver.add(
                        operation(operation(y, x), operation(x, operation(y, z))) == x
                    )
        # Free witnesses allow both equal and distinct counterexample inputs.
        x, y = z3.Consts("witness_x witness_y", carrier)
        g = lambda a, b: evaluate(term, operation, a, b)
        solver.add(g(g(y, x), g(x, g(x, y))) != x)
        result = solver.check()
        print(f"Countermodel search at order {n}: {result}", flush=True)
        if result == z3.sat:
            model = solver.model()
            positions = {str(value): i for i, value in enumerate(values)}
            table = np.array(
                [
                    [positions[str(model.eval(operation(a, b)))] for b in values]
                    for a in values
                ]
            )
            assert satisfies(equations[1482], table)
            xx, yy = np.indices(table.shape)
            derived = evaluate(term, lambda a, b: table[a, b], xx, yy)
            assert not satisfies(equations[1478], derived)
            text = json.dumps({"source": 1483, "table": table.tolist()}, indent=2)
            if args.countermodel_output:
                args.countermodel_output.write_text(text + "\n")
            else:
                print(text)


if __name__ == "__main__":
    main()
