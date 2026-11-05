#!/usr/bin/env python3
"""Search for multiplication terms in finite left-division models.

This is candidate discovery, not a proof of a uniform inverse. Every supplied
table is checked against its source law. Terms are identified by their values
on those tables, so failure also concerns only the specified search bounds.

At the root of a candidate D(u,v)=M(x,y), solve for v using the known inverse:
v=M(u,M(x,y)). Looking this vector up avoids a quadratic search over pairs of
subterms. Subterms through size k can thus produce candidates through size
2*k+1, without exhaustively searching all terms of that larger size.
"""

import argparse
import itertools
import json
from pathlib import Path

import numpy as np

from spectrum_generate import equal_coefficients, load_equations, satisfies


def search(equation, tables, affine, max_size, max_states):
    models = []
    for table in tables:
        n = len(table)
        if not n or any(sorted(row) != list(range(n)) for row in table):
            raise ValueError("Every source table must have bijective rows")
        flat = [v for row in table for v in row]
        if not satisfies(*equation, flat, n):
            raise ValueError("A supplied table fails the source law")
        models.append((table, list(itertools.product(range(n), repeat=2))))
    for spec in affine:
        n, a, b = (spec[k] for k in ("modulus", "a", "b"))
        if n < 2 or not equal_coefficients(*equation, a, b, n):
            raise ValueError("An affine family member fails the source law")
        pow(b, -1, n)  # Check that its rows are permutations.
        table = [[(a * i + b * j) % n for j in range(n)] for i in range(n)]
        # Every term remains homogeneous affine; these two inputs determine it.
        models.append((table, [(0, 1), (1, 0)]))
    if not models:
        raise ValueError("Supply at least one model")

    xs, ys, wanted, offsets, orders, multiplication, division = ([] for _ in range(7))
    for table, pairs in models:
        n = len(table)
        if n > 65535:
            raise ValueError("The search supports orders at most 65535")
        offset = len(multiplication)
        inverse = [[row.index(y) for y in range(n)] for row in table]
        multiplication.extend(v for row in table for v in row)
        division.extend(v for row in inverse for v in row)
        xs.extend(x for x, _ in pairs)
        ys.extend(y for _, y in pairs)
        wanted.extend(table[x][y] for x, y in pairs)
        offsets.extend([offset] * len(pairs))
        orders.extend([n] * len(pairs))

    source = np.asarray(multiplication, dtype=np.uint16)
    div = np.asarray(division, dtype=np.uint16)
    offsets = np.asarray(offsets, dtype=np.int64)
    orders = np.asarray(orders, dtype=np.int64)
    target = np.asarray(wanted, dtype=np.uint16)
    wanted_key = target.tobytes()
    seen, layers, counts = {}, [[]], []
    for t, values in enumerate((xs, ys)):
        key = np.asarray(values, dtype=np.uint16).tobytes()
        if key not in seen:
            seen[key] = (t, 0)
            layers[0].append(key)

    def result(candidate, complete=True):
        return {"candidate": candidate, "states": len(seen), "layers": counts,
                "complete_layers": complete, "models": len(models),
                "status": "candidate_only" if candidate else "bounded_search_exhausted"}

    if wanted_key in seen:
        return result({"term": seen[wanted_key][0], "operations": 0})

    def root_candidate():
        best = None
        for key, (left, left_size) in seen.items():
            values = np.frombuffer(key, dtype=np.uint16)
            required = source[offsets + orders * values + target].tobytes()
            if required in seen:
                right, right_size = seen[required]
                size = left_size + right_size + 1
                if best is None or size < best["operations"]:
                    best = {"term": (left, right), "operations": size}
        return best

    candidate = root_candidate()
    if candidate:
        return result(candidate)
    for size in range(1, max_size + 1):
        layer = []
        complete = True
        for left_size in range(size):
            right_size = size - 1 - left_size
            for left_key in layers[left_size]:
                left = np.frombuffer(left_key, dtype=np.uint16)
                index = offsets + orders * left
                for right_key in layers[right_size]:
                    right = np.frombuffer(right_key, dtype=np.uint16)
                    key = div[index + right].tobytes()
                    if key in seen:
                        continue
                    term = (seen[left_key][0], seen[right_key][0])
                    if key == wanted_key:
                        return result({"term": term, "operations": size}, False)
                    seen[key] = (term, size)
                    layer.append(key)
                    if len(seen) >= max_states:
                        complete = False
                        break
                if not complete:
                    break
            if not complete:
                break
        layers.append(layer)
        counts.append({"operations": size, "new_states": len(layer), "complete": complete})
        candidate = root_candidate()
        if candidate or not complete:
            out = result(candidate, complete)
            if not complete and not candidate:
                out["status"] = "state_limit"
            return out
    return result(None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("equation", type=int)
    parser.add_argument("--max-subterm-size", type=int, default=8)
    parser.add_argument("--max-states", type=int, default=1_000_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 1 <= args.equation <= 4694 or args.max_subterm_size < 0 or args.max_states < 2:
        parser.error("Invalid equation or search bounds")
    record = json.loads(args.record.read_text())["sources"][str(args.equation)]
    out = search(load_equations()[args.equation - 1], record["tables"],
                 record.get("affine_models", []), args.max_subterm_size, args.max_states)
    out["equation"] = args.equation
    text = json.dumps(out, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
