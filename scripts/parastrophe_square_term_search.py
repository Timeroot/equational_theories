#!/usr/bin/env python3
"""Search for source squares expressed by unary terms in left division.

This is bounded research, not a Lean proof. Include the saved central-extension
counterexamples as well as repository tables: omitting those supplements can
rediscover previously refuted terms. A negative result excludes terms only
through the reported bound, without excluding longer recovery terms or a
single-equation characterization.
"""

import argparse
import json
from pathlib import Path

import numpy as np

from spectrum_generate import equal_coefficients, load_equations, satisfies


ROOT = Path(__file__).resolve().parents[1]


def samples(number, equation):
    tables, sources = [], []
    # Include the nonlinear search witnesses as well as extracted repository
    # tables. In particular finite_images_20261027 contains counterexamples
    # absent from the later repository-only inventory.
    for path in sorted((ROOT / "data/parastrophes").glob("*.json")):
        data = json.loads(path.read_text())
        indexed = data.get("sources", {}) if isinstance(data, dict) else {}
        source = indexed.get(str(number), {}) if isinstance(indexed, dict) else {}
        if isinstance(source, dict) and source.get("tables"):
            tables.extend(source["tables"])
            sources.append(str(path.relative_to(ROOT)))
    if not tables:
        raise ValueError(f"No saved source models for E{number}")
    for path in sorted((ROOT / "data/parastrophes").glob("image_cocycle_counterexamples_*.json")):
        records = [r for r in json.loads(path.read_text())["records"] if r["source"] == number]
        if records:
            sources.append(str(path.relative_to(ROOT)))
        for r in records:
            base, p, a, b, phi = (r[k] for k in ("base", "p", "a", "b", "phi"))
            n = len(base) * p
            tables.append([
                [p * base[x // p][y // p]
                 + (a * (x % p) + b * (y % p) + phi[x // p][y // p]) % p
                 for y in range(n)] for x in range(n)
            ])
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31):
        for a in range(p):
            for b in range(1, p):
                if equal_coefficients(*equation, a, b, p):
                    tables.append([[(a * x + b * y) % p for y in range(p)] for x in range(p)])
    unique = {}
    for table in tables:
        unique.setdefault(tuple(tuple(row) for row in table), table)
    return list(unique.values()), sources


def search(number, max_size=12, max_states=200_000):
    equation = load_equations()[number - 1]
    tables, sources = samples(number, equation)
    offsets, orders, inputs, targets, multiplication, division = ([] for _ in range(6))
    for table in tables:
        n = len(table)
        if not 0 < n <= 65535 or any(sorted(row) != list(range(n)) for row in table):
            raise ValueError("Every source table must have bijective rows and order at most 65535")
        flat = [v for row in table for v in row]
        if not satisfies(*equation, flat, n):
            raise ValueError(f"An order-{n} sample fails E{number}")
        offsets.extend([len(multiplication)] * n)
        orders.extend([n] * n)
        inputs.extend(range(n))
        targets.extend(table[x][x] for x in range(n))
        multiplication.extend(flat)
        division.extend(row.index(y) for row in table for y in range(n))
    offsets = np.asarray(offsets, dtype=np.int64)
    orders = np.asarray(orders, dtype=np.int64)
    multiplication = np.asarray(multiplication, dtype=np.uint16)
    division = np.asarray(division, dtype=np.uint16)
    target = np.asarray(targets, dtype=np.uint16)
    initial = np.asarray(inputs, dtype=np.uint16).tobytes()
    seen = {initial: (0, 0)}
    layers = [[initial]]
    counts = []
    candidate = {"operations": 0, "term": 0} if initial == target.tobytes() else None
    excluded = -1 if candidate else 0
    for size in range(1, max_size + 1):
        if candidate:
            break
        layer = []
        complete = True
        for left_size in range(size):
            for key in layers[left_size]:
                index = offsets + orders * np.frombuffer(key, dtype=np.uint16)
                for other in layers[size - 1 - left_size]:
                    value = division[index + np.frombuffer(other, dtype=np.uint16)].tobytes()
                    if value in seen:
                        continue
                    seen[value] = ((seen[key][0], seen[other][0]), size)
                    layer.append(value)
                    if len(seen) >= max_states:
                        complete = False
                        break
                if not complete:
                    break
            if not complete:
                break
        layers.append(layer)
        counts.append({"operations": size, "new_states": len(layer), "complete": complete})
        # D(u,v)=target iff v=M(u,target). With every subterm through size k
        # represented, this lookup exhausts all terms through k+1, as well as
        # some larger ones. It remains valid after a partial next layer.
        for key, (left, left_size) in seen.items():
            needed = multiplication[offsets + orders * np.frombuffer(key, dtype=np.uint16) + target]
            entry = seen.get(needed.tobytes())
            if entry is not None:
                right, right_size = entry
                length = left_size + right_size + 1
                if candidate is None or length < candidate["operations"]:
                    candidate = {"operations": length, "term": (left, right)}
        if candidate is None:
            excluded = size + 1 if complete else size
        if not complete:
            break
    return {
        "equation": number, "side": "left", "target": "source_square",
        "status": "candidate_only" if candidate else "bounded_search_exhausted",
        "lean_proof": False, "excluded_through_operations": excluded,
        "candidate": candidate, "states": len(seen), "layers": counts,
        "sample_orders": [len(t) for t in tables], "sample_sources": sources,
        "max_subterm_size": max_size, "max_states": max_states,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("equation", type=int)
    parser.add_argument("--max-subterm-size", type=int, default=12)
    parser.add_argument("--max-states", type=int, default=200_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 1 <= args.equation <= 4694 or args.max_subterm_size < 1 or args.max_states < 2:
        parser.error("Invalid equation or search bounds")
    result = search(args.equation, args.max_subterm_size, args.max_states)
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
