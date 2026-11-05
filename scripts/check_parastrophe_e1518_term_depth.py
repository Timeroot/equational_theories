#!/usr/bin/env python3
"""Independently replay the finite E1518 term-depth obstructions.

The published Lean proofs check offsets and layer closure symbolically.
This small research replayer also checks the complete resulting tables.
"""

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/parastrophes"


def read(name):
    return json.loads((DATA / name).read_text())


def term_value(text, table):
    tokens = iter(re.findall(r"Lf 0|[()⋆]", text))

    def parse():
        token = next(tokens)
        if token == "Lf 0":
            return 0, 0
        assert token == "("
        left, dl = parse()
        assert next(tokens) == "⋆"
        right, dr = parse()
        assert next(tokens) == ")"
        return table[left][right], 1 + max(dl, dr)

    result = parse()
    assert next(tokens, None) is None
    return result


def check_lift(base, record):
    n = len(base)
    dimension = record.get("fibre_dimension", 1)
    p = record["modulus"]
    assert p == 3 and dimension in (1, 2)
    fibre = p**dimension
    encoded = [[int(c) for c in row] for row in record["offset_rows"]]
    assert len(encoded) == n and all(len(row) == n for row in encoded)
    assert all(0 <= c < fibre for row in encoded for c in row)
    digits = [[v // p**k % p for k in range(dimension)] for v in range(fibre)]

    def add(u, v):
        return sum((a + b) % p * p**k
                   for k, (a, b) in enumerate(zip(digits[u], digits[v])))

    for x in range(n):
        for y in range(n):
            assert add(add(encoded[y][x], encoded[x][base[y][x]]),
                       encoded[base[y][y]][base[x][base[y][x]]]) == 0
    size = n * fibre
    table = [[fibre * base[x // fibre][y // fibre] +
              add(y % fibre, encoded[x // fibre][y // fibre])
              for y in range(size)] for x in range(size)]
    assert all(table[table[y][y]][table[x][table[y][x]]] == x
               for x in range(size) for y in range(size))
    assert all(len(set(row)) == size for row in table)
    roots = [x for x in range(size) if table[x][x] == 0]
    assert roots == [record["root"]]
    values = {0}
    for depth, expected in enumerate(record["balls"]):
        assert sorted(values) == expected
        assert (roots[0] in values) == (depth >= record["minimum_depth"])
        values |= {table[x][y] for x in values for y in values}
    value, depth = term_value(record["attaining_term"], table)
    assert value == roots[0] and depth == record["minimum_depth"]
    print(f"Order {size}: minimum root-term depth {depth}; offsets, full law, "
          "layers and attaining term checked.")
    return table


def main():
    seed = read("e1518_square_cycles_20261103.json")["seed"]["table"]
    model45 = check_lift(seed, read("e1518_term_depth_20261104.json"))
    check_lift(model45, read("e1518_term_depth_six_20261104.json"))


if __name__ == "__main__":
    main()
