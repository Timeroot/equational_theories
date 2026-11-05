#!/usr/bin/env python3
"""Replay the E1516 candidate counterexample and its genuine quotient image.

The Lean proof is symbolic and works for arbitrary exponent-two fibres.
This independent check expands only its 38-element member. No solver is used.
The counterexample is not an E1516 model or an actual division image.
"""

import itertools
import json
from pathlib import Path

from spectrum_generate import load_equations, satisfies


def main():
    root = Path(__file__).resolve().parents[1]
    data = json.loads(
        (root / "data/parastrophes/e1516_common_counterexample_20261104.json").read_text()
    )
    spec = data["counterexample"]
    assert (spec["base_modulus"], spec["fibre_modulus"], spec["order"]) == (19, 2, 38)
    assert spec["base_coefficients"] == [17, 3, 1]
    assert spec["xor_differences"] == [13]
    assert spec["right_projection_differences"] == [4, 8, 11]
    assert spec["otherwise"] == 0

    def product(x, y):
        i, u = divmod(x, 2)
        j, v = divmod(y, 2)
        d = (j - i) % 19
        w = u ^ v if d in spec["xor_differences"] else (
            v if d in spec["right_projection_differences"] else spec["otherwise"]
        )
        return 2 * ((17 * i + 3 * j + 1) % 19) + w

    table = [[product(x, y) for y in range(38)] for x in range(38)]
    cross = [[table[y][table[y][table[x][y]]] for y in range(38)] for x in range(38)]
    turn = [table[x][table[x][table[x][x]]] for x in range(38)]
    assert turn == [2 * ((x // 2 + 13) % 19) for x in range(38)]
    assert all(cross[x][y] == turn[x] for x, y in itertools.product(range(38), repeat=2))
    assert all(
        table[cross[x][y]][table[x][cross[x][z]]] == x
        for x, y, z in itertools.product(range(38), repeat=3)
    )
    assert table[0][0] == table[0][1]  # Not a left quasigroup, hence not an image.
    assert len(set(turn)) == 19

    source = data["sources"]["1516"]["tables"][0]
    assert source == [[(7 * x + 13 * y + 6) % 19 for y in range(19)] for x in range(19)]
    assert satisfies(*load_equations()[1515], sum(source, []), 19)
    seed = [[(-2 * x + 3 * y + 1) % 19 for y in range(19)] for x in range(19)]
    assert all(
        source[x][seed[x][y]] == y and seed[x][source[x][y]] == y
        for x, y in itertools.product(range(19), repeat=2)
    )
    assert all(seed[x][x] != x for x in range(19))
    assert all(table[x][y] // 2 == seed[x // 2][y // 2]
               for x, y in itertools.product(range(38), repeat=2))
    print("PASS: Common + Short at order 38, row collision, and genuine idempotent-free order-19 image")


if __name__ == "__main__":
    main()
