#!/usr/bin/env python3
"""Enumerate every Latin square of orders 2,4,5 and classify its E667 models.

This is research evidence, not a Lean declaration. The enumeration is independent
of the SAT searches. Default: compare against the saved deterministic record.
Use --write to regenerate that record.
"""
import argparse
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "data/spectrum/667_small_quotients.json"


def law(table):
    n = len(table)
    return all(
        table[y][table[x][table[table[x][x]][y]]] == x
        for x in range(n)
        for y in range(n)
    )


def enumerate_order(n):
    perms = list(itertools.permutations(range(n)))
    tables = []

    def extend(table):
        if len(table) == n:
            tables.append(table[:])
            return
        for p in perms:
            if all(p[j] != row[j] for row in table for j in range(n)):
                extend(table + [p])

    # Every Latin square has one and only one symbol relabelling whose first
    # row is (0,...,n-1). Enumerate those squares, then undo every relabelling.
    extend([tuple(range(n))])
    count = 0
    idemcounts = {}
    classes = {}

    def canonical(table):
        candidates = []
        for a in perms:
            flat = [None] * (n * n)
            for i in range(n):
                for j in range(n):
                    flat[a[i] * n + a[j]] = a[table[i][j]]
            candidates.append(tuple(flat))
        return min(candidates)

    for table in tables:
        for p in perms:
            q = [[p[z] for z in row] for row in table]
            if law(q):
                count += 1
                k = sum(q[i][i] == i for i in range(n))
                idemcounts[k] = idemcounts.get(k, 0) + 1
                key = canonical(q)
                classes[key] = [list(key[i * n : (i + 1) * n]) for i in range(n)]
    return {
        "order": n,
        "latin_squares": len(tables) * len(perms),
        "E667_tables": count,
        "table_idempotent_counts": {str(k): v for k, v in sorted(idemcounts.items())},
        "isomorphism_classes": [classes[k] for k in sorted(classes)],
    }


def coefficient_check():
    # Necessary sign consequence of the coefficient of x in a Latin3 fiber.
    for aii, bii, ait, bit, asj, bju in itertools.product([-1, 1], repeat=6):
        if bju * (ait + bit * asj * (aii + bii)) % 3 == 1:
            assert ait * bju == -aii * bii
    # The three cyclic-diagonal product identities have no sign solution.
    assert not any(
        a2 * b1 == -d and a2 * b3 == -1 and d * b1 * b3 == -1
        for a2, b1, b3, d in itertools.product([-1, 1], repeat=4)
    )


def generate():
    orders = [enumerate_order(n) for n in [2, 4, 5]]
    assert [row["latin_squares"] for row in orders] == [2, 576, 161280]
    assert all(
        any(table[i][i] == i for i in range(row["order"]))
        for row in orders[:2]
        for table in row["isomorphism_classes"]
    )
    free = [
        table
        for table in orders[2]["isomorphism_classes"]
        if all(table[i][i] != i for i in range(5))
    ]
    assert len(free) == 1
    q = [[(3 * i + 3 * j + 1) % 5 for j in range(5)] for i in range(5)]
    assert law(q)
    iso = next(
        a
        for a in itertools.permutations(range(5))
        if all(a[free[0][i][j]] == q[a[i]][a[j]] for i in range(5) for j in range(5))
    )
    coefficient_check()
    return {
        "status": "RESEARCH_ONLY",
        "method": "exhaustive Latin-square enumeration and direct original-law evaluation",
        "orders": orders,
        "order5_idempotent_free_affine_isomorphism": list(iso),
        "order5_idempotent_free_affine_formula": "q(i,j)=3*i+3*j+1 (mod 5)",
        "fiber3_obstruction": "docs/e667_construction_research.md",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    record = generate()
    if args.write:
        DEST.write_text(json.dumps(record, indent=2) + "\n")
    else:
        assert json.loads(DEST.read_text()) == record, "saved classification differs"
    print(
        "Checked all 161858 Latin squares at orders 2,4,5; small-quotient record verified."
    )


if __name__ == "__main__":
    main()
