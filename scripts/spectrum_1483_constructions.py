#!/usr/bin/env python3
"""Check the general E1483 constructions and their saved research record.

This checks positive tables and archive integrity. It does not certify the
exploratory UNSAT results, or prove the open identities tested on the examples.
"""

from __future__ import annotations

from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import random
import tarfile

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/spectrum/1483_general_constructions.json"


def lawful(table: list[list[int]], law: int = 1483) -> bool:
    n = len(table)
    assert n and all(len(row) == n for row in table)
    assert all(0 <= v < n for row in table for v in row)
    for x, y, z in product(range(n), repeat=3):
        right = z if law == 168 else table[z][y] if law == 1485 else table[y][z]
        if table[table[y][x]][table[x][right]] != x:
            return False
    return True


def triangle_table(bits: tuple[int, ...]) -> list[list[int]]:
    """Two labels, two elements per label; each bit chooses a triangle swap."""
    assert len(bits) == 8 and set(bits) <= {0, 1}
    vertices = list(product(range(2), repeat=4))
    index = {v: i for i, v in enumerate(vertices)}
    return [
        [index[(j, k, b ^ bits[4 * i + 2 * j + k],
                c ^ bits[4 * j + 2 * k + l])]
         for k, l, c, d in vertices]
        for i, j, a, b in vertices
    ]


def coefficient_components(table: list[list[int]]) -> list[list[tuple[str, int, int]]]:
    parent: dict[tuple[str, int, int], tuple[str, int, int]] = {}

    def root(key: tuple[str, int, int]) -> tuple[str, int, int]:
        parent.setdefault(key, key)
        if parent[key] != key:
            parent[key] = root(parent[key])
        return parent[key]

    def join(left: tuple[str, int, int], right: tuple[str, int, int]) -> None:
        parent[root(left)] = root(right)

    n = len(table)
    for x, y, z in product(range(n), repeat=3):
        u, v = table[y][x], table[x][table[y][z]]
        join(("B", u, v), ("A", y, x))
        join(("A", u, v), ("B", x, table[y][z]))
    groups: dict[tuple[str, int, int], list[tuple[str, int, int]]] = {}
    for kind in ("A", "B"):
        for x, y in product(range(n), repeat=2):
            key = (kind, x, y)
            groups.setdefault(root(key), []).append(key)
    return list(groups.values())


def extension_table(base: list[list[int]], permutations: list[list[int]]) -> list[list[int]]:
    components = coefficient_components(base)
    assert len(permutations) == len(components)
    q = len(permutations[0])
    a, b, colors = {}, {}, {}
    for color, (component, permutation) in enumerate(zip(components, permutations)):
        assert sorted(permutation) == list(range(q))
        inverse = [permutation.index(i) for i in range(q)]
        for kind, x, y in component:
            colors[kind, x, y] = color
            (a if kind == "A" else b)[x, y] = permutation if kind == "A" else inverse
    for x, y, z in product(range(len(base)), repeat=3):
        u, v = base[y][x], base[x][base[y][z]]
        assert colors["B", u, v] == colors["A", y, x]
        assert colors["A", u, v] == colors["B", x, base[y][z]]
    vertices = list(product(range(len(base)), range(q), range(q)))
    index = {v: i for i, v in enumerate(vertices)}
    return [[index[(base[x][y], b[x, y][v], a[x, y][w])]
             for y, w, t in vertices] for x, u, v in vertices]


def row_profile(table: list[list[int]]) -> list[list[int]]:
    return [list(item) for item in sorted(Counter(len(set(row)) for row in table).items())]


def check_archive(record: dict) -> None:
    archive = record["archive"]
    path = ROOT / archive["path"]
    assert hashlib.sha256(path.read_bytes()).hexdigest() == archive["sha256"]
    with tarfile.open(path, "r:gz") as bundle:
        actual = {}
        for member in bundle.getmembers():
            assert member.isfile(), member.name
            assert Path(member.name).name == member.name, member.name
            stream = bundle.extractfile(member)
            assert stream is not None
            actual[member.name] = hashlib.sha256(stream.read()).hexdigest()
    assert actual == archive["members"]


def main() -> None:
    record = json.loads(DATA.read_text())
    assert record["new_spectrum_orders"] == []
    check_archive(record)

    triangle = record["triangle_example"]
    table = triangle_table(tuple(triangle["swaps"]))
    assert table == triangle["table"]
    assert lawful(table, 168) and lawful(table)
    assert len({frozenset(row) for row in table}) == 6
    profiles = Counter()
    for bits in product(range(2), repeat=8):
        t = triangle_table(bits)
        assert lawful(t, 168)
        profiles[len({frozenset(row) for row in t})] += 1
    assert dict(profiles) == {4: 64, 6: 128, 8: 64}

    extension = record["extensions"]
    base = extension["base"]
    assert lawful(base) and not lawful(base, 1485)
    assert len(coefficient_components(base)) == extension["component_count"] == 27
    rng = random.Random(extension["random_seed"])
    examples = {example["seed"]: example for example in extension["examples"]}
    for trial in range(extension["trials"]):
        permutations = [list(rng.choice(((0, 1), (1, 0)))) for _ in range(27)]
        t = extension_table(base, permutations)
        assert lawful(t)
        assert row_profile(t) == [[2, 4], [4, 12], [8, 12], [16, 4]]
        if trial in examples:
            example = examples[trial]
            assert t == example["table"]
            assert permutations == example["permutations"]
            assert not lawful(t, 1485)
            x, y, z = example["E1485_failure"]
            assert t[t[y][x]][t[x][t[z][y]]] != x

    # These checks ensure accurate reporting, not validity of SAT refutations.
    searches = record["restricted_searches"]
    assert len(searches["central_fibers"]) == 13
    assert Counter(item["order"] for item in searches["central_fibers"]) == {12: 6, 13: 7}
    assert len(searches["graph_covers"]) == 5
    for item in searches["central_fibers"] + searches["graph_covers"]:
        assert item["status"] == "unsat" and item["table"] is None
        assert item["trust"] and item["budget"] == 90
    for item in searches["projective_correlations"]:
        p = item["prime"]
        expected = (p**3 - 1) * (p**3 - p) * (p**3 - p**2) // (p - 1)
        assert item["matrices"] == expected
        assert item["counts"] == {"contradiction": expected}

    print("Verified archive integrity, all 256 triangle choices, and 100 E1483 extensions.")
    print("No new spectrum orders claimed. Restricted UNSAT reports are not Lean proofs.")


if __name__ == "__main__":
    main()
