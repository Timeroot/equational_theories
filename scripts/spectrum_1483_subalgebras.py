#!/usr/bin/env python3
"""Check E1483 cover subalgebras and symbolic identities.

The subalgebra classification uses the rectangular-fiber theorem proved in
PermutationSubalgebra.lean. Permutation words are compared in the free group,
so the symbolic checks apply to arbitrary permutations, not just the samples.
No exploratory UNSAT result is a Lean proof. The source archive contains the
slower independent exhaustive subalgebra/congruence enumeration.
"""
from __future__ import annotations

from collections import Counter, deque
from itertools import product
import hashlib
import tarfile
import json
from math import isqrt
from pathlib import Path
import random
import re

from spectrum_1483_constructions import coefficient_components, extension_table

ROOT = Path(__file__).resolve().parents[1]
BASE_DATA = ROOT / "data/spectrum/1483_general_constructions.json"
RECORD = ROOT / "data/spectrum/1483_subalgebra_research_20260930.json"


def inverse(p):
    return [p.index(x) for x in range(len(p))]


def compose(p, q):
    return [p[x] for x in q]


def base_subalgebras(base):
    n = len(base)
    result = []
    for mask in range(1, 1 << n):
        s = [x for x in range(n) if mask >> x & 1]
        if all(base[x][y] in s for x, y in product(s, repeat=2)):
            result.append(s)
    assert sorted(result) == [[0, 1, 2, 3, 4, 5, 6, 7], [0, 7], [3], [5], [6]]
    return result


def transport_subalgebras(base, permutations):
    """All subalgebras, using the coordinate transport graph and its orbits."""
    colors = {pos: i for i, c in enumerate(coefficient_components(base)) for pos in c}
    q = len(permutations[0])
    ident = list(range(q))
    all_subs = [frozenset()]
    for subset in base_subalgebras(base):
        nodes = list(product(("L", "R"), subset))
        edges = {v: [] for v in nodes}
        for x, y in product(subset, repeat=2):
            for src, dst, perm in [
                (("R", x), ("L", base[x][y]), inverse(permutations[colors["B", x, y]])),
                (("L", y), ("R", base[x][y]), permutations[colors["A", x, y]]),
            ]:
                edges[src].append((dst, perm))
                edges[dst].append((src, inverse(perm)))
        transport = {nodes[0]: ident}
        todo = deque([nodes[0]])
        while todo:
            src = todo.popleft()
            for dst, perm in edges[src]:
                if dst not in transport:
                    transport[dst] = compose(perm, transport[src])
                    todo.append(dst)
        assert len(transport) == len(nodes), "Constant-row bases give a connected graph."
        parent = list(range(q))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for src in nodes:
            for dst, perm in edges[src]:
                loop = compose(inverse(transport[dst]), compose(perm, transport[src]))
                for x, y in enumerate(loop):
                    parent[find(x)] = find(y)
        orbits = {}
        for x in range(q):
            orbits.setdefault(find(x), set()).add(x)
        orbits = list(orbits.values())
        for mask in range(1, 1 << len(orbits)):
            root_set = set().union(*(s for i, s in enumerate(orbits) if mask >> i & 1))
            fibers = {node: {transport[node][x] for x in root_set} for node in nodes}
            all_subs.append(frozenset(
                x * q * q + u * q + v for x in subset
                for u in fibers["L", x] for v in fibers["R", x]
            ))
    assert len(all_subs) == len(set(all_subs))
    return all_subs


def symbolic_identities(base):
    colors = {pos: i + 1 for i, c in enumerate(coefficient_components(base)) for pos in c}

    def transform(c, coordinate):
        variable, word = coordinate
        stack = []
        for x in (c,) + word:
            if stack and stack[-1] == -x:
                stack.pop()
            else:
                stack.append(x)
        return variable, tuple(stack)

    def op(x, y):
        a, b = x[0], y[0]
        return (base[a][b], transform(-colors["B", a, b], x[2]),
                transform(colors["A", a, b], y[1]))

    def projector(a, b, t):
        return op(a, op(t, b))

    def diagonal(x):
        return op(x, x)

    identities = [
        ("E1483", 3, lambda x, y, z: (op(op(y, x), op(x, op(y, z))), x)),
        ("projector_idempotence", 3, lambda a, b, t:
            (projector(a, b, projector(a, b, t)), projector(a, b, t))),
        ("projector_fixed_preservation", 4, lambda a, b, c, t:
            (projector(a, b, projector(a, c, projector(a, b, t))),
             projector(a, c, projector(a, b, t)))),
        ("diagonal_cubic", 1, lambda x: (diagonal(diagonal(diagonal(x))), diagonal(x))),
    ]
    result = []
    for name, variables, equation in identities:
        count = 0
        for bases in product(range(len(base)), repeat=variables):
            values = [(v, ((i, 0), ()), ((i, 1), ())) for i, v in enumerate(bases)]
            left, right = equation(*values)
            assert left == right, (name, bases, left, right)
            count += 1
        result.append({"identity": name, "base_assignments": count,
                       "status": "symbolic permutation-word identity"})
    return result


def main():
    original = json.loads(BASE_DATA.read_text())
    record = json.loads(RECORD.read_text())
    for relative, expected in record["source_hashes"].items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == expected, relative
    archive = record["archive"]
    archive_path = ROOT / archive["path"]
    assert hashlib.sha256(archive_path.read_bytes()).hexdigest() == archive["sha256"]
    with tarfile.open(archive_path, "r:gz") as bundle:
        members = {}
        for member in bundle.getmembers():
            assert member.isfile() and Path(member.name).name == member.name
            stream = bundle.extractfile(member)
            assert stream is not None
            members[member.name] = hashlib.sha256(stream.read()).hexdigest()
        assert members == archive["members"]
    base = original["extensions"]["base"]
    lean = (ROOT / "equational_theories/Spectrum/Equation1483/CubicBaseSubalgebras.lean").read_text()
    packed = re.search(r"private def rows : Fin 8 → Nat := !\[([^\]]+)\]", lean)
    assert packed is not None
    rows = [int(x.strip(), 0) for x in packed.group(1).split(",")]
    assert [[(row >> (3 * y)) % 8 for y in range(8)] for row in rows] == base
    assert symbolic_identities(base) == record["symbolic_checks"]
    rng = random.Random(record["random_seed"])
    cases = [(f"saved32_{i}", e["permutations"]) for i, e in enumerate(original["extensions"]["examples"])]
    for q, trials in record["random_trials"]:
        for i in range(trials):
            cases.append((f"random{8*q*q}_{i}", [rng.sample(range(q), q) for _ in range(27)]))
    assert len(cases) == len(record["closure_searches"])
    total = 0
    for (name, perms), saved in zip(cases, record["closure_searches"]):
        assert name == saved["name"]
        table = extension_table(base, perms)
        subs = transport_subalgebras(base, perms)
        profile = {str(n): count for n, count in sorted(Counter(map(len, subs)).items())}
        assert profile == saved["subalgebras"], (name, profile, saved["subalgebras"])
        assert saved["subalgebras_complete"] and saved["congruences_complete"]
        assert len(table) == saved["order"]
        for subset in subs:
            assert all(table[x][y] in subset for x, y in product(subset, repeat=2))
            n = len(subset)
            assert isqrt(n)**2 == n or (n % 2 == 0 and 2 * isqrt(n // 2)**2 == n)
        total += len(subs)
    table = original["extensions"]["examples"][0]["table"]
    witness = record["coordinate_associativity_counterexample"]
    a, b, x, y, z = (witness[k] for k in ("a", "b", "x", "y", "z"))
    coordinate = lambda u, v: table[table[a][u]][table[v][b]]
    assert table[a][witness["edge_witness"]] == b
    assert coordinate(coordinate(x, y), z) == witness["left"]
    assert coordinate(x, coordinate(y, z)) == witness["right"]
    assert witness["left"] != witness["right"]
    print(f"Verified {len(cases)} covers and all {total} subalgebras by coordinate transport.")
    print("Verified 512 + 512 + 4096 + 8 symbolic base assignments for arbitrary permutations.")
    print("Exploratory quotient counts and solver reports remain separate from Lean proofs.")


if __name__ == "__main__":
    main()
