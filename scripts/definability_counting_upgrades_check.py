#!/usr/bin/env python3
"""Check possible strengthenings of the latest 234 counting certificates.

Projection witnesses exclude one-way term negatives. The finite automorphism
search is exploratory: a missing target group would require a separate Lean
certificate; finding matching groups only rules out these particular witnesses.
No board facts are written. --extended additionally requires pynauty and sympy.
"""

import argparse
import ast
from collections import Counter
import itertools
import json
import math
from pathlib import Path

import numpy as np

from definability_symmetry_counts_check import permutation_tables
from definability_translation_counts_check import translation_tables
from spectrum_generate import load_equations, variables

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/definability_counting_upgrades.json"
FAMILIES = ("affine", "matrix", "translation", "symmetry", "relation")


def candidates(families=FAMILIES):
    return [
        dict(family=family, **entry)
        for family in families
        for entry in json.loads(
            (ROOT / f"data/definability_{family}_counts.json").read_text()
        )["candidates"]
    ]


def endpoint(term, side):
    while not isinstance(term, str):
        term = term[side]
    return term


def check_previous_products(equations, entries):
    """Check common forward terms, without claiming a general definition."""
    from definability_linear_counts import linear_models

    for entry in entries:
        n = entry["modulus"]
        factors = linear_models(equations[entry["source"] - 1], n)
        assert [list(pair) for pair in factors] == entry["factors"]
        x, y = np.indices((n, n))
        tables = np.array([(a * x + b * y) % n for a, b in factors], dtype=np.uint8)
        index = np.arange(len(tables))[:, None, None]

        def evaluate(node):
            if isinstance(node, ast.Name):
                return {"x": x, "y": y}[node.id]
            assert isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult)
            return tables[index, evaluate(node.left), evaluate(node.right)]

        derived = evaluate(ast.parse(entry["witness"], mode="eval").body)
        assert len(model_indices(equations, tables, entry["source"])) == len(tables)
        assert len(model_indices(equations, derived, entry["target"])) == len(tables)


def open_pairs(snapshot, entries):
    board = snapshot["boards"]["structural/fin"]
    classes = {
        member: int(rep) for rep, group in board["classes"].items() for member in group
    }
    rows = {
        int(source): {target for group in profiles.values() for target in group}
        for source, profiles in board["open_rows"].items()
    }
    return sorted(
        {
            (e["source"], e["target"])
            for e in entries
            if classes[e["target"]] in rows.get(classes[e["source"]], set())
        }
    )


def model_indices(equations, tables, law):
    """Test every assignment, dropping failing tables after each batch."""
    n = tables.shape[1]
    lhs, rhs = equations[law - 1]
    names = sorted(variables(lhs) | variables(rhs))
    assignments = np.array(
        list(itertools.product(range(n), repeat=len(names))),
        dtype=np.uint8 if n <= 256 else np.uint16,
    ).T
    active = np.arange(len(tables))
    for start in range(0, assignments.shape[1], 16):
        if not len(active):
            break
        batch = assignments[:, start : start + 16]
        index = active[:, None]
        cache = {v: batch[i][None, :] for i, v in enumerate(names)}

        def evaluate(term):
            if term not in cache:
                cache[term] = tables[index, evaluate(term[0]), evaluate(term[1])]
            return cache[term]

        good = np.broadcast_to(
            evaluate(lhs) == evaluate(rhs), (len(active), batch.shape[1])
        )
        active = active[np.all(good, axis=1)]
    return active


def preserves(table, permutations):
    return all(
        np.array_equal(table[p[:, None], p[None, :]], p[table]) for p in permutations
    )


def graph_automorphisms(table):
    """Encode the multiplication graph with three synchronized carrier copies.

    Every graph automorphism restricts to a magma automorphism, and each magma
    automorphism has exactly one extension to the graph. Return generators on
    the first carrier copy. Matching edges synchronize the three copies; a
    center's three neighbors specify its left input, right input, and output.
    """
    import pynauty

    n = len(table)
    unary = None
    if np.all(table == table[:, :1]):
        unary = table[:, 0]
    elif np.all(table == table[:1, :]):
        unary = table[0]
    if unary is not None:
        # A one-variable operation has exactly the automorphisms of its
        # functional digraph. This also handles both projections without
        # introducing the quadratic number of argument-position vertices.
        graph = pynauty.Graph(
            n, directed=True,
            adjacency_dict={x: [int(unary[x])] for x in range(n)},
        )
        generators, _, _, _, _ = pynauty.autgrp(graph)
        result = np.array(generators, dtype=np.uint16).reshape(-1, n)
        assert preserves(table, result)
        return result
    adjacency = {i: [] for i in range(3 * n + n * n)}
    colors = [set(range(k * n, (k + 1) * n)) for k in range(3)]
    centers = {}

    def link(x, y):
        adjacency[x].append(y)
        adjacency[y].append(x)

    for x in range(n):
        link(x, n + x)
        link(x, 2 * n + x)
    for x, y in itertools.product(range(n), repeat=2):
        z = int(table[x, y])
        center = 3 * n + x * n + y
        link(center, x)
        link(center, n + y)
        link(center, 2 * n + z)
        # These equality patterns are preserved by every magma automorphism.
        # Giving them initial colors avoids rediscovering them during search.
        pattern = (x == y, x == z, y == z, int(table[y, x]) == z)
        centers.setdefault(pattern, set()).add(center)
    graph = pynauty.Graph(
        3 * n + n * n,
        adjacency_dict=adjacency,
        vertex_coloring=colors + list(centers.values()),
    )
    generators, _, _, _, _ = pynauty.autgrp(graph)
    generators = np.array([p[:n] for p in generators], dtype=np.uint16).reshape(-1, n)
    assert preserves(table, generators)
    return generators


def scan(equations, label, tables, pairs, *, graph=False):
    """Compare exact subgroups of the labeled symmetric group, not group orders."""
    n = tables.shape[1]
    ids = sorted({law for pair in pairs for law in pair})
    models = {law: model_indices(equations, tables, law) for law in ids}
    active = np.unique(np.concatenate(list(models.values())))
    signatures = {}
    if graph:
        groups = []

        def classify(index):
            index = int(index)
            if index in signatures:
                return signatures[index]
            table = tables[index]
            generators = graph_automorphisms(table)
            for group, (representative, existing) in enumerate(groups):
                if preserves(table, existing) and preserves(representative, generators):
                    break
            else:
                group = len(groups)
                groups.append((table, generators))
            signatures[index] = group
            return group

        # Classify every source model. For each target it is sufficient to find
        # one representative of every required source group; only a failure
        # requires exhausting the target family. Matching operations need not
        # be distinct, and the matching may depend on the source model.
        sources = sorted({source for source, _ in pairs})
        support = {
            source: {classify(index): int(index) for index in models[source]}
            for source in sources
        }
        target_support = {}
        for target in sorted({target for _, target in pairs}):
            needed = set().union(
                *(support[source] for source, t in pairs if t == target)
            )
            found = {}
            indices = sorted(
                models[target], key=lambda index: int(index) not in signatures
            )
            for index in indices:
                if not needed:
                    break
                group = classify(index)
                found[group] = int(index)
                needed.discard(group)
            target_support[target] = found
    else:
        selected = tables[active]
        packed = np.zeros((len(active), (math.factorial(n) + 7) // 8), dtype=np.uint8)
        for index, permutation in enumerate(itertools.permutations(range(n))):
            p = np.array(permutation, dtype=np.uint8)
            good = np.all(
                selected[:, p[:, None], p[None, :]] == p[selected], axis=(1, 2)
            )
            packed[:, index // 8] |= good.astype(np.uint8) << (index % 8)
        signatures = {int(index): row.tobytes() for index, row in zip(active, packed)}
        support = {
            law: {signatures[int(index)]: int(index) for index in indices}
            for law, indices in models.items()
        }
        target_support = support
    hits = []
    for source, target in pairs:
        missing = support[source].keys() - target_support[target].keys()
        if missing:
            index = support[source][next(iter(missing))]
            hits.append(
                dict(
                    source=source,
                    target=target,
                    table=tables[index].tolist(),
                    missing_groups=len(missing),
                )
            )
    result = dict(
        family=label,
        order=n,
        tables=len(tables),
        pairs=len(pairs),
        model_tables=len(active),
        exact_groups=len(set(signatures.values())),
        hits=hits,
    )
    if graph:
        result["examined_tables"] = len(signatures)
    print(
        f"{label}: {len(tables):,} operations, {len(pairs)} pairs, {len(hits)} candidates.",
        flush=True,
    )
    return result


def invariant_tables(generators, limit=150000):
    """Enumerate every operation commuting with the supplied permutations."""
    n = len(generators[0])
    seen, orbits, choices = set(), [], []
    for x, y in itertools.product(range(n), repeat=2):
        if (x, y) in seen:
            continue
        orbit = [(x, y)]
        seen.add((x, y))
        for u, v in orbit:
            for g in generators:
                pair = (g[u], g[v])
                if pair not in seen:
                    seen.add(pair)
                    orbit.append(pair)
        allowed = []
        for z in range(n):
            image, valid = {(x, y): z}, True
            for u, v in orbit:
                for g in generators:
                    pair, value = (g[u], g[v]), g[image[u, v]]
                    if pair in image and image[pair] != value:
                        valid = False
                        break
                    image[pair] = value
                if not valid:
                    break
            if valid:
                allowed.append([image[pair] for pair in orbit])
        orbits.append(orbit)
        choices.append(allowed)
    size = math.prod(map(len, choices))
    if size > limit:
        return None, size
    tables = np.empty((size, n, n), dtype=np.uint8)
    for index, parameters in enumerate(
        itertools.product(*[range(len(v)) for v in choices])
    ):
        for orbit, values, choice in zip(orbits, choices, parameters):
            for (u, v), value in zip(orbit, values[choice]):
                tables[index, u, v] = value
    return tables, size


def extended_groups():
    from sympy import primitive_root

    def basic(n, kind):
        cycle = [(i + 1) % n for i in range(n)]
        swap = list(range(n))
        swap[0], swap[1] = 1, 0
        if kind == "C":
            return [cycle]
        return [cycle, [(-i) % n for i in range(n)] if kind == "D" else swap]

    def product(a, b, left, right):
        return [
            [p[x] * b + y for x in range(a) for y in range(b)] for p in basic(a, left)
        ] + [
            [x * b + p[y] for x in range(a) for y in range(b)] for p in basic(b, right)
        ]

    for a, b in [(2, 4), (3, 3), (3, 4), (2, 5), (3, 5), (4, 4), (3, 6), (4, 5)]:
        yield f"S{a} x S{b}", product(a, b, "S", "S")
    for a, b in [(3, 3), (4, 3), (5, 3), (3, 4), (4, 4), (5, 4), (6, 3), (7, 3)]:
        for kind in ["C", "D"]:
            yield f"{kind}{a} x S{b}", product(a, b, kind, "S")
    for a in (3, 4, 5):
        generators = product(a, a, "C", "C")
        generators.append([y * a + x for x in range(a) for y in range(a)])
        yield f"C{a} x C{a} with swap", generators
    for p in (7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        primitive = int(primitive_root(p))
        for index in (1, 2, 3):
            if (p - 1) % index:
                continue
            multiplier = pow(primitive, index, p)
            yield f"affine {p} multiplier index {index}", [
                [(x + 1) % p for x in range(p)],
                [(multiplier * x) % p for x in range(p)],
            ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extended", action="store_true")
    parser.add_argument("--verify-board", action="store_true")
    args = parser.parse_args()
    saved = json.loads(DATA.read_text())
    snapshot = json.loads((ROOT / "docs/definability_open/snapshot.json").read_text())
    assert snapshot["fingerprint"] == saved["fingerprint"], "refresh the upgrade audit"
    equations, entries = load_equations(), candidates()
    projections = Counter()
    for entry in entries:
        lhs, rhs = equations[entry["target"] - 1]
        witnesses = [
            side for side in (0, 1) if endpoint(lhs, side) == endpoint(rhs, side)
        ]
        assert witnesses, entry
        projections[
            (
                "both"
                if len(witnesses) == 2
                else ("left" if witnesses[0] == 0 else "right")
            )
        ] += 1
    assert dict(projections) == saved["projection_witnesses"]
    print(
        f"All {len(entries)} targets have a projection term on every carrier.",
        flush=True,
    )
    check_previous_products(equations, saved["previous_product_terms"])
    pairs = open_pairs(snapshot, entries)
    small = [
        scan(
            equations,
            "all three-element operations",
            np.array(
                list(itertools.product(range(3), repeat=9)), dtype=np.uint8
            ).reshape(-1, 3, 3),
            pairs,
        )
    ]
    for permutation in [(0, 2, 3, 1), (0, 2, 3, 4, 1), (1, 0, 3, 2), (0, 1, 3, 2)]:
        selected = open_pairs(
            snapshot, [e for e in entries if e.get("permutation") == list(permutation)]
        )
        small.append(
            scan(
                equations,
                "permutation " + str(permutation),
                permutation_tables(permutation),
                selected,
            )
        )
    for n in (4, 5, 6, 7):
        selected = open_pairs(
            snapshot,
            [e for e in entries if e["family"] == "translation" and e["order"] == n],
        )
        small.append(
            scan(equations, f"cyclic translations {n}", translation_tables(n), selected)
        )
    assert small == saved["small_symmetry_checks"]
    if args.extended:
        results, skipped = [], []
        deferred = {entry["family"] for entry in saved["deferred_families"]}
        for label, generators in extended_groups():
            if label in deferred:
                continue
            tables, size = invariant_tables(generators)
            if tables is None:
                skipped.append(dict(family=label, tables=size))
                continue
            results.append(scan(equations, label, tables, pairs, graph=True))
        assert results == saved["extended_symmetry_checks"]
        assert skipped == saved["skipped_families"]
    if args.verify_board:
        import definable
        from definability_audit import source_fingerprint

        before = source_fingerprint()
        assert before == saved["fingerprint"]
        positive, negative = definable.build_relations()
        for label, batch in [
            ("latest", entries),
            ("earlier", candidates(("partial_linear", "table"))),
        ]:
            for key, expected in saved[label + "_board_counts"].items():
                relation, flavour = key.split("/")
                p, n = positive[relation, flavour], negative[relation, flavour]
                actual = Counter(
                    (
                        "positive"
                        if p[e["source"], e["target"]]
                        else "negative" if n[e["source"], e["target"]] else "open"
                    )
                    for e in batch
                )
                assert dict(actual) == expected, (label, key, actual, expected)
        assert source_fingerprint() == before
    print(
        "Saved upgrade checks reproduced. Matching groups do not prove structurality."
    )


if __name__ == "__main__":
    main()
