#!/usr/bin/env python3
"""Replay E872 identity-compression candidates against verified bad models.

No solver result is inferred from a timeout or an omitted candidate. A candidate
is refuted when it HOLDS in a model that FAILS the exact two-equation image
basis. Candidates of right depth other than three have explicit cyclic
countermodels (Equation872ImageShape.lean supplies the necessary-depth theorem).

The JSON input has a `countermodels` list of square multiplication tables. The
output accounts for every generated candidate, including those still unresolved.
"""
import argparse
from functools import lru_cache
import itertools
import json
from pathlib import Path

import numpy as np


def core(t):
    return (t, ((t, t), t))


def unit(t):
    return ("U", t)


def cross(t, parameter):
    return ("T", t, parameter)


BASE = (1, (core(0), (1, 0)))


def size(t):
    if isinstance(t, int):
        return 0
    if t[0] == "U":
        return 4 + 5 * size(t[1])
    if t[0] == "T":
        return 6 + 5 * size(t[1])
    return 1 + size(t[0]) + size(t[1])


def right_depth(t):
    if isinstance(t, int):
        return 0
    if t[0] in ("U", "T"):
        return 3 + right_depth(t[1])
    return 1 + right_depth(t[1])


def replacements(t, mixed):
    yield unit(t)
    if mixed:
        for parameter in range(3):
            yield cross(t, parameter)
    if isinstance(t, int):
        return
    if t[0] == "U":
        for u in replacements(t[1], mixed):
            yield unit(u)
    elif t[0] == "T":
        for u in replacements(t[1], mixed):
            yield cross(u, t[2])
    else:
        for u in replacements(t[0], mixed):
            yield (u, t[1])
        for u in replacements(t[1], mixed):
            yield (t[0], u)


def candidates(rounds, mixed, outer, limit=None):
    seen = {BASE}
    layer = seen.copy()
    for _ in range(rounds):
        new = set()
        for t in layer:
            changes = replacements(t, mixed) if outer else (
                (1, u) for u in replacements(t[1], mixed))
            for u in changes:
                if (limit is None or size(u) <= limit) and u not in seen:
                    new.add(u)
        seen.update(new)
        layer = new
    return sorted(seen, key=lambda t: (size(t), str(t)))


class Model:
    def __init__(self, table):
        n = len(table)
        if not n or any(len(row) != n or any(
                not isinstance(x, int) or not 0 <= x < n for x in row) for row in table):
            raise ValueError("Expected a nonempty square multiplication table")
        self.table = table
        self.matrix = np.asarray(table)
        self.variables = np.asarray(list(itertools.product(range(n), repeat=3))).T
        # An entry is a vector of n³ assignments. Bound cached cells as well
        # as entries, so a larger witness does not retain gigabytes of arrays.
        cache_entries = max(32, min(20000, 2_000_000 // n**3))
        self.eval = lru_cache(maxsize=cache_entries)(self._eval)

    def _eval(self, t):
        if isinstance(t, int):
            return self.variables[t]
        if t[0] == "U":
            a = self.eval(t[1])
            return self.matrix[a, self.matrix[a, self.matrix[self.matrix[a, a], a]]]
        if t[0] == "T":
            a, b = self.eval(t[1]), self.variables[t[2]]
            c = self.matrix[a, self.matrix[self.matrix[a, a], a]]
            return self.matrix[b, self.matrix[c, self.matrix[b, a]]]
        return self.matrix[self.eval(t[0]), self.eval(t[1])]

    def holds(self, t):
        return bool(np.all(self.eval(t) == self.variables[0]))

    def is_image(self):
        # Exact on finite carriers, by Eq872Image.characterizes_fin.
        return self.holds(unit(0)) and self.holds(BASE)


def load_countermodels(tables):
    models = []
    seen = set()
    for table in tables:
        key = tuple(map(tuple, table))
        if key in seen:
            continue
        seen.add(key)
        model = Model(table)
        if model.is_image():
            raise ValueError("A supplied countermodel satisfies the image basis")
        models.append(model)
    return models


def refuting_model(t, models):
    # Deliberately positive: HOLDING in a bad model refutes characterization.
    return next((i for i, model in enumerate(models) if model.holds(t)), None)


def replay(pool):
    models = load_countermodels(pool)
    reports = []
    settings = [("unary3", 3, False, False, None),
                ("mixed2", 2, True, False, 65),
                ("outer2", 2, True, True, 65),
                ("outer3", 3, True, True, 120)]
    for name, rounds, mixed, outer, limit in settings:
        terms = candidates(rounds, mixed, outer, limit)
        refutations, unresolved = [], []
        for i, term in enumerate(terms):
            depth = right_depth(term)
            if depth != 3:
                # The generators preserve rightmost variable 0 and depth 0 mod 3.
                assert depth > 3 and depth % 3 == 0
                refutations.append({"candidate": i, "cyclic_order": depth})
            elif (witness := refuting_model(term, models)) is not None:
                refutations.append({"candidate": i, "countermodel": witness})
            else:
                unresolved.append(i)
        assert len(refutations) + len(unresolved) == len(terms)
        reports.append({"name": name, "candidates": len(terms),
                        "refuted": len(refutations), "unresolved": unresolved,
                        "refutations": refutations})
        print(f"{name}: {len(terms)} candidates; {len(refutations)} refuted; "
              f"{len(unresolved)} unresolved", flush=True)
    return {"countermodels": [m.table for m in models], "campaigns": reports}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = replay(json.loads(args.record.read_text())["countermodels"])
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
