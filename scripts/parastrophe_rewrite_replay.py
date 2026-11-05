#!/usr/bin/env python3
"""Audit an E872 rewrite campaign against saved, independently checked models.

The input records equations used as rewrite rules, finite bad tables, and
optional scalar affine bad tables. This script generates both directions of
those rewrites, accounts for every eligible candidate, and makes no assertion
that a surviving candidate characterizes the image. There are no solver calls.
"""
import argparse
from functools import lru_cache
import itertools
import json
from pathlib import Path

import numpy as np

from parastrophe_e872_compression import BASE, core, load_countermodels


def freeze(t):
    if isinstance(t, str):
        return "xyz".index(t)
    return t if isinstance(t, int) else tuple(map(freeze, t))


@lru_cache(None)
def size(t):
    return 0 if isinstance(t, int) else 1 + size(t[0]) + size(t[1])


def right_depth(t):
    return 0 if isinstance(t, int) else 1 + right_depth(t[1])


def endpoint(t, side):
    while not isinstance(t, int):
        t = t[side]
    return t


@lru_cache(None)
def variables(t):
    return frozenset([t]) if isinstance(t, int) else variables(t[0]) | variables(t[1])


def substitute(t, values):
    return values[t] if isinstance(t, int) else tuple(substitute(u, values) for u in t)


def match(pattern, term, values):
    if isinstance(pattern, int):
        if pattern in values:
            return values[pattern] == term
        values[pattern] = term
        return True
    return (isinstance(term, tuple) and match(pattern[0], term[0], values)
            and match(pattern[1], term[1], values))


def named(t):
    return "xyz"[t] if isinstance(t, int) else tuple(map(named, t))


def candidates(rules, rounds=3, limit=35):
    rules = [(freeze(a), freeze(b)) for _, a, b in rules]

    def replacements(t):
        for a, b in rules:
            for lhs, rhs in [(a, b), (b, a)]:
                values = {}
                if match(lhs, t, values):
                    missing = sorted(variables(rhs) - values.keys())
                    for extra in itertools.product(range(3), repeat=len(missing)):
                        u = substitute(rhs, values | dict(zip(missing, extra)))
                        if u != t:
                            yield u
        if isinstance(t, tuple):
            for u in replacements(t[0]):
                yield u, t[1]
            for u in replacements(t[1]):
                yield t[0], u

    seen = layer = {0}
    for _ in range(rounds):
        new = set()
        for t in layer:
            for u in replacements(t):
                if size(u) <= limit and u not in seen:
                    new.add(u)
        seen |= new
        layer = new
    eligible = [t for t in seen if t != 0 and right_depth(t) == 3
                and endpoint(t, 0) != 0 and endpoint(t, 1) == 0]
    return len(seen), sorted(eligible, key=lambda t: (size(t), str(named(t))))


def affine_holds(scalar_specs, gaussian_specs=()):
    """Evaluate four coefficients in Z/n or (Z/n)[i]/(i²+1).

    Scalar specifications accept an optional constant ``c`` (default zero).
    Gaussian specifications use [real, imaginary] pairs for a, b, c. Keeping
    both coordinates also handles nonsplit primes without multiplication tables.
    The returned predicate first validates that every model FAILS the image basis.
    """
    specs = [{"p": s["p"], "a": [s["a"], 0], "b": [s["b"], 0],
              "c": [s.get("c", 0), 0]} for s in scalar_specs] + list(gaussian_specs)
    n = len(specs)
    p = np.array([s["p"] for s in specs], dtype=np.int64)[:, None, None]
    if np.any(p < 2):
        raise ValueError("An affine modulus must be at least two")
    a, b, c = (np.array([s[k] for s in specs], dtype=np.int64).reshape(n, 1, 2) % p
               for k in ["a", "b", "c"])
    target = np.zeros((n, 4, 2), dtype=np.int64)
    target[:, 0, 0] = 1

    def mul(u, v):
        return np.stack((u[..., 0]*v[..., 0] - u[..., 1]*v[..., 1],
                         u[..., 0]*v[..., 1] + u[..., 1]*v[..., 0]), axis=-1) % p

    def coefficients(t):
        if isinstance(t, int):
            if t not in (0, 1, 2):
                raise ValueError("Expected a three-variable term")
            result = np.zeros((n, 4, 2), dtype=np.int64)
            result[:, t, 0] = 1
            return result
        result = mul(a, coefficients(t[0])) + mul(b, coefficients(t[1]))
        result[:, 3:4, :] += c
        return result % p

    def holds(t):
        return np.all(coefficients(t) == target, axis=(1, 2))

    if np.any(holds((0, core(0))) & holds(BASE)):
        raise ValueError("An affine countermodel satisfies the image basis")
    return holds


def replay(record):
    models = load_countermodels(record["countermodels"])
    specs = record.get("affine_countermodels", [])
    gaussian = record.get("gaussian_countermodels", [])
    holds = affine_holds(specs, gaussian)

    generated, terms = candidates(record["rewrite_rules"])
    counts = [0] * len(models)
    affine_counts = [0] * (len(specs) + len(gaussian))
    unresolved = []
    for i, t in enumerate(terms):
        for j, model in enumerate(models):
            if model.holds(t):
                counts[j] += 1
                break
        else:
            hits = np.flatnonzero(holds(t)) if affine_counts else []
            if len(hits):
                affine_counts[int(hits[0])] += 1
            else:
                unresolved.append({"index": i, "operations": size(t), "term": t})
    refuted = sum(counts) + sum(affine_counts)
    assert refuted + len(unresolved) == len(terms)
    return {"generated": generated, "eligible_candidates": len(terms), "refuted": refuted,
            "refuted_by_table": counts, "refuted_by_affine_model": affine_counts[:len(specs)],
            "refuted_by_gaussian_model": affine_counts[len(specs):],
            "unresolved_count": len(unresolved), "unresolved": unresolved}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = replay(json.loads(args.record.read_text()))
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{result['eligible_candidates']} candidates: {result['refuted']} refuted; "
          f"{result['unresolved_count']} unresolved.")


if __name__ == "__main__":
    main()
