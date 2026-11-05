#!/usr/bin/env python3
"""Screen collision-preserving terms in four countable idempotent constructions.

The extension rules come from Generated/Greedy/Eq{124,670,1082,1288}Idempotent.
Undefined products get fresh values, together with the forced old-row entries.
All models retain 0*1=0*2=3. Thus t(x,x*y) retains a row collision for every t.

This is a research filter, not a proof exporter. A surviving term needs a
separate universal proof; a failed finite check only rejects this construction.
The Python implementation is not trusted by any Lean theorem.

Usage: python3 scripts/parastrophe_greedy_term_scan.py --degree 6 --output result.json
"""
import argparse
import itertools
import json
import time
from pathlib import Path
from spectrum_generate import load_equations
from collections import defaultdict


class Greedy:
    def __init__(self, n):
        self.n = n
        self.ops = {}
        self.inv = defaultdict(set)
        self.R2 = defaultdict(set)
        self.P = defaultdict(set)
        self.next = 4
        self.put(0, 1, 3)
        self.put(0, 2, 3)

    def known(self, a, b):
        return a if a == b else self.ops.get((a, b))

    def pre(self, b, c):
        return self.inv[b, c] | ({b} if b == c else set())

    def put(self, u, v, w):
        assert u != v or u == w
        assert (u, v) not in self.ops or self.ops[u, v] == w
        if (u, v) in self.ops:
            return
        self.ops[u, v] = w
        self.inv[v, w].add(u)
        t = self.known(w, v)
        if t is not None:
            self.R2[u, t].add(v)
        for z in self.pre(v, u):
            self.R2[z, w].add(v)
        t = self.known(v, w)
        if t is not None:
            self.P[v, t].add(u)
        for z in self.pre(u, v):
            self.P[u, w].add(z)

    def op(self, a, b):
        old = self.known(a, b)
        if old is not None:
            return old
        c = max(self.next, a + 1, b + 1)
        self.next = c + 1
        if self.n == 124:
            p = set(self.pre(b, a))
            v = b
        elif self.n == 1082:
            p = set(self.P[b, a])
            v = b
        elif self.n == 1288:
            p = set(self.R2[b, a])
            v = b
        elif self.n == 670:
            p = set(self.R2[a, b])
            v = a
        else:
            raise ValueError(self.n)
        self.put(a, b, c)
        for x in p:
            self.put(x, c, v)
        return c


def evaluate(term, x, y, op):
    if isinstance(term, str):
        return x if term == "x" else y
    return op(evaluate(term[0], x, y, op), evaluate(term[1], x, y, op))


def scan(source, degree, equations):
    model = Greedy(source)
    # Catch basic implementation errors before screening transformed operations.
    for x, y in itertools.product(range(8), repeat=2):
        assert evaluate(equations[source - 1][1], x, y, model.op) == x
    terms = [["x", "y"]]
    hits = []
    counts = []
    started = time.monotonic()
    for size in range(degree + 1):
        if size:
            terms.append(
                [
                    (a, b)
                    for i in range(size)
                    for a in terms[i]
                    for b in terms[size - 1 - i]
                    if a != b
                ]
            )
        counts.append(len(terms[size]))
        for term in terms[size]:

            def op(x, y):
                return evaluate(term, x, model.op(x, y), model.op)

            assert op(0, 1) == op(0, 2)
            for target in [464, 669, 879, 1075, 1278, 1285]:
                pairs = [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 0)]
                if all(
                    evaluate(equations[target - 1][1], x, y, op) == x for x, y in pairs
                ):
                    hits.append({"target": target, "term": term})
        print(
            f"E{source}: degree {size}, {len(terms[size])} contexts, {len(hits)} candidates",
            flush=True,
        )
    return {
        "source": source,
        "degree": degree,
        "counts": counts,
        "candidates": hits,
        "seconds": round(time.monotonic() - started, 2),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sources",
        type=int,
        nargs="+",
        choices=[124, 670, 1082, 1288],
        default=[124, 670, 1082, 1288],
    )
    parser.add_argument("--degree", type=int, choices=range(7), default=6)
    parser.add_argument("--output")
    args = parser.parse_args()
    equations = load_equations()
    results = [scan(n, args.degree, equations) for n in args.sources]
    if args.output:
        Path(args.output).write_text(json.dumps(results, indent=2) + "\n")
