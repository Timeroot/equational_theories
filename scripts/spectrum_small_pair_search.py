#!/usr/bin/env python3
"""Bounded model searches for the unresolved E667/12, E667/15 and related cases.

An UNSAT result in an automorphism, loop-isotope, or fixed-row family excludes
only that family. This research utility emits no Lean theorem. SAT tables are
independently evaluated against the original equation before being saved.

Examples:
  python3 scripts/spectrum_small_pair_search.py 667 12 --seconds 300
  python3 scripts/spectrum_small_pair_search.py 667 12 --loop A4 --seconds 180
  python3 scripts/spectrum_small_pair_search.py 1313 11 --cycles 1,2,2,2,2,2
"""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time

from spectrum_generate import load_equations, satisfies


def encode(law, n, right=False, normalize=True):
    R = range(n)
    cs = []
    top = n**3

    def p(x, y, z):
        return 1 + (x * n + y) * n + z

    def one(v):
        cs.append(v)
        cs.extend([-a, -b] for a, b in itertools.combinations(v, 2))

    for x, y in itertools.product(R, repeat=2):
        one([p(x, y, z) for z in R])
        one([p(x, z, y) for z in R])
        if right:
            one([p(z, x, y) for z in R])
    cache = {}

    def connect(a, b, out):
        aa = [(a, None)] if isinstance(a, int) else list(enumerate(a))
        bb = [(b, None)] if isinstance(b, int) else list(enumerate(b))
        for x, ax in aa:
            for y, by in bb:
                pre = [-v for v in [ax, by] if v is not None]
                for z in R:
                    cs.append(pre + [-p(x, y, z), out[z]])
                    cs.append(pre + [p(x, y, z), -out[z]])

    def node(t, env):
        nonlocal top
        if isinstance(t, str):
            return env[t]
        a, b = node(t[0], env), node(t[1], env)
        if isinstance(a, int) and isinstance(b, int):
            return [p(a, b, z) for z in R]
        key = (
            tuple(a) if isinstance(a, list) else a,
            tuple(b) if isinstance(b, list) else b,
        )
        if key in cache:
            return cache[key]
        out = list(range(top + 1, top + n + 1))
        top += n
        one(out)
        cache[key] = out
        connect(a, b, out)
        return out

    lhs, rhs = load_equations()[law - 1]
    assert lhs == "x" and rhs[0] == "y"
    for x, y in itertools.product(R, repeat=2):
        t = rhs[1]
        env = {"x": x, "y": y}
        connect(node(t[0], env), node(t[1], env), [p(y, z, x) for z in R])
    # Choose a non-idempotent zero if one exists, then label L_0's cycles.
    for x in R:
        if normalize:
            cs.append([-p(0, 0, 0), p(x, x, x)])
    for y, z in itertools.product(R, repeat=2):
        if normalize and z > y + 1:
            cs.append([-p(0, y, z)])
    cs = [c for c in cs if not any(-v in c for v in c)]
    return top, cs


def perm_group(n, even=False):
    ps = [
        p
        for p in itertools.permutations(range(n))
        if not even
        or sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n)) % 2 == 0
    ]
    return [[ps.index(tuple(a[b[i]] for i in range(n))) for b in ps] for a in ps]


def loop_cases():
    out = []
    for n in [11, 12, 15]:
        out.append(
            (
                1313 if n == 11 else 667,
                f"C{n}",
                [[(x + y) % n for y in range(n)] for x in range(n)],
                True,
            )
        )
    out.append((667, "A4", perm_group(4, True), True))
    for name, action, twist in [("C6xC2", 1, 0), ("D6", -1, 0), ("Dic3", -1, 3)]:
        elems = list(itertools.product(range(6), range(2)))
        out.append(
            (
                667,
                name,
                [
                    [
                        elems.index(
                            ((i + action**s * j + twist * s * t) % 6, (s + t) % 2)
                        )
                        for j, t in elems
                    ]
                    for i, s in elems
                ],
                True,
            )
        )
    g = perm_group(3)
    inv = [next(y for y in range(6) if g[x][y] == 0) for x in range(6)]
    elems = list(itertools.product(range(6), range(2)))
    t = []
    for a, s in elems:
        row = []
        for b, u in elems:
            c, v = (
                (g[a][b], 0)
                if (s, u) == (0, 0)
                else (
                    (g[b][a], 1)
                    if (s, u) == (0, 1)
                    else (g[a][inv[b]], 1) if (s, u) == (1, 0) else (g[inv[b]][a], 0)
                )
            )
            row.append(elems.index((c, v)))
        t.append(row)
    out.insert(0, (667, "CheinS3", t, False))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("law", type=int, choices=(667, 1313))
    parser.add_argument("order", type=int)
    parser.add_argument("--seconds", type=int, default=60)
    family = parser.add_mutually_exclusive_group()
    family.add_argument("--loop", help="C11, C12, C15, C6xC2, D6, Dic3, A4, or CheinS3")
    family.add_argument("--automorphism", help="comma-separated permutation")
    family.add_argument(
        "--cycles", help="first-row cycle lengths; cycle containing zero first"
    )
    parser.add_argument(
        "--output", type=Path, default=Path(".cache/spectrum-small-search")
    )
    parser.add_argument(
        "--lrat", action="store_true", help="also save the potentially large raw proof"
    )
    args = parser.parse_args()
    n, law = args.order, args.law
    if n <= 0 or args.seconds <= 0:
        parser.error("order and timeout must be positive")
    r = range(n)
    # Both supported laws force left and right cancellation in finite models.
    top, cs = encode(law, n, right=True, normalize=not (args.loop or args.automorphism))
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    scope = "all models; proved cancellation and relabelling reductions"
    if args.automorphism:
        aut = list(map(int, args.automorphism.split(",")))
        if sorted(aut) != list(r):
            parser.error("automorphism must be a permutation of the carrier")
        for x, y, z in itertools.product(r, repeat=3):
            cs.append([-p(x, y, z), p(aut[x], aut[y], aut[z])])
        scope = "models with the prescribed automorphism only"
    elif args.cycles:
        lengths = list(map(int, args.cycles.split(",")))
        if min(lengths) <= 0 or sum(lengths) != n:
            parser.error("cycle lengths must be positive and sum to the order")
        row, offset = [], 0
        for length in lengths:
            row += list(range(offset + 1, offset + length)) + [offset]
            offset += length
        cs += [[p(0, y, z)] for y, z in enumerate(row)]
        scope = "fixed first-row conjugacy type only"
    elif args.loop:
        choices = {(a, name): (table, group) for a, name, table, group in loop_cases()}
        if (law, args.loop) not in choices:
            parser.error("unsupported loop for this law")
        table, group = choices[law, args.loop]
        if len(table) != n:
            parser.error("loop size does not match order")
        assert all(sorted(row) == list(r) for row in table)
        assert all(sorted(table[x][y] for x in r) == list(r) for y in r)
        base = top
        a = lambda x, z: base + 1 + x * n + z
        b = lambda y, z: base + 1 + n * n + y * n + z
        top += 2 * n * n

        def one(v):
            cs.append(v)
            cs.extend([-u, -v] for u, v in itertools.combinations(v, 2))

        for i in r:
            for fun in (a, b):
                one([fun(i, z) for z in r])
                one([fun(z, i) for z in r])
        if group:
            cs.append([a(0, 0)])
        for x, y, u, v in itertools.product(r, repeat=4):
            cs.append([-a(x, u), -b(y, v), p(x, y, table[u][v])])
        scope = (
            "principal isotopes of specified loop; all group isotopes up to relabelling"
        )
    path = args.output
    path.parent.mkdir(parents=True, exist_ok=True)
    path.with_suffix(".cnf").write_text(
        f"p cnf {top} {len(cs)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in cs)
    )
    command = [
        "cadical",
        "--quiet",
        "-t",
        str(args.seconds),
        str(path.with_suffix(".cnf")),
    ]
    if args.lrat:
        command[1:1] = ["--shrink=0", "--lrat", "--no-binary"]
        command.append(str(path.with_suffix(".lrat")))
    start = time.monotonic()
    result = subprocess.run(command, capture_output=True, text=True)
    record = dict(
        law=law,
        order=n,
        scope=scope,
        loop=args.loop,
        automorphism=args.automorphism,
        cycles=args.cycles,
        status={10: "SAT", 20: "UNSAT"}.get(result.returncode, "UNKNOWN"),
        seconds=time.monotonic() - start,
        variables=top,
        clauses=len(cs),
    )
    if result.returncode == 10:
        values = {
            int(v)
            for line in result.stdout.splitlines()
            if line.startswith("v ")
            for v in line.split()[1:]
        }
        table = [
            next(z for z in r if p(x, y, z) in values)
            for x, y in itertools.product(r, repeat=2)
        ]
        assert satisfies(*load_equations()[law - 1], table, n)
        record["table"] = table
    path.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
