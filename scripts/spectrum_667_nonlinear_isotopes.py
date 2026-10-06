#!/usr/bin/env python3
"""Search E667 isotopes of a saved nonlinear quasigroup base.

Only the named isotope family is searched. UNSAT does not exclude all magmas
of that order. Every SAT table is checked against the original E667 equation.

Example:
  python3 scripts/spectrum_667_nonlinear_isotopes.py leftbol12-1 --seconds 180
"""
import argparse
import itertools
import json
import random
from pathlib import Path
import subprocess
import time

from spectrum_generate import load_equations, satisfies
from spectrum_small_pair_search import encode

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/spectrum/667_nonlinear_isotopes.json"


def formula(table, consequences=True, equal_inputs=False, one_way=False):
    n = len(table)
    r = range(n)
    assert all(sorted(row) == list(r) for row in table)
    assert all(sorted(table[x][y] for x in r) == list(r) for y in r)
    top, clauses = encode(667, n, right=True, normalize=False)
    p = lambda x, y, z: 1 + (x * n + y) * n + z

    def one(vs):
        clauses.append(vs)
        clauses.extend([-u, -v] for u, v in itertools.combinations(vs, 2))

    if consequences:
        assert top == 2 * n**3
        # The auxiliary table is q(x,y)=(x*x)*y, so each row is bijective.
        for x, z in itertools.product(r, repeat=2):
            one([n**3 + 1 + (x * n + y) * n + z for y in r])
        # Identities proved in Spectrum/Equation667ConstantDiagonal.lean.
        for x, a, b in itertools.permutations(r, 3):
            clauses.append([-p(x, x, a), -p(x, a, b), -p(x, b, x)])
        for x, a in itertools.product(r, repeat=2):
            clauses.append([-p(x, x, a), -p(x, a, x), p(a, a, a)])
        for e, x, a in itertools.product(r, repeat=3):
            clauses.extend(
                [
                    [-p(e, e, e), -p(x, x, e), -p(e, x, a), p(e, a, x)],
                    [-p(e, e, e), -p(e, x, a), -p(e, a, x), p(x, x, e)],
                    [-p(e, e, e), -p(x, x, e), -p(e, x, a), p(a, a, e)],
                ]
            )
        if n % 3 == 0:
            for e in r:
                clauses.append([-p(x, x, e) for x in r])

    base = top
    a = lambda x, z: base + 1 + x * n + z
    b = lambda x, z: base + 1 + n * n + x * n + z
    top += 2 * n * n
    for i in r:
        for f in (a, b):
            one([f(i, z) for z in r])
            one([f(z, i) for z in r])
    for x, y, u, v in itertools.product(r, repeat=4):
        z = table[u][v]
        clauses.append([-a(x, u), -b(y, v), p(x, y, z)])
        if not one_way:
            clauses.extend(
                [[-a(x, u), -p(x, y, z), b(y, v)], [-b(y, v), -p(x, y, z), a(x, u)]]
            )
    if equal_inputs:
        for x, z in itertools.product(r, repeat=2):
            clauses.extend([[-a(x, z), b(x, z)], [-b(x, z), a(x, z)]])
    return top, clauses, (p, a, b)


def projective_lex(top, clauses, a, b, table):
    """Conjugate both isotope permutations by automorphisms of PG(3,2).

    A lexicographically least representative in the full GL4(2) orbit satisfies
    every imposed comparison. Its first two entries are at most 1 and 3: fix
    the first vector and then extend the independent vectors to a basis.
    """
    n = 15
    assert table == [
        [x if x == y else ((x + 1) ^ (y + 1)) - 1 for y in range(n)] for x in range(n)
    ]
    rng = random.Random(66715)
    automorphisms = []
    while len(automorphisms) < 48:
        columns = rng.sample(range(1, 16), 4)
        images = []
        for v in range(1, 16):
            z = 0
            for k, c in enumerate(columns):
                if (v >> k) & 1:
                    z ^= c
            images.append(z)
        if 0 in images or len(set(images)) != 15:
            continue
        aut = [v - 1 for v in images]
        if aut not in automorphisms:
            automorphisms.append(aut)
    clauses.extend([[-a(0, z)] for z in range(2, 15)])
    clauses.extend([[-a(1, z)] for z in range(4, 15)])
    for aut in automorphisms:
        inv = [aut.index(x) for x in range(n)]
        top += 1
        prefix = top
        clauses.append([prefix])
        for f, x in itertools.product([a, b], range(n)):
            for u in range(n):
                for v in range(u):
                    clauses.append([-prefix, -f(x, u), -f(inv[x], inv[v])])
            top += 1
            following = top
            for u in range(n):
                clauses.append([-prefix, -f(x, u), -f(inv[x], inv[u]), following])
            prefix = following
    return top


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "base", help="name from data/spectrum/667_nonlinear_isotopes.json"
    )
    parser.add_argument("--seconds", type=int, default=60)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--basic", action="store_true", help="omit extra proved consequences"
    )
    parser.add_argument(
        "--one-way", action="store_true", help="original weaker isotope channeling"
    )
    parser.add_argument(
        "--equal-inputs",
        action="store_true",
        help="restrict to identical input permutations",
    )
    parser.add_argument("--keep-cnf", action="store_true")
    parser.add_argument(
        "--pg-lex",
        action="store_true",
        help="base-automorphism symmetry for gap-steiner15-1",
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error("timeout must be positive")
    bases = {record["name"]: record for record in json.loads(DATA.read_text())["bases"]}
    if args.base not in bases:
        parser.error("unknown base name")
    table = bases[args.base]["table"]
    n = len(table)
    top, clauses, (p, a, b) = formula(
        table, not args.basic, args.equal_inputs, args.one_way
    )
    if args.pg_lex:
        if args.base != "gap-steiner15-1":
            parser.error("--pg-lex requires gap-steiner15-1")
        top = projective_lex(top, clauses, a, b, table)
    path = args.output or ROOT / ".cache/e667-constructions" / ("run-" + args.base)
    path.parent.mkdir(parents=True, exist_ok=True)
    cnf = path.with_suffix(".cnf")
    cnf.write_text(
        f"p cnf {top} {len(clauses)}\n"
        + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
    )
    start = time.monotonic()
    cp = subprocess.run(
        [
            "cadical",
            "--quiet",
            f"--seed={args.seed}",
            "-t",
            str(args.seconds),
            str(cnf),
        ],
        capture_output=True,
        text=True,
    )
    record = {
        "law": 667,
        "order": n,
        "base": args.base,
        "scope": (
            "equal-input-permutation isotopes only"
            if args.equal_inputs
            else "all isotopes of the specified base, up to relabelling"
        ),
        "status": {10: "SAT", 20: "UNSAT"}.get(cp.returncode, "UNKNOWN"),
        "seconds": time.monotonic() - start,
        "limit_seconds": args.seconds,
        "seed": args.seed,
        "proved_consequences": not args.basic,
        "one_way_channeling": args.one_way,
        "equal_inputs": args.equal_inputs,
        "pg_lex": args.pg_lex,
    }
    if cp.returncode == 10:
        vals = {
            int(v)
            for line in cp.stdout.splitlines()
            if line.startswith("v ")
            for v in line.split()[1:]
        }
        witness = [
            next(z for z in range(n) if p(x, y, z) in vals)
            for x, y in itertools.product(range(n), repeat=2)
        ]
        assert satisfies(*load_equations()[666], witness, n)
        record.update(
            table=witness,
            a=[next(z for z in range(n) if a(x, z) in vals) for x in range(n)],
            b=[next(z for z in range(n) if b(x, z) in vals) for x in range(n)],
        )
    path.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
    if not args.keep_cnf:
        cnf.unlink()
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
