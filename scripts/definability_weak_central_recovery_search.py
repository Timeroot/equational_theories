#!/usr/bin/env python3
"""Exploratory necessary-condition search for E1485 -> E1483 mutual recovery.

Run with a case 0..3 under an external timeout, for example:
  timeout 900 python3 scripts/definability_weak_central_recovery_search.py 0
Requires python-sat and numpy. Neither timeout nor SAT settles a board cell;
even UNSAT requires a separate proof certificate and justification in Lean.
"""
import argparse
import itertools
import json
import time
from importlib import import_module
from pathlib import Path

import numpy as np
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

from definability_weak_central_check import (
    generated_subalgebra,
    binary_clone,
    holds_1483,
)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("case", type=int, choices=range(4))
parser.add_argument("--output", type=Path)
parser.add_argument(
    "--solver", choices=("cadical195", "maplecm", "glucose42"), default="cadical195"
)
parser.add_argument(
    "--strong",
    action="store_true",
    help="use proved E1483 rank constraints and verified orbit symmetries",
)
parser.add_argument(
    "--bit-channel",
    action="store_true",
    help="with --strong, also encode the five output bits",
)
parser.add_argument(
    "--rank-edges",
    action="store_true",
    help="with --strong, constrain exact ranks along row and column edges",
)
parser.add_argument(
    "--encode-only",
    action="store_true",
    help="verify and construct constraints, then stop without solving",
)
parser.add_argument(
    "--monogenic",
    action="store_true",
    help="require generation by each of 1, 3, 7 instead of by the pair 11, 21",
)
args = parser.parse_args()
if (args.bit_channel or args.rank_edges) and not args.strong:
    parser.error("--bit-channel and --rank-edges require --strong")
data = json.loads(
    (
        Path(__file__).resolve().parent.parent
        / "data/definability_weak_central_recovery_search.json"
    ).read_text()
)
source = np.array(import_module("1485_structure_check").twisted32(), dtype=np.int32)
x, y, z = np.indices((32, 32, 32))
assert np.array_equal(source[source[y, x], source[x, source[z, y]]], x)
rotation = np.array([((x << 1) & 31) | (x >> 4) for x in range(32)])
assert np.array_equal(source[np.ix_(rotation, rotation)], rotation[source])
assert np.flatnonzero(source.diagonal() == np.arange(32)).tolist() == [
    11,
    13,
    21,
    22,
    26,
]
assert generated_subalgebra(source, (11, 21)) == tuple(range(32))
seed_sets = [(1,), (3,), (7,)] if args.monogenic else [(11, 21)]
for seeds in seed_sets:
    assert generated_subalgebra(source, seeds) == tuple(range(32))
for relation in data["relations"]:
    a, b = np.divmod(np.array(relation), 32)
    membership = np.zeros(1024, dtype=bool)
    membership[relation] = True
    assert np.all(
        membership[32 * source[a[:, None], a[None, :]] + source[b[:, None], b[None, :]]]
    )
for entry in data["subclone_targets"]:
    sub = entry["sub"]
    positions = {x: i for i, x in enumerate(sub)}
    small = np.array(
        [[positions[int(source[a, b])] for b in sub] for a in sub], dtype=np.uint8
    )
    targets = {op.tobytes() for op in binary_clone(small) if holds_1483(op)}
    saved = {
        np.array([[positions[x] for x in row] for row in op], dtype=np.uint8).tobytes()
        for op in entry["targets"]
    }
    assert targets == saved
print(
    "Source generation, all compatible relations, and local target clones verified.",
    flush=True,
)
n = 32
case = args.case
rot = lambda x: ((x << 1) & 31) | (x >> 4)
start = time.monotonic()
pool = IDPool()
cache = {}


def canonical(t):
    if t in cache:
        return cache[t]
    orb = []
    v = t
    for _ in range(5):
        orb.append(v)
        v = tuple(map(rot, v))
    m = min(orb)
    for v in orb:
        cache[v] = m
    return m


P = lambda x, y, z: pool.id(("p",) + canonical((x, y, z)))
R = lambda y, b: pool.id(("r",) + canonical((y, b)))
Good = lambda x, a, b: pool.id(("g",) + canonical((x, a, b)))
solver = Solver(name=args.solver)
count = 0


def add(c):
    global count
    solver.add_clause(c)
    count += 1


for x, y in itertools.product(range(n), repeat=2):
    if (x, y) != canonical((x, y)):
        continue
    v = [P(x, y, z) for z in range(n)]
    cnf = CardEnc.equals(v, bound=1, vpool=pool, encoding=EncType.seqcounter)
    for c in cnf:
        add(c)
for x in range(n):
    add([P(x, x, x)] if x in [11, 13, 21, 22, 26] else [-P(x, x, x)])
entries = data["subclone_targets"]
for entry, choice in [(entries[0], case % 2), (entries[1], case // 2)]:
    sub = entry["sub"]
    T = entry["targets"][choice]
    for i, x in enumerate(sub):
        for j, y in enumerate(sub):
            add([P(x, y, T[i][j])])
for y, z, b in itertools.product(range(n), repeat=3):
    if (y, z, b) != canonical((y, z, b)):
        continue
    add([-P(y, z, b), R(y, b)])
for x, a, b, c in itertools.product(range(n), repeat=4):
    if (x, a, b, c) != canonical((x, a, b, c)):
        continue
    add([-Good(x, a, b), -P(x, b, c), P(a, c, x)])
for x, y, a, b in itertools.product(range(n), repeat=4):
    if (x, y, a, b) != canonical((x, y, a, b)):
        continue
    add([-P(y, x, a), -R(y, b), Good(x, a, b)])
# Source-compatible binary relations constrain every possible defining term.
relations = data["relations"]
rel_count = 0
for ri, relation in enumerate(relations):
    if len(relation) == n * n:
        continue
    pairs = [divmod(v, n) for v in relation]
    rows = {u: [v for a, v in pairs if a == u] for u in range(n)}
    for (a, b), (c, d) in itertools.product(pairs, repeat=2):
        if (a, c, b, d) != canonical((a, c, b, d)):
            continue
        for u in range(n):
            allowed = rows[u]
            if len(allowed) == n:
                continue
            add([-P(a, c, u)] + [P(b, d, v) for v in allowed])
            rel_count += 1
print(
    "relations encoded",
    rel_count,
    "seconds",
    round(time.monotonic() - start, 2),
    flush=True,
)
# Mutual recovery preserves every generated subalgebra. Independent generation
# orders allow each selected seed set to reach the entire carrier.
truth = pool.id(("true",))
add([truth])


def less(tag, x, y):
    if x == y:
        return -truth
    return pool.id(("lt", tag, x, y)) if x < y else -pool.id(("lt", tag, y, x))


for tag, selected in enumerate(seed_sets):
    seeds = set(selected)
    for x in seeds:
        for y in set(range(n)) - seeds:
            add([less(tag, x, y)])
    for x, y, z in itertools.permutations(range(n), 3):
        add([-less(tag, x, y), -less(tag, y, z), less(tag, x, z)])
    for z in set(range(n)) - seeds:
        choices = []
        for x, y in itertools.product(range(n), repeat=2):
            if x == z or y == z:
                continue
            v = pool.id(("generate", tag, z, x, y))
            choices.append(v)
            add([-v, P(x, y, z)])
            add([-v, less(tag, x, z)])
            add([-v, less(tag, y, z)])
        add(choices)
print("generation encoded", pool.top, "variables", count, "clauses", flush=True)
# The dual E1483 identity follows from two instances of the source identity.
Col = lambda y, b: pool.id(("col",) + canonical((y, b)))
DualGood = lambda x, a, b: pool.id(("dg",) + canonical((x, a, b)))
for y, b in itertools.product(range(n), repeat=2):
    if (y, b) != canonical((y, b)):
        continue
    add([-R(y, b)] + [P(y, z, b) for z in range(n)])
    add([-Col(y, b)] + [P(z, y, b) for z in range(n)])
for y, z, b in itertools.product(range(n), repeat=3):
    if (y, z, b) != canonical((y, z, b)):
        continue
    add([-P(z, y, b), Col(y, b)])
for x, a, b, c in itertools.product(range(n), repeat=4):
    if (x, a, b, c) != canonical((x, a, b, c)):
        continue
    add([-DualGood(x, a, b), -P(b, x, c), P(c, a, x)])
for x, y, a, b in itertools.product(range(n), repeat=4):
    if (x, y, a, b) != canonical((x, y, a, b)):
        continue
    add([-P(x, y, a), -Col(y, b), DualGood(x, a, b)])
if args.strong:
    from definability_weak_central_constraints import strengthen_search

    strengthen_search(
        n,
        pool,
        solver,
        add,
        P,
        R,
        Col,
        canonical,
        truth,
        entries,
        relations,
        source,
        bit_channel=args.bit_channel,
        rank_edges=args.rank_edges,
    )
print("dual law encoded", pool.top, "variables", count, "clauses", flush=True)
print(
    "ready case",
    case,
    "vars",
    pool.top,
    "clauses",
    count,
    "seconds",
    round(time.monotonic() - start, 2),
    flush=True,
)
if args.encode_only:
    solver.delete()
    print("Encoding checked; no satisfiability result.", flush=True)
    raise SystemExit(0)
result = solver.solve()
print("RESULT", case, result, "seconds", round(time.monotonic() - start, 2), flush=True)
if result:
    mod = set(v for v in solver.get_model() if v > 0)
    T = [
        [next(z for z in range(n) if P(x, y, z) in mod) for y in range(n)]
        for x in range(n)
    ]
    assert all(
        T[T[y][x]][T[x][T[y][z]]] == x
        for x, y, z in itertools.product(range(n), repeat=3)
    )
    assert all((T[x][x] == x) == (x in [11, 13, 21, 22, 26]) for x in range(n))
    for seeds in seed_sets:
        assert generated_subalgebra(np.array(T), seeds) == tuple(range(n))
    target = np.array(T)
    assert np.array_equal(target[np.ix_(rotation, rotation)], rotation[target])
    for relation in relations:
        a, b = np.divmod(np.array(relation), n)
        membership = np.zeros(n * n, dtype=bool)
        membership[relation] = True
        assert np.all(
            membership[
                n * target[a[:, None], a[None, :]] + target[b[:, None], b[None, :]]
            ]
        )
    if args.output:
        args.output.write_text(json.dumps(T) + "\n")
    print("TARGET VERIFIED", flush=True)
elif args.output:
    args.output.write_text(
        json.dumps(
            {
                "case": case,
                "vars": pool.top,
                "clauses": count,
                "solver": args.solver,
                "strong": args.strong,
                "bit_channel": args.bit_channel,
                "rank_edges": args.rank_edges,
                "status": "unsat; not a Lean certificate",
            }
        )
        + "\n"
    )
