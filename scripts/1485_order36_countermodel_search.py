"""Bounded finite E1485 countermodel search at order 36.

Requires python-sat, including its Cadical195 solver. See
docs/1485_order36_countermodel_search.md for the mathematical constraints.
A result of null is UNKNOWN, never UNSAT. Use an external wall-clock cap
as well as --conflicts; neither resource bound is a mathematical result.
"""
import argparse
import itertools
import json
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

parser = argparse.ArgumentParser()
parser.add_argument("--minimum", type=int, choices=[3, 4], default=4)
parser.add_argument("--conflicts", type=int, default=50000)
parser.add_argument("--uniform", action="store_true")
parser.add_argument("--smoke-n8", action="store_true")
parser.add_argument("--central-anchor", action="store_true")
args = parser.parse_args()
n = 8 if args.smoke_n8 else 36
r = 2 if args.smoke_n8 else args.minimum
degrees = [2, 4] if args.smoke_n8 else ([4, 6, 9] if r == 4 else [3, 4, 6, 9, 12])
k = len(degrees)
started = time.monotonic()

def product(x, y, z):
    return 1 + (x * n + y) * n + z

a_offset = n ** 3
g_offset = a_offset + n ** 2
d_offset = g_offset + n ** 3
s_offset = d_offset + n * k

def adjacent(x, y):
    return a_offset + 1 + x * n + y

def auxiliary(x, a, b):
    return g_offset + 1 + (x * n + a) * n + b

def degree(x, i):
    return d_offset + 1 + x * k + i

def sharp(x, y):
    return s_offset + 1 + x * n + y

pool = IDPool(start_from=s_offset + n ** 2 + 1)
solver = Solver(name="cadical195", use_timer=True)
clauses = 0

def add(clause):
    global clauses
    solver.add_clause(clause)
    clauses += 1

def cardinal(literals, bound, relation="equals", guard=None):
    encoding = getattr(CardEnc, relation)(
        literals, bound=bound, vpool=pool, encoding=EncType.seqcounter
    )
    for clause in encoding:
        add(clause if guard is None else [-guard] + clause)

for x, y in itertools.product(range(n), repeat=2):
    cardinal([product(x, y, z) for z in range(n)], 1)

for x in range(n):
    cardinal([degree(x, i) for i in range(k)], 1)
    for i, d in enumerate(degrees):
        cardinal([adjacent(x, z) for z in range(n)], d, guard=degree(x, i))
        cardinal([adjacent(z, x) for z in range(n)], d, guard=degree(x, i))
    if x + 1 < n:
        for i in range(k):
            for j in range(i):
                add([-degree(x, i), -degree(x + 1, j)])

# Relabeling permits sorted degrees, and the extremal product is n.
add([degree(0, 0)])
add([degree(n - 1, k - 1)])
cardinal([degree(x, 0) for x in range(n)], r, relation="atleast")
# A non-full core has defect at least r:
# docs/1485_small_central_defects.md. The pinned smoke model is full-core.
central_cap = r * r if args.smoke_n8 else r * r - r
cardinal([degree(x, 0) for x in range(n)], central_cap, relation="atmost")
if r == 4:
    add([degree(x, 1) for x in range(n)])

if args.central_anchor:
    # Row(0) and Col(0) consist of top vertices, have size r, and
    # meet only at 0*0. Relabel top vertices to fix these two sets.
    row_zero = list(range(n - r, n))
    col_zero = list(range(n - 2 * r + 1, n - r)) + [n - 1]
    for x in range(n):
        add([adjacent(0, x)] if x in row_zero else [-adjacent(0, x)])
        add([adjacent(x, 0)] if x in col_zero else [-adjacent(x, 0)])
    add([product(0, 0, n - 1)])
    # Every element of Row(0) has a central sharp successor, so
    # L_0 restricted to the central set surjects onto Row(0).
    # Relabel r-1 other central vertices to choose distinct witnesses.
    for x in range(1, r):
        add([product(0, x, n - r + x - 1)])

if args.smoke_n8:
    original = [
        [4, 4, 5, 5, 4, 4, 5, 5],
        [6, 6, 7, 7, 6, 7, 7, 6],
        [4, 4, 5, 5, 4, 4, 5, 5],
        [6, 6, 7, 7, 6, 7, 7, 6],
        [4, 4, 5, 5, 0, 0, 1, 1],
        [6, 6, 7, 7, 2, 2, 3, 3],
        [4, 4, 7, 7, 0, 0, 1, 1],
        [6, 6, 5, 5, 2, 2, 3, 3],
    ]
    order = sorted(range(n), key=lambda x: len(set(original[x])))
    if args.central_anchor:
        h = order[0]
        central = [x for x in range(n) if len(set(original[x])) == r]
        common = original[h][h]
        row_rest = sorted(set(original[h]) - {common})
        col_rest = sorted({original[x][h] for x in range(n)} - {common})
        fixed = {0: h, n - 1: common}
        for i, value in enumerate(row_rest):
            fixed[n - r + i] = value
            fixed[i + 1] = next(x for x in central if original[h][x] == value)
        for i, value in enumerate(col_rest):
            fixed[n - 2 * r + 1 + i] = value
        assert len(set(fixed.values())) == len(fixed)
        remaining = [x for x in order if x not in fixed.values()]
        order = [fixed[i] if i in fixed else remaining.pop(0) for i in range(n)]
    inverse = {x: i for i, x in enumerate(order)}
    known = [[inverse[original[x][y]] for y in order] for x in order]
    for x, y in itertools.product(range(n), repeat=2):
        add([product(x, y, known[x][y])])

for x, y, z in itertools.product(range(n), repeat=3):
    p = product(x, y, z)
    add([-p, adjacent(x, z)])
    add([-p, adjacent(z, y)])
for x, y in itertools.product(range(n), repeat=2):
    add([-adjacent(x, y)] + [product(x, z, y) for z in range(n)])
    add([-adjacent(x, y)] + [product(z, y, x) for z in range(n)])
    add([-sharp(x, y), adjacent(x, y)])
    for i, di in enumerate(degrees):
        for j, dj in enumerate(degrees):
            guard = [-degree(x, i), -degree(y, j)]
            if di * dj < n:
                add(guard + [-adjacent(x, y)])
            if di * dj == n:
                add(guard + [-adjacent(x, y), sharp(x, y)])
            else:
                add(guard + [-sharp(x, y)])

for x in range(n):
    add([sharp(x, y) for y in range(n)])
    add([sharp(y, x) for y in range(n)])

for x, a, z in itertools.product(range(n), repeat=3):
    add([-sharp(x, a), -adjacent(a, z), product(x, z, a)])
    add([-adjacent(x, a), -sharp(a, z), product(x, z, a)])

if args.uniform:
    for x, z in itertools.product(range(n), repeat=2):
        for i, d in enumerate(degrees):
            cardinal([product(x, y, z) for y in range(n)], n // d,
                        relation="atmost", guard=degree(x, i))
            cardinal([product(y, x, z) for y in range(n)], n // d,
                        relation="atmost", guard=degree(x, i))

print(json.dumps({"stage": "structure", "seconds": time.monotonic() - started,
                  "clauses": clauses, "aux_top": pool.top}), flush=True)

# G(x,a,b) is forced when a=y*x and b belongs to Col(y).
# Ordinary adjacency b->y is precisely b in Col(y), not Row(y).
for x, y, a, b in itertools.product(range(n), repeat=4):
    add([-product(y, x, a), -adjacent(b, y), auxiliary(x, a, b)])
# It then forces a*(x*b)=x. Together these are exactly E1485.
for x, a, b, c in itertools.product(range(n), repeat=4):
    add([-auxiliary(x, a, b), -product(x, b, c), product(a, c, x)])

print(json.dumps({"stage": "ready", "n": n, "minimum": r,
                  "degrees": degrees, "uniform": args.uniform,
                  "central_anchor": args.central_anchor,
                  "seconds": time.monotonic() - started,
                  "clauses": clauses, "aux_top": pool.top,
                  "conflict_budget": args.conflicts}), flush=True)
solver.conf_budget(args.conflicts)
answer = solver.solve_limited()
print(json.dumps({"stage": "result", "result": answer,
                  "seconds": time.monotonic() - started,
                  "solver_seconds": solver.time(), "stats": solver.accum_stats()}), flush=True)
if answer:
    model = set(v for v in solver.get_model() if v > 0)
    table = [[next(z for z in range(n) if product(x, y, z) in model)
              for y in range(n)] for x in range(n)]
    row_degrees = [len(set(row)) for row in table]
    assert min(row_degrees) == r
    assert set(row_degrees) <= set(degrees)
    assert sum(d == r for d in row_degrees) <= central_cap
    assert all(table[table[y][x]][table[x][table[z][y]]] == x
               for x, y, z in itertools.product(range(n), repeat=3))
    assert all(len({table[x][y] for x in range(n)}) == row_degrees[y]
               for y in range(n))
    print(json.dumps({"stage": "verified_model", "row_degrees": row_degrees,
                      "table": table}), flush=True)
solver.delete()
