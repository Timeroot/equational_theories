"""Exploratory necessary-constraint filter, NOT a proof of nonexistence.

Requires the z3-solver Python package. No full magma table or refutation
certificate is produced.
"""
import argparse
import z3

parser = argparse.ArgumentParser()
parser.add_argument('--size', type=int, default=8)
parser.add_argument('--reciprocal', type=int, required=True)
parser.add_argument('--timeout', type=int, default=30)
parser.add_argument('--ordinary', action='store_true')
parser.add_argument('--epsilon', type=int, default=1)
parser.add_argument('--delta', type=int, default=0)
parser.add_argument('--partial', action='store_true')
parser.add_argument('--one-sided', action='store_true')
parser.add_argument('--no-uniqueness', action='store_true')
args = parser.parse_args()
cells = [(p, q) for p in range(3) for q in range(3)][:args.size]
f, b = len(cells), args.reciprocal
s = z3.Solver()
s.set(timeout=1000 * args.timeout)
F = [z3.Int(f'F_{i}') for i in range(f)]
G = [z3.Int(f'G_{i}') for i in range(f)]
out = [[z3.Bool(f'out_{k}_{t}') for t in range(9)] for k in range(b)]
inc = [[z3.Bool(f'in_{k}_{t}') for t in range(9)] for k in range(b)]
left = [[z3.Int(f'left_{i}_{t}') for t in range(9)] for i in range(f)]
right = [[z3.Int(f'right_{i}_{t}') for t in range(9)] for i in range(f)]
for i in range(f):
    s.add(F[i] >= 0, F[i] < b, G[i] >= 0, G[i] < b)
    s.add(F[i] <= i)
    if i:
        s.add(z3.Or(F[i] == 0, *[F[i] == F[j] + 1 for j in range(i)]))
    for j in range(i):
        if cells[i][0] == cells[j][0]:
            s.add(F[i] != F[j])
        if cells[i][1] == cells[j][1]:
            s.add(G[i] != G[j])
        s.add(z3.Or(F[i] != F[j], G[i] != G[j]))
    for t in range(9):
        s.add(left[i][t] >= -1, left[i][t] < 3)
        s.add(right[i][t] >= -1, right[i][t] < 3)
        for k in range(b):
            s.add(z3.Implies(F[i] == k, (left[i][t] == -1) == out[k][t]))
            s.add(z3.Implies(G[i] == k, (right[i][t] == -1) == inc[k][t]))
for k in range(b):
    if not args.partial:
        s.add(z3.Or(*[F[i] == k for i in range(f)]))
        s.add(z3.Or(*[G[i] == k for i in range(f)]))
    s.add(z3.PbEq([(x, 1) for x in out[k]], 3))
    s.add(z3.PbEq([(x, 1) for x in inc[k]], 3))
    for h in range(3):
        s.add(z3.PbEq([(out[k][3*p+q], 1) for p in range(3) for q in range(3) if (p+q)%3 == h], 1))
        s.add(z3.PbEq([(inc[k][3*p+q], 1) for p in range(3) for q in range(3) if (p-q)%3 == h], 1))
for a in range(f):
    for c, (pc, qc) in enumerate(cells):
        for d, (pd, qd) in enumerate(cells):
            s.add(z3.Implies(z3.And(F[c] != G[a], F[d] != G[c]), left[a][3*pc+qd] != qc))
            if not args.one_sided:
                s.add(z3.Implies(z3.And(F[a] != G[c], F[c] != G[d]), right[a][3*pd+qc] != pc))
if args.ordinary:
    D = [[z3.Bool(f'D_{u}_{v}') for v in range(9)] for u in range(9)]
    for t in range(9):
        for h in range(3):
            s.add(z3.PbEq([(D[t][3*p+q], 1) for p in range(3) for q in range(3) if (p+q)%3 == h], 1))
            s.add(z3.PbEq([(D[3*p+q][t], 1) for p in range(3) for q in range(3) if (p-q)%3 == h], 1))
    for a, (pa, qa) in enumerate(cells):
        for t in range(9):
            if not args.no_uniqueness:
                s.add(z3.Implies(left[a][t] != -1, z3.PbEq([(D[3*p+qa][t], 1) for p in range(3)], 1)))
                if not args.one_sided:
                    s.add(z3.Implies(right[a][t] != -1, z3.PbEq([(D[t][3*pa+q], 1) for q in range(3)], 1)))
            for j in range(3):
                pv = (args.epsilon * (pa+j-args.delta)+qa)%3
                qv = (args.epsilon * (j-qa)+args.delta-pa)%3
                s.add(z3.Implies(left[a][t] == j, D[3*pv+qa][t]))
                if not args.one_sided:
                    s.add(z3.Implies(right[a][t] == j, D[t][3*pa+qv]))
status = s.check()
print('size', f, 'reciprocal', b, status)
if status == z3.sat:
    m = s.model()
    print('F', [m.eval(x).as_long() for x in F])
    print('G', [m.eval(x).as_long() for x in G])
    print('out', [[t for t in range(9) if z3.is_true(m.eval(out[k][t]))] for k in range(b)])
    print('in', [[t for t in range(9) if z3.is_true(m.eval(inc[k][t]))] for k in range(b)])
