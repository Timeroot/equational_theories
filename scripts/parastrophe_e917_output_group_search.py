#!/usr/bin/env python3
"""Search E917's 22-operation candidate with its auxiliary outputs fixed.

All answers are external research, not Lean nonexistence certificates. The
normalization is proved in Equation917FrontProduct; the output group's free
action in Equation917OutputWords; and the necessary core defect for a
counterexample in Equation917RegularOutput. Input JSON is a list of objects
containing permutations `a` and `b`, with optional descriptive fields.
"""
import argparse
import itertools
import json
import multiprocessing as mp
import time
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Solver


def encode(a, b, require_defect=True, fixed_unit=None):
    n = len(a)
    assert sorted(a) == sorted(b) == list(range(n))
    cnf, memo = CNF(), {}
    nv = 0

    def value():
        nonlocal nv
        v = tuple(range(nv + 1, nv + n + 1))
        nv += n
        cnf.append(list(v))
        cnf.extend([[-x, -y] for x, y in itertools.combinations(v, 2)])
        return v

    m = [[value() for _ in range(n)] for _ in range(n)]
    for x, k in itertools.product(range(n), repeat=2):
        for y, z in itertools.combinations(range(n), 2):
            cnf.append([-m[x][y][k], -m[x][z][k]])
            cnf.append([-m[y][x][k], -m[z][x][k]])

    def op(x, y):
        if isinstance(x, int) and isinstance(y, int):
            return m[x][y]
        key = (x, y)
        if key in memo:
            return memo[key]
        z = value()
        memo[key] = z
        xx = [(x, [])] if isinstance(x, int) else [(i, [-x[i]]) for i in range(n)]
        yy = [(y, [])] if isinstance(y, int) else [(j, [-y[j]]) for j in range(n)]
        for i, px in xx:
            for j, py in yy:
                for k in range(n):
                    cnf.append(px + py + [-m[i][j][k], z[k]])
        return z

    def equal(x, y):
        if isinstance(y, int):
            cnf.append([x[y]])
        else:
            for u, v in zip(x, y):
                cnf.append([-u, v])
                cnf.append([-v, u])

    def permute(p, v):
        inverse = [p.index(k) for k in range(n)]
        return tuple(v[inverse[k]] for k in range(n))

    q = [op(op(x, m[x][x]), x) for x in range(n)]
    u = [op(x, q[x]) for x in range(n)]
    if fixed_unit is not None:
        assert sorted(fixed_unit) == list(range(n))
        for x in range(n):
            equal(u[x], fixed_unit[x])
    for x, y in itertools.product(range(n), repeat=2):
        equal(op(y, op(q[x], m[x][y])), a[x])
        equal(op(u[x], y), permute(b, m[x][y]))
        equal(m[a[x]][y], permute(a, m[b[x]][y]))
    if require_defect:
        # q(U(0)) != q(0), expanded without introducing another lookup vector.
        # When a,b have been normalized, moving the defect to 0 requires
        # transitivity of their common centralizer. The runner checks it.
        for x, k in itertools.product(range(n), repeat=2):
            cnf.append([-u[0][x], -q[x][k], -q[0][k]])
    return cnf, m, u


def centralizer_transitive(a, b):
    """Construct a commuting relabeling taking 0 to each possible defect."""
    n = len(a)
    for target in range(n):
        p = {0: target}
        pending = [0]
        while len(p) <= n:
            for x in pending:
                for f in (a, b):
                    y, z = f[x], f[p[x]]
                    if y in p:
                        if p[y] != z:
                            return False
                    elif z in p.values():
                        return False
                    else:
                        p[y] = z
                        pending.append(y)
            if len(p) == n:
                break
            x = next(x for x in range(n) if x not in p)
            z = next(z for z in range(n) if z not in p.values())
            p[x] = z
            pending = [x]
        if sorted(p.values()) != list(range(n)):
            return False
        if any(p[f[x]] != f[p[x]] for f in (a, b) for x in range(n)):
            return False
    return True


def check(table, a, b, u):
    n = len(table)
    q = [table[table[x][table[x][x]]][x] for x in range(n)]
    assert all(sorted(row) == list(range(n)) for row in table)
    assert all(sorted(table[x][y] for x in range(n)) == list(range(n)) for y in range(n))
    assert all(table[x][q[x]] == u[x] for x in range(n))
    for x, y in itertools.product(range(n), repeat=2):
        assert table[y][table[q[x]][table[x][y]]] == a[x]
        assert table[u[x]][y] == b[table[x][y]]
        assert table[a[x]][y] == a[table[b[x]][y]]
    # Independently evaluate the literal four-variable identity.
    for x, y, v, z in itertools.product(range(n), repeat=4):
        t = table[y][v]
        f = table[z][table[q[t]][table[t][z]]]
        assert table[table[u[y]][v]][table[q[x]][table[x][f]]] == x
    assert any(q[u[x]] != q[x] for x in range(n))


def worker(conn, a, b, fixed_unit=None):
    start = time.monotonic()
    cnf, m, u = encode(a, b, require_defect=fixed_unit is None, fixed_unit=fixed_unit)
    meta = {'variables': cnf.nv, 'clauses': len(cnf.clauses)}
    conn.send(meta)
    with Solver(name='cadical195', bootstrap_with=cnf) as solver:
        ans = solver.solve()
        result = dict(meta, status='sat' if ans else 'unsat', stats=solver.accum_stats())
        if ans:
            true = {v for v in solver.get_model() if v > 0}
            val = lambda v: next(x for x, k in enumerate(v) if k in true)
            table = [[val(v) for v in row] for row in m]
            unit = [val(v) for v in u]
            check(table, a, b, unit)
            result.update(table=table, U=unit)
    result['seconds'] = time.monotonic() - start
    conn.send(result)
    conn.close()


def run(a, b, seconds, fixed_unit=None):
    if fixed_unit is None:
        assert centralizer_transitive(a, b), 'Normal form must allow the defect at zero'
    else:
        # A fixed-point-free U already excludes the basis. Do not also put
        # the core defect at zero: this smaller centralizer need not be transitive.
        assert sorted(fixed_unit) == list(range(len(a)))
        assert all(x != y for x, y in enumerate(fixed_unit))
    ctx = mp.get_context('spawn')
    receive, send = ctx.Pipe(False)
    process = ctx.Process(target=worker, args=(send, a, b, fixed_unit))
    process.start()
    send.close()
    process.join(seconds)
    result = {'status': 'timeout' if process.is_alive() else 'error', 'time_limit': seconds}
    if process.is_alive():
        process.terminate()
        process.join()
    while receive.poll():
        try:
            result.update(receive.recv())
        except EOFError:
            break
    receive.close()
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cases', type=Path)
    parser.add_argument('--seconds', type=float, default=90)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error('The time limit must be positive')
    results = []
    cases = json.loads(args.cases.read_text())
    if isinstance(cases, dict):
        cases = cases['records']
    for case in cases:
        row = {k: case[k] for k in ('case', 'group', 'a', 'b', 'fixed_unit') if k in case}
        row.update(run(case['a'], case['b'], args.seconds, case.get('fixed_unit')))
        results.append(row)
        print(row.get('case'), row['status'], row.get('seconds'), flush=True)
        args.output.write_text(json.dumps({
            'candidate_operations': 22,
            'status': 'external research only; not Lean nonexistence proofs',
            'records': results,
        }, indent=2) + '\n')
        if row['status'] == 'sat':
            break
