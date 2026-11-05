#!/usr/bin/env python3
"""Bounded search for infinite collision models over a finite base.

The carrier is a finite magma times the finitely supported F2 sequences.
An operation uses pair-dependent linear coefficients from binary-tree shifts:
L_i selects coordinates 2n+i, and R_i inserts into coordinates 2n+i.
They satisfy L_i R_j = delta_ij I and R_0 L_0 + R_1 L_1 = I.

A and B use the finite bases AT and BT below. Some B must have a kernel,
so that the resulting operation has a row collision. Constraints evaluate
basis vectors; SAT candidates additionally undergo exact symbolic checking.
UNSAT excludes only this coefficient template over the selected finite base.
These are research results, not Lean certificates. Requires z3-solver.

Examples:
  python3 scripts/parastrophe_operator_bundles.py --equations 464 669
  python3 scripts/parastrophe_operator_bundles.py --equations 1117 --colors 1
The latter is a positive control: it should find a symbolically checked model.
"""
import argparse
import itertools
import json
import time
from concurrent.futures import ProcessPoolExecutor
import z3
from spectrum_generate import load_equations

E = load_equations()
# Each pair (p,q) is a low-bit output/input word; tuples are low bit first.
I = ((), ())
L0 = ((), (0,))
L1 = ((), (1,))
R0 = ((0,), ())
R1 = ((1,), ())
AT = [I, L0, L1, R0, R1, ((0,), (0,)), ((0,), (1,)), ((1,), (0,))]
BT = [I, L0, L1]


def value(t, n):
    p, q = t
    if any(((n >> i) & 1) != b for i, b in enumerate(q)):
        return
    return (n >> len(q)) * 2 ** len(p) + sum(b << i for i, b in enumerate(p))


def pmul(t, s):
    p, q = t
    r, u = s
    k = min(len(q), len(r))
    if q[:k] != r[:k]:
        return
    return p + r[k:], u + q[k:]


def mul(a, b):
    out = set()
    for t in a:
        for s in b:
            w = pmul(t, s)
            if w is None:
                continue
            if w in out:
                out.remove(w)
            else:
                out.add(w)
    return out


def norm(a, D=4):
    out = set()
    for p, q in a:
        assert len(q) <= D
        for w in itertools.product([0, 1], repeat=D - len(q)):
            v = (p + w, q + w)
            if v in out:
                out.remove(v)
            else:
                out.add(v)
    return out


def run(job):
    n, kind, k, sec = job
    base = lambda i, j: kind[i][j]
    A = [
        [[z3.Bool(f"a{i}{j}{v}") for v in range(len(AT))] for j in range(k)]
        for i in range(k)
    ]
    B = [
        [[z3.Bool(f"b{i}{j}{v}") for v in range(len(BT))] for j in range(k)]
        for i in range(k)
    ]
    S = z3.Solver()
    S.set(timeout=sec * 1000)
    for row in B:
        for b in row:
            S.add(z3.Or(*b))
    S.add(z3.Or([z3.And(z3.Not(b[0]), z3.Or(b[1], b[2])) for row in B for b in row]))

    def xor(v):
        if not v:
            return z3.BoolVal(False)
        r = v[0]
        for x in v[1:]:
            r = z3.Xor(r, x)
        return z3.simplify(r)

    def act(bits, terms, vec):
        d = {}
        for bit, t in zip(bits, terms):
            for j, v in vec.items():
                l = value(t, j)
                if l is not None:
                    d.setdefault(l, []).append(z3.And(bit, v))
        return {j: xor(v) for j, v in d.items()}

    def plus(a, b):
        return {j: xor([d[j] for d in [a, b] if j in d]) for j in a.keys() | b.keys()}

    def ev(t, x, y):
        if isinstance(t, str):
            return x if t == "x" else y
        i, u = ev(t[0], x, y)
        j, v = ev(t[1], x, y)
        return base(i, j), plus(act(A[i][j], AT, u), act(B[i][j], BT, v))

    start = time.monotonic()
    for i, j in itertools.product(range(k), repeat=2):
        for q in range(16, 32):
            for side in [0, 1]:
                x = (i, {q: z3.BoolVal(True)} if side == 0 else {})
                y = (j, {q: z3.BoolVal(True)} if side == 1 else {})
                c, v = ev(E[n - 1][1], x, y)
                if c != i:
                    return
                for l in v.keys() | x[1].keys():
                    S.add(v.get(l, z3.BoolVal(False)) == x[1].get(l, z3.BoolVal(False)))
    print("built", n, kind, k, round(time.monotonic() - start, 1), flush=True)
    t = time.monotonic()
    status = S.check()
    r = {
        "equation": n,
        "base": kind,
        "colors": k,
        "status": str(status),
        "seconds": round(time.monotonic() - t, 2),
    }
    if status == z3.sat:
        m = S.model()
        get = lambda bits, terms: {
            t for b, t in zip(bits, terms) if z3.is_true(m.eval(b))
        }
        a = [[get(bits, AT) for bits in row] for row in A]
        b = [[get(bits, BT) for bits in row] for row in B]

        def sym(t, x, y):
            if isinstance(t, str):
                return x if t == "x" else y
            i, u, v = sym(t[0], x, y)
            j, w, z = sym(t[1], x, y)
            return (
                base(i, j),
                mul(a[i][j], u) ^ mul(b[i][j], w),
                mul(a[i][j], v) ^ mul(b[i][j], z),
            )

        for i, j in itertools.product(range(k), repeat=2):
            c, u, v = sym(E[n - 1][1], (i, {I}, set()), (j, set(), {I}))
            assert c == i and norm(u) == norm({I}) and not norm(v), (i, j, u, v)
        r.update(
            A=[[sorted(v) for v in row] for row in a],
            B=[[sorted(v) for v in row] for row in b],
            symbolicCheck=True,
        )
    print(json.dumps(r), flush=True)
    return r


def base_models(n, k):
    """All row-bijective base models up to relabeling (small k only)."""
    perms = list(itertools.permutations(range(k)))

    def ev(t, x, y, m):
        if isinstance(t, str):
            return x if t == "x" else y
        return m[ev(t[0], x, y, m)][ev(t[1], x, y, m)]

    def canon(m):
        forms = []
        for p in perms:
            q = [[0] * k for _ in range(k)]
            for i, j in itertools.product(range(k), repeat=2):
                q[p[i]][p[j]] = p[m[i][j]]
            forms.append(tuple(tuple(row) for row in q))
        return min(forms)

    return sorted(
        {
            canon(m)
            for m in itertools.product(perms, repeat=k)
            if all(
                ev(E[n - 1][0], x, y, m) == ev(E[n - 1][1], x, y, m)
                for x, y in itertools.product(range(k), repeat=2)
            )
        }
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--equations", type=int, nargs="+", default=[464, 669, 879, 1075, 1278, 1285]
    )
    parser.add_argument("--colors", type=int, choices=[1, 2, 3], default=3)
    parser.add_argument("--seconds", type=int, default=90)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--output", help="Optional JSON report file")
    args = parser.parse_args()
    jobs = []
    for n in args.equations:
        if not 1 <= n <= len(E) or E[n - 1][0] != "x":
            parser.error(
                "This search currently requires a numbered law of the form x = ..."
            )
        bases = base_models(n, args.colors)
        print(f"E{n}: {len(bases)} base models", flush=True)
        jobs.extend((n, m, args.colors, args.seconds) for m in bases)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(run, jobs))
    if args.output:
        from pathlib import Path

        Path(args.output).write_text(json.dumps(results, indent=2) + "\n")
