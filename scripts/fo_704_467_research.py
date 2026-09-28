#!/usr/bin/env python3
"""Reproducible small symmetry-reduced probes for E704 -> E467.

Default: exhaust the shifted-power permutation family, using only Python.
--smt P: search every scalar-equivariant operation on F_P using Z3.
An SMT timeout is not a refutation. This script does not prove a Lean theorem.
"""

import argparse
import json
import math


def verify(p, d, h):
    inverse = [0] + [pow(t, -1, p) for t in range(1, p)]

    def op(x, y):
        return (d * y if x == 0 else x * h[y * inverse[x] % p]) % p

    return all(
        x == op(y, op(x, op(x, op(y, y))))
        for x in range(p) for y in range(p)
    )


def powers(p):
    inverse = [0] + [pow(t, -1, p) for t in range(1, p)]
    tried = 0
    survivors = 0
    witnesses = []
    for k in range(1, p - 1):
        if math.gcd(k, p - 1) != 1:
            continue
        base = [pow(t, k, p) for t in range(p)]
        for shift in range(p):
            shifted = [base[(t + shift) % p] for t in range(p)]
            for b in range(1, p):
                scaled = [b * t % p for t in shifted]
                for a in range(p):
                    tried += 1
                    h = [(a + t) % p for t in scaled]
                    c = h[1]
                    if not c or not h[0] or c * h[c] % p != 1:
                        continue
                    if h[c * c % p] != c * c % p or not h[h[0]]:
                        continue
                    d = inverse[h[h[0]]]
                    survivors += 1
                    if h[d * d * c % p] != 0:
                        continue
                    if all(h[t * h[h[inverse[t] * c % p]] % p] == t
                           for t in range(1, p)):
                        assert verify(p, d, h)
                        witnesses.append(dict(a=a, b=b, shift=shift, k=k, d=d, h=h))
    return dict(prime=p, coefficient_tuples=tried,
                surviving_diagonal_tests=survivors, witnesses=witnesses)


def smt(p, timeout):
    import z3

    width = p.bit_length()
    solver = z3.SolverFor("QF_AUFBV")
    solver.set(timeout=timeout * 1000)
    h = z3.Array("h", z3.BitVecSort(width), z3.BitVecSort(width))
    d = z3.BitVec("d", width)

    def value(n):
        return z3.BitVecVal(n, width)

    def H(x):
        return z3.Select(h, value(x) if isinstance(x, int) else x)

    def mul(a, b):
        a = value(a) if isinstance(a, int) else a
        b = value(b) if isinstance(b, int) else b
        product = z3.ZeroExt(width, a) * z3.ZeroExt(width, b)
        return z3.Extract(width - 1, 0,
                          z3.URem(product, z3.BitVecVal(p, 2 * width)))

    for i in range(p):
        solver.add(z3.ULT(H(i), p))
    solver.add(z3.ULT(d, p), d != 0, H(0) != 0, H(1) != 0,
               z3.Distinct([H(i) for i in range(p)]))
    c = H(1)
    solver.add(H(mul(mul(d, d), c)) == 0)
    for t in range(1, p):
        solver.add(H(mul(t, H(H(mul(pow(t, -1, p), c))))) == t)
    solver.add(mul(d, H(H(0))) == 1)
    solver.add(z3.Distinct([d] + [mul(t, H(pow(t, -1, p)))
                                  for t in range(1, p)]))
    solver.add(mul(c, H(c)) == 1, H(mul(c, c)) == mul(c, c))
    result = solver.check()
    report = dict(prime=p, timeout_seconds=timeout, solver="Z3 QF_AUFBV",
                  result=str(result))
    if result == z3.sat:
        model = solver.model()
        hh = [model.eval(H(i)).as_long() for i in range(p)]
        dd = model.eval(d).as_long()
        assert verify(p, dd, hh)
        report["witness"] = dict(d=dd, h=hh)
    elif result == z3.unknown:
        report["reason"] = solver.reason_unknown()
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smt", type=int)
    parser.add_argument("--timeout", type=int, default=90)
    args = parser.parse_args()
    result = (smt(args.smt, args.timeout) if args.smt else
              {"status": "restricted-family exhaustion, not a spectrum exclusion",
               "shifted_power_searches": [powers(31), powers(47)]})
    print(json.dumps(result, indent=2, sort_keys=True))
