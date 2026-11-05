#!/usr/bin/env python3
"""Replay affine refutations of all 24 E917 compression candidates.

Compare coefficient vectors of the complete six-variable identity. This is a
research check, not a Lean proof. All placements in this family have counterexamples.
"""
import json
from pathlib import Path


def arithmetic(spec):
    if spec['kind'] == 'modular':
        n = spec['modulus']
        return n, lambda a, b: (a+b) % n, lambda a, b: a*b % n
    p, polynomial = spec['characteristic'], spec['polynomial']
    d = len(polynomial)-1
    assert polynomial[-1] == 1

    def digits(x):
        return [(x // p**i) % p for i in range(d)]

    def encode(coefficients):
        return sum((x % p)*p**i for i, x in enumerate(coefficients))

    def add(x, y):
        return encode([a+b for a, b in zip(digits(x), digits(y))])

    def mul(x, y):
        a, b = digits(x), digits(y)
        c = [sum(a[j]*b[i-j] for j in range(d) if 0 <= i-j < d)
             for i in range(2*d-1)]
        for i in range(2*d-2, d-1, -1):
            for j in range(d):
                c[i-d+j] -= c[i]*polynomial[j]
        return encode(c[:d])

    return p**d, add, mul


def check(spec, permutation):
    n, add, mul = arithmetic(spec)
    a, b, constant = (spec[k] for k in ('a', 'b', 'constant'))
    assert len({mul(a, x) for x in range(n)}) == n
    assert len({mul(b, x) for x in range(n)}) == n

    def m(left, right):
        out = [add(mul(a, x), mul(b, y)) for x, y in zip(left, right)]
        out[-1] = add(out[-1], constant)
        return out

    def c(x):
        return m(m(x, m(x, x)), x)

    def f(x, z):
        return m(z, m(c(x), m(x, z)))

    x, y, z, w, v, t = [[int(i == j) for i in range(7)] for j in range(6)]
    terms = {'x': x, 'U': m(x, c(x)),
             'B1': m(f(z, w), m(c(x), m(x, z))),
             'B2': m(v, m(c(x), m(x, f(v, t))))}
    A, B, C, D = (terms[name] for name in permutation)
    core = m(m(A, m(B, C)), D)
    assert m(y, m(core, m(x, y))) == x
    assert terms['U'] != x or f(x, y) != x
    return n


if __name__ == '__main__':
    path = (Path(__file__).resolve().parents[1] / 'data/parastrophes'
            / 'e917_double_compression_20261103.json')
    data = json.loads(path.read_text())
    for spec in data['countermodels']:
        i = spec['candidate']
        n = check(spec, data['permutations'][i])
        print(f'Candidate {i}: refuted at order {n}')
    print(f"Still unproved: {data['open_candidates']}")
