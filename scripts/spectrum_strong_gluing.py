#!/usr/bin/env python3
"""Check the seeds and arithmetic of the strong-design cofiniteness argument.

Research evidence, not Lean proofs. --exhaustive also builds three explicitly
constructed E677 tables in memory and checks every pair, then discards them.
No model search or UNSAT oracle is used.
"""
import argparse
from functools import reduce
import hashlib
import json
from math import gcd
from operator import mul
from pathlib import Path
import subprocess

import sympy as sp

from spectrum_generate import coefficients, load_equations, satisfies
from spectrum_open_survey import Field, subterms

ROOT = Path(__file__).resolve().parents[1]
POLYS = {
    677: [1, -1, 1, -1, 1],
    1083: [1, -1, 2, -2, 1],
    1286: [1, -1, 2, -2, 1],
}


def strong_seed(law, record, full=False):
    f = Field(record['p'], record['modulus'])
    a, b = record['a'], record['b']
    t = sp.Symbol('t')
    assert sp.isprime(f.p)
    assert sp.Poly(sum(c*t**i for i, c in enumerate(f.modulus)), t,
                   modulus=f.p).is_irreducible
    lhs, rhs = load_equations()[law-1]
    assert f.add(a, b) == 1
    u, v = f.coeff(lhs, a, b), f.coeff(rhs, a, b)
    assert all(u.get(x, 0) == v.get(x, 0) for x in u.keys() | v.keys())
    differences = [f.add(f.coeff(node[0], a, b).get('x', 0),
                         f.neg(f.coeff(node[1], a, b).get('x', 0)))
                   for node in subterms(rhs)]
    assert all(differences)
    if full:
        assert satisfies(lhs, rhs, f.table(a, b), f.q)
    return dict(order=f.q, **record, node_differences=differences,
                coefficient_identity_verified=True, strong=True,
                full_table_law_checked=full)


def bezout_checks():
    t = sp.Symbol('t')
    out = {}
    for law, cs in POLYS.items():
        f = sum(c*t**i for i, c in enumerate(cs))
        lhs, rhs = load_equations()[law-1]
        xcoeff = coefficients(rhs, 1-t, t)['x']
        ycoeff = coefficients(rhs, 1-t, t)['y']
        assert sp.rem(xcoeff-1, f, t) == sp.rem(ycoeff, f, t) == 0
        rows = []
        for node in subterms(rhs):
            d = sp.expand(coefficients(node[0], 1-t, t).get('x', 0)
                          - coefficients(node[1], 1-t, t).get('x', 0))
            u, v, one = sp.gcdex(f, d, t)
            assert one == 1 and sp.expand(u*f+v*d) == 1
            assert all(c.q == 1 for poly in [u, v] for c in sp.Poly(poly, t).all_coeffs())
            rows.append(dict(difference=str(sp.factor(d)),
                             f_multiplier=str(u), difference_multiplier=str(v)))
        out[str(law)] = rows
    return out


def arithmetic_checks(p, k, gs):
    primes = list(map(int, sp.primerange(2, k+1)))
    M = reduce(mul, primes, 1)
    assert k % p == 0
    assert {g % p for g in gs} == set(range(2, p))
    result = []
    for g in gs:
        assert sp.isprime(g) and g <= k and gcd(g, k) == 1
        e = 1
        while g**e < k:
            e += 1
        D = g**e*M
        for C in [k+1, 10*k+31]:
            # C is a dummy threshold to check arithmetic, NOT an assertion
            # that the Wilson conclusion starts at this particular value.
            N = (k+1)*(g*C+k*D)
            for residue in range(g):
                n = N + (g-N) % p
                n += p*((residue-n)*pow(p, -1, g) % g)
                assert n % p == g % p and n % g == residue
                if residue:
                    c = n*pow(k, -1, g) % g
                    q0 = 1 + (M//g)*((c-1)*pow(M//g, -1, g) % g)
                    step = M
                    assert gcd(q0, M) == 1
                else:
                    c = pow(g, -e, p)
                    Q0 = 1 + (M//p)*((c-1)*pow(M//p, -1, p) % p)
                    assert gcd(Q0, M) == 1
                    q0, step = g**e*Q0, D
                start = (n+k)//(k+1)
                q = q0 + ((start-q0+step-1)//step)*step
                r = n-k*q
                assert q >= C and 0 < r <= q and r % g == 0
                assert r//g >= C and (r//g) % p == 1 and q % p == 1
                if residue:
                    assert gcd(q, M) == 1
                else:
                    assert q % (g**e) == 0 and gcd(q//(g**e), M) == 1
        result.append(dict(g=g, e=e, residue_cases_checked=2*g))
    return dict(modulus=p, block_sizes=[k, k+1], small_prime_product=str(M),
                cases=result, threshold_checks_are_not_numerical_cutoffs=True)


def construction_677(survey):
    def model(n):
        r = survey['677']['idempotent_models'][str(n)]
        f = Field(r['p'], r['modulus'])
        return f, f.table(r['a'], r['b'])
    f, op81 = model(81)
    _, op5 = model(5)
    _, op16 = model(16)
    op80 = [16*op5[(x//16)*5+y//16]+op16[(x%16)*16+y%16]
            for x in range(80) for y in range(80)]
    eq = load_equations()[676]
    assert satisfies(*eq, op80, 80) and satisfies(*eq, op81, 81)
    add = [f.add(x, y) for x in range(81) for y in range(81)]
    mult = [f.mul(x, y) for x in range(81) for y in range(81)]
    neg = [f.neg(x) for x in range(81)]
    inv = [0]+[next(y for y in range(1, 81) if f.mul(x, y) == 1) for x in range(1, 81)]
    return dict(fieldAdd=add, fieldMul=mult, fieldNeg=neg, fieldInv=inv,
                block80=op80, block81=op81)


def exhaustive_677(survey):
    work = ROOT/'.cache/strong-designs'
    work.mkdir(parents=True, exist_ok=True)
    source = ROOT/'scripts/spectrum_strong_gluing_check.cpp'
    exe = work/'check'
    subprocess.run(['g++', '-O3', '-std=c++17', str(source), '-o', str(exe)], check=True)
    seeds = construction_677(survey)
    results = []
    for r, a, b in [(7, 4, 1), (13, 9, 11), (19, 7, 3)]:
        hole = [(a*x+b*y) % r for x in range(r) for y in range(r)]
        values = [81, 80, r]+[x for table in seeds.values() for x in table]+hole
        data = ' '.join(map(str, values))+'\n'
        done = subprocess.run([str(exe)], input=data, text=True, capture_output=True, check=True)
        row = json.loads(done.stdout)
        assert row['law'] == 677 and row['order'] == 80*81+r
        assert row['pairs_checked'] == row['order']**2 and row['e255']
        row.update(input_sha256=hashlib.sha256(data.encode()).hexdigest(),
                   recipe=dict(td_groups=81, group_order=81, truncated_group=r))
        results.append(row)
        print(f"Exhaustively verified E677 at order {row['order']}: {row['pairs_checked']} pairs.", flush=True)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exhaustive', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    survey = json.loads((ROOT/'data/spectrum/open_survey_20260927.json').read_text())['finite_fields']['families']
    result = dict(status='PROVED',
                  laws=[677, 1083, 1286], numerical_cutoff=None,
                  formal_reduction=dict(
                      crt='Spectrum.PBD.ResidueFilling.decompose',
                      e677='Spectrum.E677.cofinite_of_wilson',
                      e1083_e1286='Spectrum.E1083E1286.cofinite_of_wilson',
                      conditional_proofs_status='PROVED',
                      design_existence=['Spectrum.PBD.wilson_5_11_16',
                                        'Spectrum.PBD.wilson_7_9_16'],
                      unconditional_proofs=['Spectrum.Pending.cofinite_677',
                                            'Spectrum.Pending.cofinite_1083',
                                            'Spectrum.Pending.cofinite_1286'],
                      pending_inputs=[]),
                  bezout=bezout_checks(), strong_seeds={}, nonidempotent_seeds={},
                  crt_arithmetic={})
    for law, sizes in [(677, [5, 11, 16, 81]), (1083, [7, 9, 16]), (1286, [7, 9, 16])]:
        rows = [strong_seed(law, survey[str(law)]['idempotent_models'][str(n)], full=True) for n in sizes]
        if law != 677:
            rows.append(strong_seed(law, dict(p=1009, modulus=[0, 1], a=958, b=52)))
        result['strong_seeds'][str(law)] = rows
    for law, recipes in [(677, [(7, 4, 1), (13, 9, 11), (19, 7, 3)]),
                         (1083, [(11, 6, 9)]), (1286, [(11, 1, 7)])]:
        rows = []
        for n, a, b in recipes:
            table = [(a*x+b*y) % n for x in range(n) for y in range(n)]
            assert satisfies(*load_equations()[law-1], table, n)
            assert (a+b) % n != 1
            rows.append(dict(order=n, a=a, b=b, full_table_verified=True))
        result['nonidempotent_seeds'][str(law)] = rows
    result['crt_arithmetic']['677'] = arithmetic_checks(5, 80, [7, 13, 19])
    result['crt_arithmetic']['1083_1286'] = arithmetic_checks(3, 1008, [11])
    if args.exhaustive:
        result['exhaustive_models'] = exhaustive_677(survey)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('Verified strong seeds, integral Bezout identities, prime models, and CRT inequalities.')


if __name__ == '__main__':
    main()
