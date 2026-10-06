#!/usr/bin/env python3
"""Correlated partial groups: E1286 models of orders 240, 400, and 448.

Six full groups of order 32 and three half-groups of order 16. The latter
use the coordinates y, x, x+y in an affine transversal design. A binary
linear functional vanishes on either one or three of those coordinates,
so the restricted transversal blocks have sizes 7 and 9.

The related binary and septenary constructions give orders 400 and 448.
This reconstructs and checks all three models independently of the tail search.
No multiplication table needs to be saved in the repository.
"""
import gzip
import hashlib
import json
from pathlib import Path

from spectrum_effective_bound import polynomial_operations

ROOT = Path(__file__).resolve().parents[1]


def binary_multiply(a, b, modulus=37):
    degree = modulus.bit_length()-1
    value = 0
    while b:
        if b & 1:
            value ^= a
        b >>= 1
        a <<= 1
        if a >> degree:
            a ^= modulus
    return value


def algebraic_table(certificate, n, idempotent=False):
    for p, modulus, left, right, idem in certificate['extensions']:
        if p**(len(modulus)-1) != n or (idempotent and not idem):
            continue
        reduce, add, mul = polynomial_operations(p, modulus)
        def digits(x):
            out = []
            while x:
                out.append(x % p)
                x //= p
            return tuple(out)
        def index(xs):
            return sum(x*p**i for i, x in enumerate(xs))
        a, b = reduce(left), reduce(right)
        return [[index(add(mul(a, digits(x)), mul(b, digits(y))))
                 for y in range(n)] for x in range(n)]
    for size, a, b, idem in certificate['scalars']:
        if size == n and (not idempotent or idem):
            return [[(a*x+b*y) % n for y in range(n)] for x in range(n)]
    raise ValueError(f'Missing algebraic model of order {n}')


def construct(certificate, dimension=2, low=7, nonzero=False):
    """A concrete member of the binary-simplex construction over F32."""
    half = 1 << (dimension-1)
    partial = 2*half-1
    high = low+half
    full = low if nonzero else low-half+1
    order = 32*full+16*partial
    assert full >= 0 and full+partial <= 33
    tables = {n: algebraic_table(certificate, n, n in (low, high, 16))
              for n in (low, high, 16, 32)}
    for n, t in tables.items():
        assert t[0][0] == 0
        assert all(t[y][t[t[t[x][y]][x]][y]] == x
                   for x in range(n) for y in range(n))
    # The first partial directions are u=1,...,2^dimension-1. The other
    # directions, including the vertical one, give the full groups.
    directions = list(range(1, partial+1))+([None, 0]+list(range(partial+1, 32)))[:full]
    def keep(i, x):
        return i >= partial or binary_multiply(i+1, x) % 2 == int(nonzero)
    groups = [[(i, x) for x in range(32) if keep(i, x)] for i in range(len(directions))]
    points = sum(groups, [])
    lookup = {p: i for i, p in enumerate(points)}
    table = [[None]*order for _ in points]
    for group in groups:
        t = tables[len(group)]
        for i, a in enumerate(group):
            for j, b in enumerate(group):
                table[lookup[a]][lookup[b]] = lookup[group[t[i][j]]]
    counts = {low: 0, high: 0}
    for x in range(32):
        for y in range(32):
            coordinates = [y if c is None else x ^ binary_multiply(c, y) for c in directions]
            block = [(i, z) for i, z in enumerate(coordinates) if keep(i, z)]
            counts[len(block)] += 1
            t = tables[len(block)]
            for i, a in enumerate(block):
                for j, b in enumerate(block):
                    if i != j:
                        assert table[lookup[a]][lookup[b]] is None
                        table[lookup[a]][lookup[b]] = lookup[block[t[i][j]]]
    assert all(z is not None for row in table for z in row)
    assert table[0][0] == 0
    assert all(table[y][table[table[table[x][y]][x]][y]] == x
               for x in range(order) for y in range(order))
    return table, counts


def construct448(certificate):
    """Eight full and eight one-seventh groups over F49, blocks 9 or 16.

Choose one u from each projective point of F7^2. The eight slopes u^6
are distinct. The conditions constant(u*x+u^7*y)=0 hold in either one
or eight of those directions, since they are the kernel of a linear form.
    """
    def add(x, y):
        return (x % 7+y % 7) % 7+7*((x//7+y//7) % 7)
    def mul(x, y):
        a, b, c, d = x % 7, x//7, y % 7, y//7
        return (a*c-b*d) % 7+7*((a*d+b*c) % 7)
    def power(x, n):
        out = 1
        for _ in range(n):
            out = mul(out, x)
        return out
    representatives = [1]+[7+i for i in range(7)]
    partial_slopes = [power(u, 6) for u in representatives]
    assert len(set(partial_slopes)) == 8
    directions = partial_slopes+([None]+[s for s in range(49) if s not in partial_slopes])[:8]
    def keep(i, x):
        return i >= 8 or mul(representatives[i], x) % 7 == 0
    groups = [[(i, x) for x in range(49) if keep(i, x)] for i in range(16)]
    points = sum(groups, [])
    lookup = {p: i for i, p in enumerate(points)}
    tables = {n: algebraic_table(certificate, n, True) for n in (7, 9, 16)}
    tables[49] = [[tables[7][x % 7][y % 7]+7*tables[7][x//7][y//7]
                   for y in range(49)] for x in range(49)]
    table = [[None]*448 for _ in points]
    for group in groups:
        t = tables[len(group)]
        for i, a in enumerate(group):
            for j, b in enumerate(group):
                table[lookup[a]][lookup[b]] = lookup[group[t[i][j]]]
    counts = {9: 0, 16: 0}
    for x in range(49):
        for y in range(49):
            coordinates = [y if c is None else add(x, mul(c, y)) for c in directions]
            block = [(i, z) for i, z in enumerate(coordinates) if keep(i, z)]
            counts[len(block)] += 1
            t = tables[len(block)]
            for i, a in enumerate(block):
                for j, b in enumerate(block):
                    if i != j:
                        assert table[lookup[a]][lookup[b]] is None
                        table[lookup[a]][lookup[b]] = lookup[block[t[i][j]]]
    assert all(z is not None for row in table for z in row)
    assert all(table[x][x] == x for x in range(448))
    # This idempotent model satisfies both laws, as do its component models.
    assert all(table[y][table[table[table[x][y]][x]][y]] == x
               and table[y][table[table[x][table[y][x]]][y]] == x
               for x in range(448) for y in range(448))
    return table, counts


def main():
    cert = json.load(gzip.open(ROOT/'data/spectrum/e1286_effective_tail.json.gz'))
    results = []
    for dimension, low, nonzero in [(2, 7, False), (3, 9, True)]:
        table, counts = construct(cert, dimension, low, nonzero)
        order = len(table)
        encoded = b''.join(z.to_bytes(2, 'little') for row in table for z in row)
        results.append(dict(law=1286, order=order, pointed=True,
                            construction='binary simplex half-groups', degree=5, modulus=37,
                            dimension=dimension, low_block=low, nonzero=nonzero,
                            block_counts=counts, checked_pairs=order**2,
                            table_sha256=hashlib.sha256(encoded).hexdigest()))
    table, counts = construct448(cert)
    encoded = b''.join(z.to_bytes(2, 'little') for row in table for z in row)
    results.append(dict(laws=[1083, 1286], order=448, idempotent=True,
                        construction='projective seventh-groups', prime=7,
                        dimension=2, low_block=9, nonzero=False,
                        block_counts=counts, checked_pairs=448**2,
                        table_sha256=hashlib.sha256(encoded).hexdigest()))
    for result in results:
        result['existence_status'] = 'PROVED' if result['order'] == 240 else 'PROVED_UNFORMALIZED'
        if result['order'] == 240:
            result['lean_existence'] = {
                'file': 'equational_theories/Spectrum/Equation1083_1286/BinaryHalves.lean',
                'declaration': 'Spectrum.E1083E1286.BinaryHalves.model240',
            }
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
