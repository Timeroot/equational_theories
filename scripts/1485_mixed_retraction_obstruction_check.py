#!/usr/bin/env python3
"""Solver-free certificates for countable, NOT finite, E1485 countermodels.

See docs/1485_mixed_retraction_bands.md for the completion argument.
The four- and eight-vertex seeds are partial graphs, not operation tables.
"""

from itertools import product


M3 = [
    [{2}, {2}, {0}],
    [{2}, {1, 2}, {1}],
    [{0}, {1}, {0, 1}],
]
M5 = [
    [{1}, {2}, {0}, {2}, {1}],
    [{4}, {0}, {0}, {4}, {1}],
    [{1}, {1}, {3}, {3}, {1, 3}],
    [{4}, {2}, {3}, {2, 4}, {3}],
    [{0}, {0}, {0, 3}, {3}, {3}],
]


def certificate(middles, successors, predecessors):
    n = len(middles)
    good = {(a, b, c) for a, c in product(range(n), repeat=2)
            for b in middles[a][c]}
    edges = {(a, b) for a, b, c in good} | {(b, c) for a, b, c in good}
    assert all(middles[a][c] for a, c in product(range(n), repeat=2))
    assert all(((a, b, a) in good) == ((b, a, b) in good)
               for a, b in product(range(n), repeat=2))
    for a, b, c, d, e in product(range(n), repeat=5):
        if (a, b, c) in good and (c, d, e) in good and (e, a) in edges:
            assert (b, c, d) in good

    def sharp(a, b):
        return ((a, b) in edges
                and all((a, b, c) in good for c in range(n) if (b, c) in edges)
                and all((c, a, b) in good for c in range(n) if (c, a) in edges))

    assert all(sharp(a, successors[a]) for a in range(n))
    assert all(sharp(predecessors[a], a) for a in range(n))
    central = {b for b in range(n)
               if all((a, b, c) in good for a, c in product(range(n), repeat=2)
                      if (a, b) in edges and (b, c) in edges)}
    return good, central


def seed(certificate_data, colors, triples, central_vertices):
    good, central = certificate_data
    n = len(colors)
    edges = {(a, b) for a, b, c in triples} | {(b, c) for a, b, c in triples}
    assert all(tuple(colors[x] for x in triple) in good for triple in triples)
    assert all(colors[x] in central for x in central_vertices)
    for a, c in product(range(n), repeat=2):
        assert sum((a, b) in edges and (b, c) in edges
                   and (colors[a], colors[b], colors[c]) in good
                   for b in range(n)) <= 1
    operation = {(a, c): b for a, b, c in triples}
    assert len(operation) == len(set(triples))
    return lambda a, b: operation[a, b]


def main():
    c3 = certificate(M3, (2, 1, 0), (2, 1, 0))
    c5 = certificate(M5, (2, 4, 1, 2, 0), (4, 2, 0, 2, 1))

    # Global two-parameter band: u=0, v=1, a=2, c=3.
    f = seed(c5, [0, 1, 2, 4], [
        (2, 1, 0), (0, 2, 1), (1, 0, 2),
        (3, 0, 0), (0, 0, 2), (0, 1, 0),
        (2, 1, 1), (1, 0, 1), (1, 3, 0),
    ], (2, 3))
    lam = lambda a, b, x: f(f(a, x), f(x, b))
    assert lam(2, 1, 0) == 0
    assert lam(3, 2, 0) == 1
    assert lam(2, 1, 1) == 3 != 1

    # Parameter P=L_z R_z: A=0, x=1, k=2, z=3, b=4, t=5.
    f = seed(c5, [0, 1, 2, 3, 3, 4], [
        (2, 1, 1), (0, 1, 0), (2, 3, 2), (5, 0, 1),
        (1, 5, 0), (5, 4, 3), (3, 2, 4), (1, 0, 2),
    ], (2, 5))
    lam = lambda a, b, x: f(f(a, x), f(x, b))
    assert f(2, 2) == 3 and f(3, f(5, 3)) == 2
    assert lam(5, 2, 1) == 1
    assert lam(2, 2, 1) == 5 != 1

    # Period shrinkage: k=0,z=1,t=2,a=3,b=4,x=5.
    # T(t)=a, T(a)=b, T(b)=b: every power >=2 has the same obstruction.
    f = seed(c3, [2, 1, 2, 1, 1, 0], [
        (0, 1, 0), (2, 3, 1), (2, 5, 5), (3, 4, 1),
        (4, 2, 5), (4, 4, 1), (5, 2, 5), (5, 5, 0),
    ], (0, 2))
    lam = lambda a, b, x: f(f(a, x), f(x, b))
    assert f(0, 0) == 1
    t = 2
    for _ in range(10):
        t = f(t, 1)
    assert t == 4 and f(4, 1) == 4
    assert lam(t, 0, 5) == 5
    assert lam(2, 0, 5) == 2 != 5

    # Full meet, already on a 2-cycle: x,z,b,v,c,k,t,u = 0,...,7.
    f = seed(c3, [0, 1, 1, 1, 1, 2, 2, 2], [
        (5, 1, 5), (0, 7, 0), (3, 7, 0), (7, 0, 0),
        (4, 6, 1), (0, 0, 5), (6, 2, 7), (2, 3, 1), (6, 4, 1),
    ], (5, 6, 7))
    lam = lambda a, b, x: f(f(a, x), f(x, b))
    assert f(5, 5) == 1
    t = 6
    for _ in range(8):
        t = f(t, 1)
    assert t == 6
    v = f(f(t, 7), 1)
    assert v == 3 and lam(v, 5, 0) == 0
    assert lam(7, 5, 0) == 7 != 0

    # Short meet LEFT inclusion, with k=0,h=1 central.
    f = seed(c5, [2, 2, 4, 1, 3, 1, 4, 0, 0, 1, 4], [
        (0, 4, 0), (1, 5, 2), (5, 6, 4), (6, 7, 3),
        (3, 8, 0), (7, 3, 8), (1, 9, 3), (9, 10, 8),
    ], (0, 1))
    lam = lambda a, b, x: f(f(a, x), f(x, b))
    v = f(f(1, 2), f(0, 0))
    assert v == 6 and lam(v, 0, 3) == 3
    assert lam(1, 0, 3) == 10 != 3
    print("Both relaxed certificates, sharp choices, and all five seeds pass.")


if __name__ == "__main__":
    main()
