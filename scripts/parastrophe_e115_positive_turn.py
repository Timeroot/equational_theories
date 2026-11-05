#!/usr/bin/env python3
"""Construct a finite E115 right image refuting a proposed inverse-core term.

This implements the positive-height argument in docs/e115-finite-right-image.md.
It stores finitely many triangle trades, never an enormous multiplication
table. The image obstruction is formalized in Lean; the reverse-recovery
corollary illustrated here is documented separately as a paper consequence.
"""
import itertools
import json
from pathlib import Path


def vector(xs):
    xs = list(xs)
    while xs and xs[-1] == 0:
        xs.pop()
    return tuple(xs)


def add(x, y):
    return vector(a + b for a, b in itertools.zip_longest(x, y, fillvalue=0))


def neg(x):
    return vector(-a for a in x)


def sub(x, y):
    return add(x, neg(y))


def height(x):
    return x[0] if x else 0


class PartialTurn:
    def __init__(self):
        self.cycles = []
        self.turn = {}
        self.fresh = 1
        self.add_cycle((), (-6,), (3,))

    def add_cycle(self, x, y, z):
        assert len({x, y, z}) == 3
        assert not any(a in self.turn for a in (x, y, z))
        assert add(add(x, y), z) == (-3,)
        for a, b in ((x, y), (y, z), (z, x)):
            assert height(a) % 3 == 0
            assert height(b) <= max(0, -height(a))
            self.turn[a] = b
        self.cycles.append((x, y, z))

    def query(self, x):
        if x not in self.turn:
            assert len(x) <= self.fresh
            h = height(x)
            b = [0] * (self.fresh + 1)
            b[0] = 0 if h >= 0 else -3 - h
            b[self.fresh] = 1
            self.fresh += 1
            b = vector(b)
            self.add_cycle(x, b, sub(sub((-3,), x), b))
        return self.turn[x]

    def evaluate(self, term):
        if isinstance(term, int):
            return ()
        x, y = map(self.evaluate, term)
        result = sub(y, self.query(sub(x, y)))
        assert height(result) >= min(height(x), height(y)) >= 0
        return result


def finite_witness(term):
    partial = PartialTurn()
    integer_value = partial.evaluate(term)
    # Reverse each partial t-cycle: the source uses A=t², while right
    # division uses t. Translating by v=e₀ makes each cycle sum to zero.
    triples = [[add(x, (1,)) for x in (a, c, b)]
               for a, b, c in partial.cycles]
    bound = max([3, height(integer_value) + 3] +
                [abs(a) for triple in triples for x in triple for a in x])
    modulus = 2 * bound + 1
    dimension = partial.fresh

    def reduce(x):
        return tuple((x[i] if i < len(x) else 0) % modulus for i in range(dimension))

    zero = (0,) * dimension
    v = reduce((1,)) + zero
    initial = zero + zero

    def plus(x, y):
        return tuple((a + b) % modulus for a, b in zip(x, y))

    def minus(x, y):
        return tuple((a - b) % modulus for a, b in zip(x, y))

    def rotation(x):
        a, b = x[:dimension], x[dimension:]
        return tuple(-t % modulus for t in b) + minus(a, b)

    replacements = {}
    for triple in triples:
        xs = [reduce(x) + zero for x in triple]
        for _ in range(3):
            assert not any(x in replacements for x in xs)
            assert plus(plus(xs[0], xs[1]), xs[2]) == initial
            for i in range(3):
                replacements[xs[i]] = xs[(i + 1) % 3]
            xs = list(map(rotation, xs))
    assert set(replacements) == set(replacements.values())

    def turn(x):
        return replacements.get(x, rotation(x))

    def A(x):
        return minus(turn(plus(x, v)), v)

    def D(x, y):
        return minus(y, A(A(minus(x, y))))

    def evaluate(t):
        return initial if isinstance(t, int) else D(evaluate(t[0]), evaluate(t[1]))

    # Check the prescribed partial calculations against the completed turn.
    # The off-trade rotation has period three and zero triangle sum; the
    # finite replacement set consists of whole rotation orbits.
    for x in replacements:
        assert turn(turn(turn(x))) == x
        assert plus(plus(x, turn(x)), turn(turn(x))) == initial
    for x, tx in partial.turn.items():
        assert A(A(reduce(x) + zero)) == reduce(tx) + zero
    assert A(initial) == reduce((3,)) + zero
    value = evaluate(term)
    assert value == reduce(integer_value) + zero
    core = D(value, D(value, value))
    assert core == plus(value, reduce((3,)) + zero)
    assert core != initial
    return {
        'term': term,
        'cycles': [[list(x) for x in cycle] for cycle in partial.cycles],
        'integer_value': list(integer_value),
        'modulus': modulus,
        'dimension': dimension,
        'carrier_order': f'{modulus}^{2 * dimension}',
        'trade_points': len(replacements),
    }


def main():
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root / 'data/parastrophes/image_candidate_refutations_20261103.json').read_text())
    terms = [0, [0, 0], *[r['term'] for r in data['records']
                          if r['source'] == 115 and r['test'] == 'inverse_square']]
    for term in terms:
        witness = finite_witness(term)
        print({k: witness[k] for k in ['carrier_order', 'trade_points', 'integer_value']})


if __name__ == '__main__':
    main()
