#!/usr/bin/env python3
"""Independently check the three twisted term-recovery certificates.

This evaluates the full source and target laws on the explicit finite carriers,
and checks the interpolation identity that proves closure of the parameter
family. It uses no private model bank, bounded clone search, or solver output.
Only the separately compiled TwistedRecovery.lean declarations seed the board.
"""

from itertools import product

import numpy as np

from spectrum_generate import load_equations, variables


# source, target, p, q, base coefficient, fiber coefficient, twist at x-y
CERTIFICATES = (
    (1516, 1489, 5, 7, 3, 6, (0, 1, 1, 1, 1)),
    (1076, 1313, 5, 13, 4, 7, (0, 1, -1, -1, 1)),
    (1685, 3548, 7, 5, 2, 3, (0, 1, 1, -1, 1, -1, -1)),
)


def table(p, q, character, a, b, c):
    """Encode (x,u) as q*x+u, and return the complete operation table."""
    base = np.repeat(np.arange(p), q)
    fiber = np.tile(np.arange(q), p)
    twist = np.asarray(character)[(base[:, None] - base[None, :]) % p]
    return (q * ((a * base[:, None] + (1 - a) * base[None, :]) % p)
            + (b * fiber[:, None] + (1 - b) * fiber[None, :] + c * twist) % q)


def satisfies(equation, operation):
    """Evaluate both terms at every assignment, without coefficient shortcuts."""
    lhs, rhs = equation
    names = sorted(variables(lhs) | variables(rhs))
    assignments = np.indices((len(operation),) * len(names)).reshape(len(names), -1)
    environment = dict(zip(names, assignments))

    def evaluate(term):
        if isinstance(term, str):
            return environment[term]
        return operation[evaluate(term[0]), evaluate(term[1])]

    return bool(np.all(evaluate(lhs) == evaluate(rhs)))


def verify(certificate, equations):
    source, target, p, q, A, B, character = certificate

    def twist(x, y):
        return character[(x - y) % p] % q

    for a, aa, x, y in product(range(p), repeat=4):
        left = twist((a * x + (1 - a) * y) % p,
                     (aa * x + (1 - aa) * y) % p)
        if left != twist(a, aa) * twist(x, y) % q:
            raise AssertionError('The family does not have the claimed interpolation identity')

    operation = table(p, q, character, A, B, 1)
    if not satisfies(equations[source - 1], operation):
        raise AssertionError(f'The source does not satisfy E{source}')
    if not np.any(operation[::q, ::q] % q):
        raise AssertionError('The source preserves the zero section')

    targets = []
    for a, b, c in product(range(p), range(q), range(q)):
        companion = table(p, q, character, a, b, c)
        if satisfies(equations[target - 1], companion):
            if c != 0 or np.any(companion[::q, ::q] % q):
                raise AssertionError('A target companion retains a nonzero twist')
            targets.append((a, b, c))
    return targets


def main():
    equations = load_equations()
    for certificate in CERTIFICATES:
        source, target, p, q, *_ = certificate
        targets = verify(certificate, equations)
        print(f'{source} → {target}: order {p*q}; {p*q*q} family members; '
              f'target parameters {targets}; all erase the twist.')
    print('All three checks passed. Board facts require the Lean proofs.')


if __name__ == '__main__':
    main()
