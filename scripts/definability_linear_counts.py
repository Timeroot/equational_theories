#!/usr/bin/env python3
"""Search for linear-model counting obstructions; never write proof facts.

For a finite ring R, more distinct linear source operations than linear target
operations obstruct finite term-structural definability. LinearCounting.lean
proves this by taking a product of distinct source models. This script discovers
small certificates; only separately checked Lean declarations settle cells.

The default search reads the current completely-open inventory. --all-open
searches every open finite term-structural class pair, including partially
resolved pairs. --pair lets one reproduce a settled certificate. All moduli are
tried, including composite ones:
the counting theorem needs a commutative ring, not a field.
"""

import argparse
import json
from functools import lru_cache
from pathlib import Path

import numpy as np

from spectrum_generate import load_equations, variables


ROOT = Path(__file__).resolve().parents[1]


def linear_models(equation, modulus):
    """Exactly the pairs (a,b) for which a*x+b*y satisfies the equation.

    Expanding at each variable's unit assignment is sufficient because the
    operation is linear. No elimination polynomial, field division, bounded
    term search, or solver unsatisfiability result is used.
    """
    if modulus < 2:
        raise ValueError('modulus must be at least 2')
    a = np.repeat(np.arange(modulus, dtype=np.int64), modulus)
    b = np.tile(np.arange(modulus, dtype=np.int64), modulus)
    lhs, rhs = equation

    @lru_cache(None)
    def coefficient(term, variable):
        if isinstance(term, str):
            return int(term == variable)
        return (a * coefficient(term[0], variable)
                + b * coefficient(term[1], variable)) % modulus

    good = np.ones(len(a), dtype=bool)
    for variable in variables(lhs) | variables(rhs):
        good &= coefficient(lhs, variable) == coefficient(rhs, variable)
    return [(int(x), int(y)) for x, y in zip(a[good], b[good])]


def find_obstructions(equations, pairs, max_modulus):
    """Yield the first counting certificate found for each requested pair."""
    remaining = set(map(tuple, pairs))
    for modulus in range(2, max_modulus + 1):
        ids = {i for pair in remaining for i in pair}
        models = {i: linear_models(equations[i - 1], modulus) for i in ids}
        for source, target in sorted(remaining):
            ns, nt = len(models[source]), len(models[target])
            if ns <= nt:
                continue
            # Only nt+1 distinct source factors are necessary.
            yield dict(source=source, target=target, modulus=modulus,
                       source_count=ns, target_count=nt,
                       factors=models[source][:nt + 1])
            remaining.remove((source, target))
        if not remaining:
            break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pair', type=int, nargs=2, action='append',
                        metavar=('SOURCE', 'TARGET'))
    parser.add_argument('--max-modulus', type=int, default=100)
    parser.add_argument('--all-open', action='store_true',
                        help='search all open termStructural/fin class pairs')
    args = parser.parse_args()
    if not 2 <= args.max_modulus <= 1000:
        parser.error('--max-modulus must be between 2 and 1000')
    equations = load_equations()
    if args.pair and args.all_open:
        parser.error('--pair and --all-open are mutually exclusive')
    snapshot = json.loads((ROOT / 'docs/definability_open/snapshot.json').read_text())
    if args.all_open:
        pairs = [(int(source), target)
                 for source, profiles in snapshot['boards']['termStructural/fin']['open_rows'].items()
                 for targets in profiles.values() for target in targets]
    else:
        pairs = args.pair or snapshot['completely_open']['pairs']
    if any(not 1 <= i <= len(equations) for pair in pairs for i in pair):
        parser.error('equation numbers must be between 1 and 4694')
    found = set()
    for result in find_obstructions(equations, pairs, args.max_modulus):
        found.add((result['source'], result['target']))
        print(json.dumps(result), flush=True)
    unresolved = sorted(set(map(tuple, pairs)) - found)
    print(f'{len(found)} candidate rows; {len(unresolved)} without a counting obstruction '
          f'through modulus {args.max_modulus}.')
    print('Not finding an obstruction is not evidence of definability. '
          'Candidates require separate Lean verification.')
    if unresolved:
        preview = unresolved[:30] if args.all_open else unresolved
        print('No obstruction found:', ', '.join(f'{s}→{t}' for s, t in preview),
              f'... ({len(unresolved)} total)' if len(preview) < len(unresolved) else '')


if __name__ == '__main__':
    main()
