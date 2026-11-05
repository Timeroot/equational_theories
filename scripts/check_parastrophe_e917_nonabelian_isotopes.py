#!/usr/bin/env python3
"""Replay the exhaustive D8/Q8 isotope check for the E917 candidate.

This is bounded Python research, not a Lean proof. Every group isotope is
isomorphic to x*y=alpha(x).beta(y). Replacing alpha(x) by alpha(x).alpha(1)^-1
and beta(y) by alpha(1).beta(y) preserves the table and normalizes alpha(1)=1.
Conjugating both permutations by a group automorphism preserves its isomorphism
class; we can therefore normalize beta(1) to one representative of each orbit.
The reduced candidate criterion is formalized in Equation917PowerComparison.lean.
Run from the repository root. Requires NumPy; takes about three minutes.
"""
import itertools
import json
from pathlib import Path
import numpy as np
from check_parastrophe_e917_group_isotopes import filter_models, groups


def quaternion_group():
    """Units 1,i,j,k, with each positive unit followed by its negative."""
    units = [[0, 1, 2, 3], [1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]]
    signs = [[0, 0, 0, 0], [0, 1, 0, 1], [0, 1, 1, 0], [0, 0, 1, 1]]
    return np.array([
        [2 * units[a // 2][b // 2] + (a % 2 + b % 2 + signs[a // 2][b // 2]) % 2
         for b in range(8)] for a in range(8)
    ])


def check(name, table):
    n = len(table)
    points = np.arange(n)
    assert np.all(table[table[:, :, None], points] == table[points[:, None, None], table[None, :, :]])
    assert np.array_equal(table[0], points) and np.array_equal(table[:, 0], points)
    assert all(np.array_equal(np.sort(row), points) for row in table)
    alphas = np.array([(0,) + p for p in itertools.permutations(range(1, n))])
    automorphisms = [p for p in alphas if np.array_equal(p[table], table[p[:, None], p[None, :]])]
    representatives, seen = [], set()
    for i in range(n):
        if i not in seen:
            representatives.append(i)
            seen.update(int(p[i]) for p in automorphisms)
    betas = np.array([p for p in itertools.permutations(range(n)) if p[0] in representatives])
    total, frames = len(alphas) * len(betas), 0
    for lo in range(0, total, 2048):
        ids = np.arange(lo, min(lo + 2048, total))
        aa, bb = ids // len(betas), ids % len(betas)
        magmas = table[alphas[aa, :, None], betas[bb, None, :]]
        found, count = filter_models(magmas)
        assert not found, f"Unexpected counterexample: {name}, batch {lo}, {found}"
        frames += count
    return dict(group=name, automorphisms=len(automorphisms),
                beta_zero_representatives=representatives, pairs=total,
                pre_frames=frames, counterexamples=[], exhaustive_up_to_isomorphism=True)


def main():
    dihedral = next(table for name, table, _ in groups() if name == 'D8')
    records = []
    for name, table in [('D8', dihedral), ('Q8', quaternion_group())]:
        records.append(check(name, table))
        print(json.dumps(records[-1]), flush=True)
    path = Path('data/parastrophes/e917_nonabelian_isotopes_20261104.json')
    assert records == json.loads(path.read_text())['records'], 'Saved research counts differ'


if __name__ == '__main__':
    main()
