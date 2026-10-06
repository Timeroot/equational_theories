#!/usr/bin/env python3
"""Exhaust regular-action E667 constructions over groups of order 20 or 24.

All square values are covered up to inner automorphism. The group lists are
the standard complete classifications at these orders; the mathematical
coverage argument is documented in docs/e667_open_orders_20261004.md.
UNSAT results here are external computations, not Lean exclusions.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path

from spectrum_667_regular import group, validate_group
from spectrum_667_regular_sat import solve

GROUPS = {
    20: ['C20', 'C5xC2xC2', 'D20', 'Dic20', 'F20'],
    24: ['S4', 'SL2F3', 'A4xC2', 'C24', 'C12xC2', 'C3xC2xC2xC2',
         'D8xC3', 'Q8xC3', 'C3rtC8', 'Dic12xC2', 'D6xC4', 'D6xC2xC2',
         'D24', 'C3rtD8', 'Dic24'],
}


def coverage(name):
    g = group(name)
    inv = validate_group(g)
    n = len(g)
    seen, reps, classes = set(), [], []
    for d in range(n):
        if d in seen:
            continue
        cl = sorted({g[g[x][d]][inv[x]] for x in range(n)})
        assert not seen.intersection(cl)
        seen.update(cl)
        reps.append(d)
        classes.append(cl)
    assert len(seen) == n
    orders = []
    for x in range(n):
        y, k = x, 1
        while y:
            y, k = g[y][x], k+1
        orders.append(k)
    center = [x for x in range(n) if all(g[x][y] == g[y][x] for y in range(n))]
    commutators = {g[g[g[x][y]][inv[x]]][inv[y]] for x in range(n) for y in range(n)}
    derived = {0}
    while True:
        new = derived | {g[x][y] for x in derived for y in commutators}
        if new == derived:
            break
        derived = new
    invariants = dict(element_orders=dict(sorted(Counter(orders).items())),
                      center_order=len(center), derived_order=len(derived))
    return dict(representatives=reps, conjugacy_classes=classes, invariants=invariants)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('order', type=int, choices=sorted(GROUPS))
    p.add_argument('--seconds', type=int, default=30)
    p.add_argument('--workers', type=int, default=4)
    p.add_argument('--workdir', type=Path, required=True)
    a = p.parse_args()
    a.workdir.mkdir(parents=True, exist_ok=True)
    cov = {g: coverage(g) for g in GROUPS[a.order]}
    # These elementary invariants distinguish every listed group.
    assert len({json.dumps(c['invariants'], sort_keys=True) for c in cov.values()}) == len(cov)
    (a.workdir/'coverage.json').write_text(json.dumps(cov, indent=2)+'\n')
    jobs = [(g,d) for g,c in cov.items() for d in c['representatives']]
    print(f'{len(cov)} groups, {len(jobs)} square-value cases', flush=True)
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        fs = [pool.submit(solve,g,a.seconds,a.workdir,d) for g,d in jobs]
        for f in as_completed(fs):
            print(f.result(), flush=True)
