#!/usr/bin/env python3
"""Generate the five strengthened E667 order-twelve row searches.

The additional conditions are proved in Equation667Twelve/RowReduction.lean:
repeated square values are idempotent, and rows 37/39 minimize entry (1,2)
under relabellings fixing zero and commuting with the prescribed first row.
No assertion that the square map is a homomorphism is used.

By default, write sanitized DIMACS. --solve also captures CaDiCaL LRAT traces.
Trim and compact the traces with the usual spectrum certificate tools, export
RowReduction.natFormula from Lean, then use the collision certificate script's
--improve option to check the clause match and install the smaller data.
"""
import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path

from spectrum_667_incremental import clauses, partitions
from spectrum_667_fixed_square import permutation

N = 12
INDICES = (37, 38, 39, 40, 41)


def atom(x, y, z):
    return 1 + (x*N+y)*N+z


def centralizer(lengths):
    """All nonidentity permutations commuting with the row and fixing zero."""
    groups = {}
    start = 0
    for size in lengths:
        groups.setdefault(size, []).append(list(range(start, start+size)))
        start += size
    choices = []
    for size, cycles in groups.items():
        group = []
        for targets in itertools.permutations(cycles):
            for shifts in itertools.product(range(size), repeat=len(cycles)):
                pairs = [(a, target[(j+shift) % size])
                         for source, target, shift in zip(cycles, targets, shifts)
                         for j, a in enumerate(source)]
                if any(a == 0 and b != 0 for a, b in pairs):
                    continue
                group.append(pairs)
        choices.append(group)
    for bundle in itertools.product(*choices):
        move = list(range(N))
        for block in bundle:
            for a, b in block:
                move[a] = b
        if move != list(range(N)):
            yield move


def formula(index):
    lengths = list(partitions(N))[index]
    row = permutation(lengths)
    result = clauses(N, 'one-idempotent')
    result += [[atom(0, y, z)] for y, z in enumerate(row)]
    if index in (37, 39):
        for move in centralizer(lengths):
            inverse = [move.index(x) for x in range(N)]
            for z, w in itertools.product(range(N), repeat=2):
                if z > move[w]:
                    result.append([-atom(1, 2, z), -atom(inverse[1], inverse[2], w)])
    result += [[-atom(a, a, c), -atom(b, b, c), atom(c, c, c)]
               for a in range(N) for b in range(a+1, N) for c in range(N)]
    return [sorted(set(c)) for c in result if not any(-v in c for v in c)]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('work', type=Path)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--timeout', type=int, default=180)
    args = ap.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    for index in INDICES:
        mode = 'min-fibers' if index in (37, 39) else 'fibers'
        stem = args.work / f'row{index:03d}-{mode}'
        cnf = formula(index)
        with stem.with_suffix('.cnf').open('w') as out:
            out.write(f'p cnf {2*N**3} {len(cnf)}\n')
            out.writelines(' '.join(map(str, c)) + ' 0\n' for c in cnf)
        print(f'{stem}: {len(cnf)} clauses', flush=True)
        if args.solve:
            start = time.monotonic()
            cmd = ['cadical', '--lrat', '--no-binary', '--shrink=0',
                   '-t', str(args.timeout), str(stem.with_suffix('.cnf')),
                   str(stem.with_suffix('.lrat'))]
            result = subprocess.run(cmd, capture_output=True, text=True)
            stem.with_suffix('.log').write_text(result.stdout + result.stderr)
            status = {10: 'SAT', 20: 'UNSAT'}.get(result.returncode, 'UNKNOWN')
            record = dict(index=index, mode=mode, command=cmd, status=status,
                          seconds=time.monotonic()-start)
            stem.with_suffix('.json').write_text(json.dumps(record, indent=2)+'\n')
            print(record, flush=True)


if __name__ == '__main__':
    main()
