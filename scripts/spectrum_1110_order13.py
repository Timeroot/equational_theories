#!/usr/bin/env python3
"""Reproduce the original E1110 order-13 search, split by squaring cycles.

The square permutation has no 2-cycles (Equation1110/Diagonal.lean).
Conjugating it gives 44 nonidentity cycle types; the identity branch uses
already proved first-row normalization. The final two types also sort the
images of the nontrivial cycle in row zero, by freely relabelling fixed points.
Only a solver's exhaustive UNSAT result counts as a refutation, never a timeout.
The final, more efficient Lean-certified construction is reproduced by
spectrum_1110_thirteen.py; this file preserves the initial search experiment.
"""
import argparse
from pathlib import Path
import subprocess
import time
import json
from spectrum_small_orders import clauses, variables

ROOT = Path(__file__).resolve().parents[1]


def partitions(n, least=1):
    if n == 0:
        yield []
    for k in range(least, n + 1):
        if k != 2:
            for tail in partitions(n - k, k):
                yield [k] + tail


def cycles(n=13):
    return [sorted(p, key=lambda k: (k == 1, k))
            for p in partitions(n) if p != [1] * n]


def permutation(parts):
    result = []
    for k in parts:
        start = len(result)
        result.extend(list(range(start + 1, start + k)) + [start])
    return result


def fixed_clauses(parts, stabilize=False):
    n = sum(parts)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    old_chain = {-p(0, y, z) for y in range(n) for z in range(y + 2, n)}
    cs = [c for c in clauses(1110, n)
          if not (len(c) == 1 and c[0] in old_chain)]
    cs += [[p(x, x, y)] for x, y in enumerate(permutation(parts))]
    if stabilize:
        k = parts[0]
        assert parts == [k] + [1] * (n - k)
        # All labels >= k are fixed by D and can be permuted arbitrarily.
        # Label the tail images of f(0,0),...,f(0,k-1) in their order of
        # appearance. Since f(0,0)=1, at most i new labels appear by column i.
        cs += [[-p(0, 1, z)] for z in range(k + 1, n)]
        for i in range(k):
            cs += [[-p(0, i, z)] for z in range(k + i, n)]
            for j in range(i + 1, k):
                for v in range(k, n):
                    for w in range(k, v):
                        cs.append([-p(0, i, v), -p(0, j, w)])
    return cs


def cnf(parts, stabilize=False):
    n = sum(parts)
    cs = fixed_clauses(parts, stabilize)
    return (f'p cnf {variables(1110, n)} {len(cs)}\n' +
            ''.join(' '.join(map(str, c)) + ' 0\n' for c in cs)).encode()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory', type=Path, default=ROOT / '.cache/e1110-order13-replay')
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--seconds', type=int, default=600)
    args = ap.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    rows = []
    for parts in cycles():
        stabilize = parts in ([3] + [1] * 10, [4] + [1] * 9)
        name = 'cycles_' + '_'.join(map(str, parts))
        path = args.directory / (name + '.cnf')
        path.write_bytes(cnf(parts, stabilize))
        if args.solve:
            start = time.monotonic()
            with path.with_suffix('.log').open('w') as out:
                result = subprocess.run(['cadical', '-t', str(args.seconds), str(path)],
                                        stdout=out, stderr=subprocess.STDOUT)
            row = dict(cycles=parts, stabilize=stabilize,
                       status={10: 'SAT', 20: 'UNSAT'}.get(result.returncode, 'UNKNOWN'),
                       seconds=time.monotonic() - start)
            rows.append(row)
            print(json.dumps(row), flush=True)
            (args.directory / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')


if __name__ == '__main__':
    main()
