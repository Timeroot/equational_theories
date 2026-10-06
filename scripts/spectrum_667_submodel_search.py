#!/usr/bin/env python3
"""Search for an idempotent E63/E667 algebra with a five- or seven-point subalgebra.

The known small E229 table is labelled along the cycles of its first
row, so the generic chain symmetry breaking remains valid. A positive result
is checked on every pair, after conversion from E229 to E63. Exhaustion only
excludes extensions of this particular small algebra.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

from spectrum_63_ten_certificate import clauses
from spectrum_667_idempotent_search import checked_table


def submodel(n):
    assert n in (5, 7)
    labels = [0, 1, 2, 4, 3] if n == 5 else [0, 1, 4, 2, 3, 5, 6]
    op = (lambda x,y: (2*y-x) % 5) if n == 5 else (lambda x,y: 4*(x+y) % 7)
    table = [[labels.index(op(x,y)) for y in labels] for x in labels]
    checked_table(table)
    assert all(z <= y + 1 for y, z in enumerate(table[0]))
    return table


def solve(n, seconds, workdir, suborder=7):
    assert n >= suborder
    workdir.mkdir(parents=True, exist_ok=True)
    stem = workdir / f"{n}-sub{suborder}"
    small = submodel(suborder)
    cs = clauses(n)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    cs.extend([[p(x, x, x)] for x in range(n)])
    cs.extend([[p(x, y, small[x][y])] for x in range(suborder) for y in range(suborder)])
    path = stem.with_suffix('.cnf')
    with path.open('w') as f:
        f.write(f'p cnf {n**3} {len(cs)}\n')
        for c in cs:
            f.write(' '.join(map(str, c)) + ' 0\n')
    out = dict(order=n, submodel_order=suborder, encoding='idempotent E229',
               seconds_limit=seconds, variables=n**3, clauses=len(cs),
               cnf_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
               scope=f'extensions of the specified affine {suborder}-point subalgebra')
    del cs
    start = time.monotonic()
    cp = subprocess.run(['cadical', '--quiet', '-t', str(seconds), str(path)],
                        capture_output=True, text=True)
    out.update(elapsed=time.monotonic()-start,
               status={10:'SAT', 20:'UNSAT'}.get(cp.returncode, 'UNKNOWN'))
    stem.with_suffix('.log').write_text(cp.stdout + cp.stderr)
    if cp.returncode == 10:
        vals = {int(v) for line in cp.stdout.splitlines() if line.startswith('v ')
                for v in line.split()[1:]}
        table = [[next(z for z in range(n) if p(x,y,z) in vals)
                  for y in range(n)] for x in range(n)]
        assert all(table[x][y] == small[x][y] for x in range(suborder) for y in range(suborder))
        out.update(e229_table=table, e63_table=checked_table(table))
    path.unlink()
    stem.with_suffix('.json').write_text(json.dumps(out, indent=2)+'\n')
    return {k:v for k,v in out.items() if not k.endswith('_table')}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('order', type=int)
    p.add_argument('--seconds', type=int, default=300)
    p.add_argument('--suborder', type=int, choices=[5,7], default=7)
    p.add_argument('--workdir', type=Path, required=True)
    a = p.parse_args()
    print(solve(a.order, a.seconds, a.workdir, a.suborder))
