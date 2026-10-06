#!/usr/bin/env python3
"""Audit/replay the complete external exclusion of E467 at order sixteen.

This is not yet a Lean nonexistence theorem. The algebra and general
first-occurrence normalization are proved in Lean, but the exhaustive case
split and its link to the CNF still require formalization. --check-cnfs
reconstructs every selected CNF and checks its saved hash. --solve repeats
all selected searches (or just --case INDEX), without creating proof traces.
"""
import argparse
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

import spectrum_467_square_search as square
import spectrum_467_1516_search as row

ROOT = Path(__file__).resolve().parent.parent


def partitions(n, lower=1):
    if n == 0:
        yield ()
    for k in range(lower, n+1):
        for rest in partitions(n-k, k):
            yield (k,) + rest


def selected_cases():
    data = json.loads((ROOT/'data/spectrum/467_order16_square_research.json').read_text())
    old = json.loads((ROOT/'data/spectrum/467_1516_order16_research.json').read_text())
    # Independently enumerate ordinary integer partitions, then distinguish
    # a shortest moving cycle. This must agree with the search enumeration.
    types = set()
    for part in partitions(16):
        if 2 in part or 3 in part or max(part) == 1:
            continue
        tail = list(part)
        k = min(x for x in tail if x > 1)
        tail.remove(k)
        types.add((k,) + tuple(tail))
    assert types == set(square.cycle_types(16)) and len(types) == 50
    whole = (data['square_cycle_survey'] + data['longer_square_cycle_searches'] +
             [r for r in data['full_first_use_searches'] if not r['anchor']])
    returns = data['return_point_subcases'] + data['long_return_searches']
    result = []
    for shape in sorted(types):
        candidates = [r for r in whole if tuple(r['square_cycles']) == shape and r['status'] == 'UNSAT']
        if candidates:
            result.append(dict(min(candidates, key=lambda r:r['seconds']), encoding='square'))
            continue
        # L_0 has 0 -> 1 -> k-1 -> v -> 0, with fixed point 2.
        # Before column k-1, at most k-4 earlier free columns can introduce
        # fixed labels; first-use therefore bounds v <= 2k-4 outside the cycle.
        k = shape[0]
        assert all(x == 1 for x in shape[1:])
        allowed = list(range(3,k-1)) + list(range(k,min(16,2*k-3)))
        for v in allowed:
            candidates = [r for r in returns if tuple(r['square_cycles']) == shape
                          and r['row_return'] == v and r['status'] == 'UNSAT']
            assert candidates, (shape,v)
            result.append(dict(min(candidates, key=lambda r:r['seconds']), encoding='square'))
    idem = [r for r in old['cases'] if r['cycles'][0] == 1]
    expected = {(1,)+p for p in partitions(15,3)}
    assert {tuple(r['cycles']) for r in idem} == expected and len(idem) == 17
    assert all(r['status'] == 'UNSAT' for r in idem)
    result.extend(dict(r, encoding='row') for r in idem)
    return result


@lru_cache(maxsize=4)
def row_base(strength):
    return row.clauses(467,16,strength=strength)


def cnf(record):
    n = 16
    if record['encoding'] == 'square':
        d = square.permutation(record['square_cycles'])
        cs = square.clauses(d)
        if record.get('full_first_use'):
            cs += square.full_first_use_clauses(n,record['square_cycles'][0])
        if 'row_return' in record:
            cs.append([1+d.index(0)*n+record['row_return']])
        variables = n**3
    else:
        cs = row_base(record['strength']) + [[1+y*n+z]
             for y,z in enumerate(square.permutation(record['cycles']))]
        if record['first_use']:
            cs += row.first_use_clauses(n,record['cycles'])
        variables = 2*n**3
    return (f'p cnf {variables} {len(cs)}\n' +
            ''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check-cnfs', action='store_true')
    ap.add_argument('--check-certificates', action='store_true',
                    help='replay the saved LRAT traces for the last two cases using Lean\'s checker executable')
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--case', type=int)
    ap.add_argument('--seconds', type=int, default=600)
    ap.add_argument('--output', type=Path, default=ROOT/'.cache/e467-sixteen-replay')
    args = ap.parse_args()
    records = selected_cases()
    print(f'Complete cover: 50 nonidentity squaring types and 17 idempotent row types; {len(records)} UNSAT searches.',flush=True)
    if args.case is not None and not 0 <= args.case < len(records):
        ap.error('case index out of range')
    if args.check_certificates:
        meta = json.loads((ROOT/'data/spectrum/467_order16_square_research.json').read_text())
        for cert in meta['last_case_certificates']:
            record = next(r for r in records if r['cnf_sha256'] == cert['cnf_sha256'])
            packed = (ROOT/cert['file']).read_bytes()
            assert hashlib.sha256(packed).hexdigest() == cert['gzip_sha256']
            proof = gzip.decompress(packed)
            assert hashlib.sha256(proof).hexdigest() == cert['proof_sha256']
            data = cnf(record)
            assert hashlib.sha256(data).hexdigest() == cert['cnf_sha256']
            with tempfile.TemporaryDirectory(prefix='e467-lrat-') as work:
                base = Path(work)/'check'
                base.with_suffix('.cnf').write_bytes(data)
                base.with_suffix('.lrat').write_bytes(proof)
                subprocess.run(['lake','env','lean','--run',
                                str(ROOT/'scripts/templates/SpectrumResearchLRAT.lean'),
                                str(base)],cwd=ROOT,check=True)
    if args.check_cnfs or args.solve:
        if args.solve:args.output.mkdir(parents=True,exist_ok=True)
        for i,r in enumerate(records):
            if args.case is not None and args.case != i:continue
            data = cnf(r)
            assert hashlib.sha256(data).hexdigest() == r['cnf_sha256'], f'CNF hash mismatch: case {i}'
            if args.solve:
                file = args.output/f'{i}.cnf';file.write_bytes(data)
                start = time.monotonic()
                with file.with_suffix('.log').open('w') as f:
                    p = subprocess.run(['cadical','-t',str(args.seconds),str(file)],stdout=f,stderr=f)
                record = dict(r,replay_seconds=time.monotonic()-start,replay_exit=p.returncode)
                file.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
                assert p.returncode == 20, f'UNSAT not established on replay: case {i}'
                file.unlink()
            if i%10 == 0:print(f'Checked through case {i}.',flush=True)
        print('All selected CNF hashes match.' + (' All selected searches returned UNSAT.' if args.solve else ''),flush=True)


if __name__ == '__main__':
    main()
