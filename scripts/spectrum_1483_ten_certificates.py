#!/usr/bin/env python3
"""Reproduce and audit the fourteen Lean LRAT checks excluding E1483 at ten.

The default checks sources, certificate hashes, complete case coverage and exact
CNF reproduction. --write regenerates only the fourteen certificate modules.
--export-cnf DIR also writes solver inputs; solve these with Lean's CaDiCaL and
--quiet --shrink=0 --lrat --no-binary to obtain independently replayable proofs.
"""
import argparse
import gzip
import hashlib
import inspect
import itertools
import json
from pathlib import Path

import definability_1483_sat_check as old

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / 'data/spectrum/1483_order10_refutation.json'
DEST = ROOT / 'equational_theories/Spectrum/Equation1483/TenCases'
CASES = [(2, False), (3, False)] + [(k, z) for k in range(4, 10) for z in (False, True)]


def clauses(k, zero):
    source = inspect.getsource(old.cnf_clauses)
    source = source.replace('assert (k, zero) in CASES', 'assert (k, zero) in allowed')
    source = source.replace('n = 11', 'n = 10')
    source = source.replace('itertools.combinations(R, 8)', 'itertools.combinations(R, 7)')
    source = source.replace('[3, 4, 6]', '[3, 4, 5]')
    source = source.replace('[(3, 6), (4, 4), (6, 3)]', '[(3, 5), (4, 4), (5, 3)]')
    env = {'itertools': itertools, 'allowed': CASES}
    exec(source, env)
    return env['cnf_clauses'](k, zero)


def cnf_bytes(k, zero):
    cs = clauses(k, zero)
    return (f'p cnf 10000 {len(cs)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cs)).encode()


def render(d):
    k = d['rank']
    zero = d['zero_in_image']
    name = f'Rank{k}Zero{int(zero)}'
    return f'''import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: {d['cnf_sha256']}
Expanded proof SHA-256: {d['proof_sha256']}. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proof{name} : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../{d['certificate']}").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem check{name} :
    check proof{name} (CNF.natRankFormula 10 {k} {str(zero).lower()}) = true := by
  native_decide

theorem unsat{name} : (CNF.natRankFormula 10 {k} {str(zero).lower()}).Unsat :=
  check_sound proof{name} _ check{name}

end Spectrum.E1483.OrderTen.Refutation
'''


def verify(d, export, cnf_builder=None, variable_bound=10000):
    data = (cnf_builder or cnf_bytes)(d['rank'], d['zero_in_image'])
    assert hashlib.sha256(data).hexdigest() == d['cnf_sha256']
    assert len(data.splitlines()) - 1 == d['clauses']
    if export:
        export.mkdir(parents=True, exist_ok=True)
        (export / f'rank{d["rank"]}_zero{int(d["zero_in_image"])}.cnf').write_bytes(data)
    certificate = ROOT / d['certificate']
    assert hashlib.sha256(certificate.read_bytes()).hexdigest() == d['compressed_sha256']
    assert certificate.stat().st_size == d['compressed_bytes']
    digest = hashlib.sha256()
    size = count = 0
    last = None
    with gzip.open(certificate, 'rb') as inp:
        for line in inp:
            digest.update(line)
            size += len(line)
            words = list(map(int, line.split()))
            assert words[0] == d['clauses'] + count + 1
            cut = words.index(0, 1)
            assert words[-1] == 0
            assert all(0 < abs(x) <= variable_bound for x in words[1:cut])
            assert all(0 < x < words[0] for x in words[cut + 1:-1])
            assert cut > 1 or count + 1 == d['proof_steps']
            count += 1
            last = words
    assert last is not None and last[1] == 0
    assert (size, count, digest.hexdigest()) == (d['proof_bytes'], d['proof_steps'], d['proof_sha256'])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write', action='store_true')
    p.add_argument('--export-cnf', type=Path)
    args = p.parse_args()
    manifest = json.loads(DATA.read_text())
    cases = manifest['cases']
    assert sorted((d['rank'], d['zero_in_image']) for d in cases) == CASES
    for d in cases:
        name = f'Rank{d["rank"]}Zero{int(d["zero_in_image"])}'
        source = DEST / f'{name}.lean'
        text = render(d)
        if args.write:
            source.write_text(text)
        else:
            assert source.read_text() == text, f'{source} is stale'
        verify(d, args.export_cnf)
    print(f'Verified {len(cases)} complete cases, source reproduction, CNFs and certificate hashes.')


if __name__ == '__main__':
    main()
