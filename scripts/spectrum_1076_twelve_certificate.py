#!/usr/bin/env python3
"""Audit/reproduce the compact, fully checked E1076 order-twelve exclusion.

First exclude the three first-row types with a three-cycle. That order-specific
result justifies extra three-cycle clauses in the remaining cases. Residual
row symmetries reduce f(1,0) to a few orbits; the eleven-cycle case uses three
groups of possible entries. Lean checks both the normalization and all proofs.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from itertools import product, permutations
import json
import lzma
from pathlib import Path
import resource
import subprocess
import time

from spectrum_1076_twelve_search import CASES, first_row, search_clauses
from spectrum_63_ten_certificate import TRIM

ROOT = Path(__file__).resolve().parents[1]
META = ROOT / 'data/spectrum/1076_order12.json'
DEST = ROOT / 'equational_theories/Spectrum/Equation1076/OrderTwelve/Certificates'
WORK = ROOT / '.cache/e1076-twelve-certificates'
SPECS = [('C0',0,None), ('C1G234',1,[2,3,4]), ('C2G234',2,[2,3,4]),
         ('C3G2345',3,[2,3,4,5]), ('C4G23456',4,[2,3,4,5,6]),
         ('C5G234',5,[2,3,4]), ('C5G567',5,[5,6,7]),
         ('C5G891011',5,[8,9,10,11]), ('Coverage',None,None)]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def formula(tag,j,zs):
    if tag == 'Coverage':
        return 'RowTransfer.coverage'
    r = f'(CanonicalData.row (CanonicalData.representative {j}))'
    if zs is None:
        return f'PointEncoding.natFormula {r} false'
    return f'PointEncoding.groupFormula {r} {"true" if j >= 3 else "false"} [{",".join(map(str,zs))}]'


def cnf(tag,j,zs):
    n = 12
    p = lambda x,y,z: 1+(x*n+y)*n+z
    q = lambda x,y,z: 1+n**3+(x*n+y)*n+z
    if tag == 'Coverage':
        cs = search_clauses(None,True)
        ordered = sorted({parts for case in CASES for parts in permutations(case)})
        assert len(ordered) == 13
        cs += [[-p(0,y,z) for y,z in enumerate(first_row(parts))] for parts in ordered]
    else:
        cs = search_clauses(CASES[j],True)
        cs += [[-p(x,y,z),-p(y,z,x)] for x,y,z in product(range(n),repeat=3) if x!=y]
        cs += [[q(x,x,x)] for x in range(n)]
        cs += [[-q(x,y,x)] for x,y in product(range(n),repeat=2) if x!=y]
        if j >= 3:
            cs += [[-p(x,y,a),-p(x,a,b),-p(x,b,y)]
                   for x,y,a,b in product(range(n),repeat=4) if x!=y]
        if zs is not None:
            cs += [[p(1,0,z) for z in zs]]
    return (f'p cnf 3456 {len(cs)}\n' +
            ''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()


def render(r):
    return f'''import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 {r['cnf_sha256']}.
Compact payload SHA-256 {r['proof_sha256']}. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.{r['tag']}
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../{r['certificate']}")
  ({r['formula']})
@[spectrum_native]
theorem checked : check refutation ({r['formula']}) = true := by native_decide
theorem unsat : ({r['formula']}).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.{r['tag']}
'''


def solve(spec,seconds):
    tag,j,zs = spec
    data = cnf(*spec)
    stem = WORK/tag
    stem.with_suffix('.cnf').write_bytes(data)
    proof = stem.with_suffix('.lrat')
    def limit():
        resource.setrlimit(resource.RLIMIT_FSIZE,(1024**3,1024**3))
    start = time.monotonic()
    with stem.with_suffix('.log').open('w') as log:
        r = subprocess.run(['cadical','--lrat','-t',str(seconds),
                            str(stem.with_suffix('.cnf')),str(proof)],
                           stdout=log,stderr=subprocess.STDOUT,
                           timeout=seconds+30,preexec_fn=limit)
    assert r.returncode == 20, (tag,r.returncode)
    elapsed = time.monotonic()-start
    subprocess.run(['lake','env','lean','--run',str(WORK/'TrimBinary.lean'),str(proof)],
                   cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    compact = stem.with_suffix('.rup')
    with Path(str(proof)+'.trimmed.bin').open('rb') as source:
        subprocess.run([str(WORK/'compact-rup'),'--input-mask',str(compact)],
                       stdin=source,check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    raw = compact.read_bytes()
    packed = lzma.compress(raw,preset=6)
    assert len(packed) < 10*1024**2, (tag,len(packed))
    path = ROOT/f'data/spectrum/1076_order12_rup/{tag}.rup.xz'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(packed)
    result = dict(tag=tag,j=j,point=zs,compressed_bytes=len(packed),proof_bytes=len(raw),
                  seconds=round(elapsed,3),cnf_sha256=sha(data),proof_sha256=sha(raw),
                  compressed_sha256=sha(packed),certificate=str(path.relative_to(ROOT)),
                  formula=formula(*spec))
    print(f'{tag}: {len(packed):,} bytes; solver {elapsed:.2f}s',flush=True)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--solve',action='store_true')
    ap.add_argument('--only',nargs='+',choices=[s[0] for s in SPECS])
    ap.add_argument('--seconds',type=int,default=90)
    ap.add_argument('--jobs',type=int,default=3)
    ap.add_argument('--write',action='store_true',help='Rewrite certificate modules')
    ap.add_argument('--export-cnf',type=Path)
    ap.add_argument('--check-lean-cnf',type=Path)
    args = ap.parse_args()
    if args.only and not args.solve:
        ap.error('--only requires --solve')
    if args.jobs <= 0 or args.seconds <= 0:
        ap.error('--jobs and --seconds must be positive')
    if args.solve:
        WORK.mkdir(parents=True,exist_ok=True)
        (WORK/'TrimBinary.lean').write_text(TRIM.replace('".trimmed"','".trimmed.bin"')
                                         .replace('trimmed false','trimmed true'))
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'scripts/spectrum_compact_rup.cpp'),
                        '-o',str(WORK/'compact-rup')],check=True)
        previous = {r['tag']:r for r in json.loads(META.read_text())['cases']} if args.only else {}
        selected = [s for s in SPECS if not args.only or s[0] in args.only]
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(lambda s:solve(s,args.seconds),selected))
        previous.update({r['tag']:r for r in results})
        rs = [previous[s[0]] for s in SPECS]
        META.write_text(json.dumps(dict(law=1076,order=12,cases=rs),indent=2)+'\n')
    rs = json.loads(META.read_text())['cases']
    assert [r['tag'] for r in rs] == [s[0] for s in SPECS]
    for spec,r in zip(SPECS,rs):
        assert r['formula'] == formula(*spec)
        data = cnf(*spec)
        assert sha(data) == r['cnf_sha256'], r['tag']
        packed = (ROOT/r['certificate']).read_bytes()
        raw = lzma.decompress(packed)
        assert len(packed) == r['compressed_bytes'] and sha(packed) == r['compressed_sha256']
        assert len(raw) == r['proof_bytes'] and sha(raw) == r['proof_sha256']
        if args.export_cnf:
            args.export_cnf.mkdir(parents=True,exist_ok=True)
            (args.export_cnf/(r['tag']+'.cnf')).write_bytes(data)
        if args.check_lean_cnf:
            assert (args.check_lean_cnf/(r['tag']+'.cnf')).read_bytes() == data, r['tag']
        path = DEST/(r['tag']+'.lean')
        if args.write or (args.solve and (not args.only or r['tag'] in args.only)):
            DEST.mkdir(parents=True,exist_ok=True)
            path.write_text(render(r))
        else:
            assert path.read_text() == render(r), path
    print(f'Checked {len(rs)} cases, {sum(r["compressed_bytes"] for r in rs):,} bytes.')


if __name__ == '__main__':
    main()
