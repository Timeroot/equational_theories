#!/usr/bin/env python3
"""Reproduce and audit the compact E1483 order-twelve exclusion certificates.

The clause order is part of each certificate. Lean independently defines these
CNFs, proves their soundness and normalization, and checks the reconstructed
LRAT deductions. This script audits data and generated wrappers, not logic.
"""
import argparse
import hashlib
import itertools
import json
import lzma
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data/spectrum/1483_order12.json"
DEST = ROOT / "equational_theories/Spectrum/Equation1483/OrderTwelve/Certificates"

def central_base(n, k, zero):
    """Independent DIMACS encoding; clause order is part of the certificate."""
    assert n == 12 and 2 <= k < n and (not zero or k >= 4)
    R = range(n)
    base = []
    a = lambda t, x, y, z: 1 + ((t * n + x) * n + y) * n + z
    p = lambda x, y, z: a(0, x, y, z)
    r = lambda x, z: a(1, x, z, 0)
    g = lambda x, y, z: a(2, x, y, z)
    c = lambda x, z: a(3, x, z, 0)
    d = lambda x, y, z: a(4, x, y, z)
    R = range(n)
    for x, y in itertools.product(R, repeat=2):
        base.append([p(x, y, z) for z in R])
    for x, y, z, w in itertools.product(R, repeat=4):
        if z != w:
            base.append([-p(x, y, z), -p(x, y, w)])
    for y, z, b in itertools.product(R, repeat=3):
        base.append([-p(y, z, b), r(y, b)])
    for y, z, b in itertools.product(R, repeat=3):
        base.append([-p(z, y, b), c(y, b)])
    for x, y, u, b in itertools.product(R, repeat=4):
        base.append([-p(y, x, u), -r(y, b), g(x, u, b)])
    for x, u, b, v in itertools.product(R, repeat=4):
        base.append([-g(x, u, b), -p(x, b, v), p(u, v, x)])
    for x, y, u, b in itertools.product(R, repeat=4):
        base.append([-p(x, y, u), -c(y, b), d(x, u, b)])
    for x, u, b, v in itertools.product(R, repeat=4):
        base.append([-d(x, u, b), -p(b, x, v), p(v, u, x)])

    large = lambda x: a(5, x, 0, 0)
    # Reverse implications make row/column membership exact.
    for y, b in itertools.product(R, repeat=2):
        base.append([-r(y, b)] + [p(y, z, b) for z in R])
        base.append([-c(y, b)] + [p(z, y, b) for z in R])
    # Regularity of translations, proved from E1483 and its dual.
    for x, b, z in itertools.product(R, repeat=3):
        base.append([-c(x, b), -p(x, b, z), p(z, x, b)])
        base.append([-r(x, b), -p(b, x, z), p(x, z, b)])
    for x in R:
        for image in (r, c):
            base.append([-image(x, z) for z in R])
    clauses = list(base)
    for x in R:
        for image in (r, c):
            for sub in itertools.combinations(R, n - k + 1):
                clauses.append([image(x, z) for z in sub])
    image = set(range(k)) if zero else set(range(1, k + 1))
    for z in R:
        clauses.append([r(0, z) if z in image else -r(0, z)])
    for sub in itertools.combinations(R, k + 1):
        clauses.append([-c(0, z) for z in sub])
    clauses.append([p(0, 0, 0), p(0, 0, 1)] if zero else [p(0, 0, 1)])
    # Rows of rank three cannot be joined by either a row or column edge.
    if k == 3:
        for x in R:
            for im in (r, c):
                for sub in itertools.combinations(R, n - 3):
                    clauses.append([-large(x)] + [im(x, z) for z in sub])
            clauses.append([-p(x, x, x), large(x)])
        for x, y in itertools.product(R, repeat=2):
            clauses.append([-r(x, y), large(x), large(y)])
            clauses.append([-c(x, y), large(x), large(y)])
    for y in range(k + 1, n - 1):
        for z, w in itertools.product(range(k + 1), repeat=2):
            if z > w:
                clauses.append([-p(0, y, z), -p(0, y + 1, w)])
    # Semantically necessary cardinality bounds on both ends of every image edge.
    for threshold in [3, 4, 6]:
        flag = lambda x: a(4 + threshold, x, 0, 0)
        for x in R:
            for im in (r, c):
                for sub in itertools.combinations(R, n - threshold + 1):
                    clauses.append([-flag(x)] + [im(x, z) for z in sub])
    for x in R:
        clauses.append([-p(x, x, x), a(8, x, 0, 0)])
    for x, y in itertools.product(R, repeat=2):
        for im in (r, c):
            for t, u in [(3, 6), (4, 4), (6, 3)]:
                clauses.append([-im(x, y), a(4 + t, x, 0, 0), a(4 + u, y, 0, 0)])
    clauses = [cl for cl in clauses if not any(-l in cl for l in cl)]
    return clauses


def central_clauses(n, k, zero):
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    row = lambda x, z: 1 + ((n + x) * n + z) * n
    col = lambda x, z: 1 + ((3 * n + x) * n + z) * n
    old_sort = {(-p(0, y, z), -p(0, y + 1, w))
                for y in range(k + 1, n - 1)
                for z in range(k + 1) for w in range(z)}
    cs = [c for c in central_base(n, k, zero) if tuple(c) not in old_sort]
    for a, b in itertools.product(range(n), repeat=2):
        cs.extend([[-row(a, b), col(b, a)], [-col(b, a), row(a, b)]])
    for a, b, z in itertools.product(range(n), repeat=3):
        cs.extend([[-p(a, b, z), row(z, b)], [-p(a, b, z), col(z, a)]])
    for y in range(k if zero else k + 1, n - 1):
        c, d = col(0, y), col(0, y + 1)
        cs.append([c, -d])
        for z, w in itertools.product(range(k + 1), repeat=2):
            if w < z:
                cs.append([c, d, -p(0, y, z), -p(0, y + 1, w)])
            if w <= z:
                cs.append([-c, -d, -p(0, y, z), -p(0, y + 1, w)])
    cs.extend([-p(0, 1, z)] for z in range(3, n))
    return cs


def clauses(rec):
    """Mirror ImageEncoding, RowOneEncoding, HeadLexEncoding, CombinedEncoding."""
    n, k, zero = 12, rec['rank'], rec['zero_in_image']
    kind = rec['encoding']
    second = kind in ('secondlex','secondcombined')
    base_kind = {'secondlex':'headlex','secondcombined':'combined'}.get(kind,kind)
    r = range(n)
    p = lambda x, y, z: 1 + (x*n+y)*n+z
    atom = lambda t, x, y, z: 1 + ((t*n+x)*n+y)*n+z
    row = lambda x, z: atom(1,x,z,0)
    col = lambda x, z: atom(3,x,z,0)
    cs = central_clauses(n,k,zero)
    cs += [[p(x,y,z)] for x,y,z in rec.get('fixed_cells',[])]
    bound = k-1 if zero else k
    if base_kind in ('rowone','headlex','combined','fibers'):
        for a,b,i,u in itertools.product(r,repeat=4):
            if bound<a<b and i<a and u<=k:
                cs.append([-p(0,a,u),-p(0,b,u),col(0,a),col(0,b),-p(1,i,b)]+
                          [p(1,j,v) for j in range(i) for v in (a,b)])
    if base_kind in ('headlex','combined','fibers'):
        cs.append([-p(0,0,0),p(0,1,0)])
        q = lambda a,b,i: 1+20736+(a*n+b)*n+i
        for a,b in itertools.product(r,repeat=2):
            if not 2<=a<b<=bound:
                continue
            swap = lambda x: b if x==a else a if x==b else x
            cs.append([q(a,b,0)])
            for i,v,w in itertools.product(range(bound+1),repeat=3):
                if v>swap(w):
                    cs.append([-q(a,b,i),-p(0,i,v),-p(0,swap(i),w)])
                if v==swap(w) and i<bound:
                    cs.append([-q(a,b,i),-p(0,i,v),-p(0,swap(i),w),q(a,b,i+1)])
    if base_kind in ('combined','fibers'):
        cs += [[-p(0,y,v)] for y in range(2,n) for v in range(y+2,n)]
        if k in (2,3):
            t, tag = n//k+1, (6 if k==2 else 9)
            image = range(k) if zero else range(1,k+1)
            for b in image:
                flag = atom(tag,b,0,0)
                for sub in itertools.combinations(r,n-t+1):
                    cs.append([-flag]+[row(b,v) for v in sub])
                for x,u in itertools.product(r,repeat=2):
                    cs.append([flag,-p(b,x,u),p(0,u,b)])
                    cs.append([flag,-p(x,0,u),p(u,b,0)])
    if second:
        full = rec.get('full',False)
        q = lambda a,b,i: 1+22464+(a*n+b)*n+i
        for a,b in itertools.product(r,repeat=2):
            if not bound<a<b:
                continue
            swap = lambda x: b if x==a else a if x==b else x
            for u in range(k+1):
                cs.append([col(0,a),col(0,b),-p(0,a,u),-p(0,b,u),q(a,b,0)])
            stop = n-1 if full else a
            for i in range(stop+1):
                for v,w in itertools.product(r,repeat=2):
                    if v>swap(w):
                        cs.append([-q(a,b,i),-p(1,i,v),-p(1,swap(i),w)])
                    if v==swap(w) and i<stop:
                        cs.append([-q(a,b,i),-p(1,i,v),-p(1,swap(i),w),q(a,b,i+1)])
    assert kind in ('image','rowone','headlex','combined','secondlex','secondcombined')
    return [c for c in cs if not any(-v in c for v in c)]


def cnf_bytes(rec):
    cs = clauses(rec)
    nv = (20736 if rec['encoding'] in ('image','rowone') else
          24192 if rec['encoding'] in ('secondlex','secondcombined') else 22464)
    return (f'p cnf {nv} {len(cs)}\n'+
            ''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()


def lean_formula(rec):
    prefix = {'image':'ImageEncoding.fixedNat', 'rowone':'RowOneEncoding.toNat',
              'headlex':'HeadLexEncoding.toNat', 'combined':'CombinedEncoding.toNat',
              'secondlex':'SecondLexEncoding.toNat', 'secondcombined':'SecondLexEncoding.strongNat'}[rec['encoding']]
    if rec['encoding'] in ('secondlex','secondcombined'):
        prefix += ' '+str(rec.get('full',False)).lower()
    cells = '['+', '.join(f'({x},{y},{z})' for x,y,z in rec.get('fixed_cells',[]))+']'
    return f"{prefix} {rec['rank']} {str(rec['zero_in_image']).lower()} {cells}"


def render(rec):
    module = {'image':'ImageEncoding','rowone':'RowOneEncoding','headlex':'HeadLexEncoding',
              'combined':'CombinedEncoding','secondlex':'SecondLexEncoding',
              'secondcombined':'SecondLexEncoding'}[rec['encoding']]
    formula = lean_formula(rec)
    return f'''import equational_theories.Spectrum.Equation1483.OrderTwelve.{module}
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated by scripts/spectrum_1483_twelve.py.
CNF SHA-256: {rec['cnf_sha256']}
Compact payload SHA-256: {rec['proof_sha256']} -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.Certificates.{rec['name']}
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData

private def refutation : Array IntAction :=
  CompactRup.reconstruct (include_binary_xz "../../../../../{rec['certificate']}")
    ({formula})

@[spectrum_native]
theorem checked : check refutation ({formula}) = true := by native_decide

theorem unsat : ({formula}).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.Certificates.{rec['name']}
'''


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true',help='rewrite generated Lean wrappers')
    ap.add_argument('--export-cnf',type=Path)
    ap.add_argument('--check-lean-cnf',type=Path)
    args = ap.parse_args()
    rows = json.loads(DATA.read_text())['cases']
    assert len({r['name'] for r in rows}) == len(rows)
    for rec in rows:
        name = rec['name']
        cnf = cnf_bytes(rec)
        assert sha(cnf) == rec['cnf_sha256'], (name,'CNF hash')
        assert len(cnf.splitlines())-1 == rec['clauses']
        packed = (ROOT/rec['certificate']).read_bytes()
        raw = lzma.decompress(packed)
        assert len(packed) == rec['compressed_bytes'] and sha(packed) == rec['compressed_sha256']
        assert len(raw) == rec['proof_bytes'] and sha(raw) == rec['proof_sha256']
        initial = shift = pos = 0
        while True:
            b = raw[pos]
            pos += 1
            initial |= (b & 127) << shift
            if b < 128:
                break
            shift += 7
            assert shift < 70
        assert initial == 2*(rec['clauses']+1) and raw[pos] == ord('m')
        mask = raw[pos+1:pos+1+initial//2]
        assert len(mask) == initial//2 and mask[0] == 0 and all(x in (0,1) for x in mask)
        if args.export_cnf:
            args.export_cnf.mkdir(parents=True,exist_ok=True)
            (args.export_cnf/(name+'.cnf')).write_bytes(cnf)
        if args.check_lean_cnf:
            assert (args.check_lean_cnf/(name+'.cnf')).read_bytes() == cnf, name
        dest = DEST/(name+'.lean')
        if args.write:
            DEST.mkdir(parents=True,exist_ok=True)
            dest.write_text(render(rec))
        else:
            assert dest.read_text() == render(rec), dest
        print(f"{name}: {len(packed):,} bytes; hashes and formula checked.")
    print(f"All {len(rows)} certificates checked; {sum(r['compressed_bytes'] for r in rows):,} bytes.")


if __name__ == '__main__':
    main()
