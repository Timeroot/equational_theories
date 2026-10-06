#!/usr/bin/env python3
"""Reproduce the thirteen E229 row certificates excluding idempotent E667/15.

Default verifies hashes and regenerates Rows.lean. --solve regenerates each
LRAT proof, trims it, and stores the compressed result. Row coverage is proved
separately in Canonical.lean using the general chain-row enumeration theorem.
"""
import argparse,gzip,json,subprocess,tempfile,time
from pathlib import Path
from itertools import product
from spectrum_63_ten_certificate import ROOT,TRIM,clauses as cubic_clauses,sha

DATA=ROOT/'data/spectrum/667_idempotent_fifteen.json'
DIR=ROOT/'data/spectrum/667_idempotent_fifteen_lrat'
ROWS=ROOT/'equational_theories/Spectrum/Equation667IdempotentFifteen/Rows.lean'

def parts(n,lo=3):
    if not n:yield []
    for k in range(lo,n+1):
        for tail in parts(n-k,k):yield [k]+tail

def row(lengths):
    out=[0];offset=1
    for k in lengths:out+=list(range(offset+1,offset+k))+[offset];offset+=k
    return out

def cnf(lengths):
    n=15;r=range(n);p=lambda x,y,z:1+(x*n+y)*n+z
    cs=cubic_clauses(n)+[[p(x,x,x)] for x in r]+[[p(0,y,z)] for y,z in enumerate(row(lengths))]
    return (f'p cnf {n**3} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()

def render():
    rs=list(parts(14));vec=',\n    '.join('!['+','.join(map(str,row(r)))+']' for r in rs)
    return '''import equational_theories.Spectrum.SmallPairs.ChainRows
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation

/-! Generated canonical rows; coverage is verified in Canonical.lean. -/
namespace Spectrum.E667.IdempotentFifteen

def row : Fin 13 → Fin 15 → Fin 15 :=
  !['''+vec+''']

def rows : List (Fin 15 → Fin 15) := (List.finRange 13).map row
end Spectrum.E667.IdempotentFifteen
'''

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--solve',action='store_true');ap.add_argument('--reuse',type=Path,help='trim existing case LRAT files instead of rerunning the solver');args=ap.parse_args()
    rs=list(parts(14));assert len(rs)==13;DIR.mkdir(parents=True,exist_ok=True);ROWS.parent.mkdir(parents=True,exist_ok=True)
    if args.solve or args.reuse:
        records=[]
        with tempfile.TemporaryDirectory(prefix='e667-fifteen-') as work:
            work=Path(work);trim=work/'Trim.lean';trim.write_text(TRIM)
            for i,lengths in enumerate(rs):
                label='-'.join(map(str,lengths));raw=cnf(lengths);inp=work/'input.cnf';inp.write_bytes(raw)
                pr=args.reuse/(label+'.lrat') if args.reuse else work/'proof.lrat'
                if not args.reuse:
                    t=time.monotonic();r=subprocess.run(['cadical','--quiet','--shrink=0','--lrat','--no-binary','-t','120',str(inp),str(pr)],capture_output=True,text=True)
                    assert r.returncode==20,(label,r.returncode)
                    seconds=time.monotonic()-t
                else:seconds=json.loads((args.reuse/(label+'.json')).read_text())['seconds']
                subprocess.run(['lake','env','lean','--run',str(trim),str(pr)],cwd=ROOT,check=True)
                payload=Path(str(pr)+'.trimmed').read_bytes();z=gzip.compress(payload,mtime=0);target=DIR/f'{i}.lrat.gz';target.write_bytes(z)
                records.append(dict(index=i,cycles=[1]+lengths,cnf_sha256=sha(raw),proof_sha256=sha(payload),compressed_sha256=sha(z),proof_bytes=len(payload),compressed_bytes=len(z),search_seconds=round(seconds,3)))
                print(i,len(z),flush=True)
        DATA.write_text(json.dumps(dict(law=667,order=15,restriction='idempotent',cases=records),indent=2)+'\n')
    saved=json.loads(DATA.read_text())
    for i,lengths in enumerate(rs):
        rec=saved['cases'][i];z=(DIR/f'{i}.lrat.gz').read_bytes()
        assert sha(cnf(lengths))==rec['cnf_sha256'] and sha(z)==rec['compressed_sha256'] and sha(gzip.decompress(z))==rec['proof_sha256']
    ROWS.write_text(render());print('All 13 cases verified; Rows.lean regenerated.')

if __name__=='__main__':main()
