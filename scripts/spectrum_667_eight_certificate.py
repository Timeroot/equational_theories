#!/usr/bin/env python3
"""Certificate for the unique normalized idempotent-free E667 table at order 8."""
import argparse,gzip,json,subprocess,tempfile,time
from itertools import product,combinations
from pathlib import Path
from spectrum_63_ten_certificate import ROOT,TRIM,sha

DATA=ROOT/'data/spectrum/667_eight_classification.json'
PROOF=ROOT/'data/spectrum/667_eight_classification.lrat.gz'

TABLE = [[1, 2, 3, 4, 5, 6, 0, 7], [5, 0, 4, 3, 1, 7, 2, 6], [4, 7, 5, 1, 3, 0, 6, 2], [2, 1, 6, 7, 0, 3, 5, 4], [7, 4, 0, 2, 6, 5, 3, 1], [3, 6, 1, 5, 4, 2, 7, 0], [6, 3, 2, 0, 7, 1, 4, 5], [0, 5, 7, 6, 2, 4, 1, 3]]

def canonical(x,y):
    return TABLE[x][y]

def clauses():
    n=8;r=range(n);p=lambda x,y,z:1+(x*n+y)*n+z;q=lambda x,y,z:1+n**3+(x*n+y)*n+z
    cs=[]
    def one(v):cs.append(v);cs.extend([-a,-b] for a,b in combinations(v,2))
    for x,y in product(r,repeat=2):
        for v in ([p(x,y,z) for z in r],[p(x,z,y) for z in r],[p(z,x,y) for z in r]):one(v)
    for x,y in product(r,repeat=2):
        one([q(x,y,z) for z in r])
        for a,b in product(r,repeat=2):cs.extend([[-p(x,x,a),-p(a,y,b),q(x,y,b)],[-p(x,x,a),p(a,y,b),-q(x,y,b)]])
        for a,b in product(r,repeat=2):cs.extend([[-q(x,y,a),-p(x,a,b),p(y,b,x)],[-q(x,y,a),p(x,a,b),-p(y,b,x)]])
    cs.extend([[-p(0,y,z)] for y,z in product(r,repeat=2) if y+1<z])
    cs.append([p(0,y,y) for y in r])
    cs.extend([[-p(x,x,x)] for x in r])
    cs.append([-p(x,y,canonical(x,y)) for x,y in product(r,repeat=2)])
    return [c for c in cs if not any(-v in c for v in c)]

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--solve',action='store_true');args=ap.parse_args()
    cs=clauses();raw=(f'p cnf 1024 {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()
    if args.solve:
        with tempfile.TemporaryDirectory(prefix='e667-eight-') as temp:
            temp=Path(temp);inp=temp/'input.cnf';pr=temp/'proof.lrat';inp.write_bytes(raw)
            start=time.monotonic();r=subprocess.run(['cadical','--quiet','--shrink=0','--lrat','--no-binary','-t','180',str(inp),str(pr)],capture_output=True,text=True)
            assert r.returncode==20,(r.returncode,r.stdout)
            elapsed=time.monotonic()-start
            trim=temp/'Trim.lean';trim.write_text(TRIM)
            subprocess.run(['lake','env','lean','--run',str(trim),str(pr)],cwd=ROOT,check=True)
            payload=Path(str(pr)+'.trimmed').read_bytes();z=gzip.compress(payload,mtime=0);PROOF.write_bytes(z)
            record=dict(law=667,order=8,scope='unique idempotent-free table after chain labelling a row with a fixed point',cnf_sha256=sha(raw),proof_sha256=sha(payload),compressed_sha256=sha(z),proof_bytes=len(payload),compressed_bytes=len(z),clauses=len(cs),variables=1024,search_seconds=round(elapsed,3),canonical_table=[canonical(x,y) for x,y in product(range(8),repeat=2)])
            DATA.write_text(json.dumps(record,indent=2)+'\n')
    record=json.loads(DATA.read_text());z=PROOF.read_bytes()
    assert sha(raw)==record['cnf_sha256'] and sha(z)==record['compressed_sha256'] and sha(gzip.decompress(z))==record['proof_sha256']
    print(f"E667/8 classification: {len(cs)} clauses; {len(z)} compressed bytes.")

if __name__=='__main__':main()
