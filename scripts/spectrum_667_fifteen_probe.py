#!/usr/bin/env python3
"""Bounded order-15 subclass probes, retaining exact scopes and input hashes.

The cubic case is equivalent to globally idempotent E667, by left division.
The commutative-permutation case additionally assumes bijective squaring and
no idempotents. These are research restrictions, not silently imposed axioms.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from itertools import combinations,product
import json
from pathlib import Path
import subprocess
import time

from spectrum_63_ten_certificate import clauses as cubic_clauses
from spectrum_667_incremental import clauses as e667_clauses
from spectrum_generate import load_equations,satisfies


def encode(case):
    n=15;r=range(n)
    p=lambda x,y,z:1+(x*n+y)*n+z
    if case=='idempotent':
        return n**3,cubic_clauses(n)+[[p(x,x,x)] for x in r]
    cs=e667_clauses(n,'unnormalized')
    for y,z in product(r,repeat=2):
        if y+1<z:cs.append([-p(0,y,z)])
    if case=='right-identity':
        cs.extend([[p(x,0,x)] for x in r])
    elif case.startswith('commutative'):
        for x,y,z in product(r,repeat=3):
            cs.append([-p(x,y,z),p(y,x,z)])
        if case=='commutative-permutation':
            cs.extend([[-p(x,x,x)] for x in r])
            for z in r:
                cs.append([p(x,x,z) for x in r])
                cs.extend([-p(x,x,z),-p(y,y,z)] for x,y in combinations(r,2))
    else:raise ValueError(case)
    return 2*n**3,[c for c in cs if not any(-v in c for v in c)]


def work(args,case):
    n=15;r=range(n);top,cs=encode(case)
    raw=(f'p cnf {top} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()
    base=args.output/case;base.with_suffix('.cnf').write_bytes(raw)
    cmd=['cadical','--quiet','-t',str(args.seconds),str(base.with_suffix('.cnf'))]
    if args.lrat:
        cmd[1:1]=['--shrink=0','--lrat','--no-binary'];cmd.append(str(base.with_suffix('.lrat')))
    start=time.monotonic();print(json.dumps(dict(event='start',case=case)),flush=True)
    result=subprocess.run(cmd,capture_output=True,text=True)
    record=dict(law=667,order=n,restriction=case,status={10:'SAT',20:'UNSAT'}.get(result.returncode,'UNKNOWN'),cpu_limit=args.seconds,wall_seconds=round(time.monotonic()-start,3),variables=top,clauses=len(cs),cnf_sha256=sha256(raw).hexdigest(),proof_status='external search; no Lean replay')
    if result.returncode==10:
        vals={int(v) for line in result.stdout.splitlines() if line.startswith('v ') for v in line.split()[1:]}
        table=[next(z for z in r if 1+(x*n+y)*n+z in vals) for x,y in product(r,repeat=2)]
        if case=='idempotent':
            table=[next(y for y in r if table[x*n+y]==z) for x,z in product(r,repeat=2)]
        assert satisfies(*load_equations()[666],table,n)
        record['table']=table
    base.with_suffix('.out').write_text(result.stdout+result.stderr)
    base.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
    return record


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case',choices=['all','idempotent','right-identity','commutative','commutative-permutation'],default='all')
    ap.add_argument('--seconds',type=int,default=600)
    ap.add_argument('--lrat',action='store_true')
    ap.add_argument('--output',type=Path,default=Path('.cache/e667-fifteen-subclasses'))
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    cases=['idempotent','right-identity','commutative','commutative-permutation'] if args.case=='all' else [args.case]
    with ThreadPoolExecutor(max_workers=4) as pool:records=list(pool.map(lambda c:work(args,c),cases))
    (args.output/'results.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':main()
