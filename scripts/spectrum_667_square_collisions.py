#!/usr/bin/env python3
"""The three square-map collisions in Equation667SquareCases.square_cases.

First-use normalization fixes all named points and traverses the growing
square of table entries. Refutations remain external until replayed in Lean.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time

from spectrum_667_incremental import clauses


def encode(case):
    n=12;p=lambda x,y,z:1+(x*n+y)*n+z
    if case=='idempotent':k=2;units=[(0,0,0),(1,1,0)]
    elif case=='three':k=3;units=[(0,0,2),(1,1,2),(2,2,0)]
    elif case=='four':k=4;units=[(0,0,2),(1,1,2),(2,2,3)]
    else:raise ValueError(case)
    cs=clauses(n,'one-idempotent')
    cs.extend([p(*u)] for u in units)
    cells=sorted(((x,y) for x in range(n) for y in range(n)),key=lambda c:(max(c),*c))
    for i,(x,y) in enumerate(cells):
        for z in range(max(k,max(x,y)+1)+1,n):
            cs.append([-p(x,y,z)]+[p(u,v,z-1) for u,v in cells[:i]])
    return 2*n**3,cs


def solve(case,seconds,workdir,proof=False):
    top,cs=encode(case);stem=workdir/case;path=stem.with_suffix('.cnf')
    with path.open('w') as out:
        out.write(f'p cnf {top} {len(cs)}\n')
        for c in cs:out.write(' '.join(map(str,c))+' 0\n')
    record=dict(order=12,case=case,variables=top,clauses=len(cs),
                cnf_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                normalization='growing-square first use, fixing named points',
                proof_status='external; not yet replayed in Lean',seconds_limit=seconds)
    del cs
    command=['cadical','-t',str(seconds),str(path)]
    if proof:command[1:1]=['--lrat','--no-binary','--shrink=0'];command.append(str(stem.with_suffix('.lrat')))
    start=time.monotonic();cp=subprocess.run(command,capture_output=True,text=True)
    record.update(status={10:'SAT',20:'UNSAT'}.get(cp.returncode,'UNKNOWN'),
                  elapsed=time.monotonic()-start,exit_code=cp.returncode)
    stem.with_suffix('.log').write_text(cp.stdout+cp.stderr)
    stem.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    print(record,flush=True)
    return record


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seconds',type=int,default=300)
    ap.add_argument('--workdir',type=Path,required=True)
    ap.add_argument('--proof',action='store_true')
    args=ap.parse_args();args.workdir.mkdir(parents=True,exist_ok=True)
    with ThreadPoolExecutor(max_workers=3) as pool:
        list(pool.map(lambda c:solve(c,args.seconds,args.workdir,args.proof),
                      ['idempotent','three','four']))
