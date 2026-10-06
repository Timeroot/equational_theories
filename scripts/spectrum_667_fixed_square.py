#!/usr/bin/env python3
"""E667 searches with a prescribed square map, eliminating the auxiliary table.

Permutation cycle types exhaust bijective square maps up to relabelling.
No row normalization is imposed: it need not preserve the chosen square map.
Each finite search result is external unless its certificate is replayed in Lean.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import time

from spectrum_667_incremental import partitions
from spectrum_generate import load_equations, satisfies


def permutation(cycles):
    result=[]
    for k in cycles:
        i=len(result)
        result.extend(list(range(i+1,i+k))+[i])
    return result


def encode(square, extra=True):
    n=len(square);r=range(n);cs=[]
    p=lambda x,y,z:1+(x*n+y)*n+z
    for x,y in product(r,repeat=2):
        for vals in ([p(x,y,z) for z in r],[p(x,z,y) for z in r],[p(z,x,y) for z in r]):
            cs.append(vals)
            cs.extend([-a,-b] for a,b in combinations(vals,2))
    for x,y,a,b in product(r,repeat=4):
        av,bv,cv=p(square[x],y,a),p(x,a,b),p(y,b,x)
        cs.extend([[-av,-bv,cv],[-av,bv,-cv],[av,-bv,-cv]])
    cs.extend([p(x,x,square[x])] for x in r)
    if extra:
        if n==12:
            cs.append([-p(x,x,x) for x in r])
            for e in r:cs.append([-p(x,e,x) for x in r])
        for x,a,b in product(r,repeat=3):
            cs.append([-p(x,x,a),-p(x,a,b),-p(x,b,x),p(x,x,x)])
        for x,a in product(r,repeat=2):
            cs.append([-p(x,x,a),-p(x,a,x),p(a,a,a)])
        for e,x,y in product(r,repeat=3):
            cs.append([-p(e,e,e),-p(x,x,e),-p(e,x,y),p(e,y,x)])
            cs.append([-p(e,e,e),-p(e,x,y),-p(e,y,x),p(x,x,e)])
            cs.append([-p(e,e,e),-p(x,x,e),-p(e,x,y),p(y,y,e)])
    return n**3,[sorted(set(c)) for c in cs if not any(-v in c for v in c)]


def nonautomorphism_pairs(cycles):
    """Orbits of distinct ordered pairs under the centralizer of an involution.

    Cycles must put the fixed points first. A diagonal pair cannot witness
    failure of multiplicativity. Within moving points the second point is
    either the partner of the first or belongs to a different two-cycle.
    """
    assert list(cycles)==sorted(cycles) and set(cycles)<= {1,2}
    f=cycles.count(1);m=cycles.count(2)
    pairs=[]
    if f>=2:pairs.append((0,1))
    if f and m:pairs.extend([(0,f),(f,0)])
    if m:pairs.append((f,f+1))
    if m>=2:pairs.append((f,f+2))
    return pairs


def centralizer_first_use(square,pinned=()):
    """Necessary conditions for a lexicographically minimal relabelling.

    Use swaps of fixed points, flips of two-cycles, and swaps of two-cycles.
    They commute with the square map and fix the pinned labels. At a cell
    whose preceding inputs and outputs are fixed by a swap, the output may
    not be made smaller by it. This is weaker than a full lex-leader test.
    """
    n=len(square);r=range(n);p=lambda x,y,z:1+(x*n+y)*n+z
    assert all(square[square[x]]==x for x in r)
    fixed=[x for x in r if square[x]==x]
    pairs=[(x,square[x]) for x in r if x<square[x]]
    moves=[[(a,b)] for a,b in combinations(fixed,2)]
    moves += [[(a,b)] for a,b in pairs]
    moves += [[(a,b),(aa,bb)] for (a,aa),(b,bb) in combinations(pairs,2)]
    cs=[]
    for swaps in moves:
        s=list(r)
        for a,b in swaps:s[a]=b;s[b]=a
        assert all(s[square[x]]==square[s[x]] for x in r)
        if any(s[x]!=x for x in pinned):continue
        support=[x for x in r if s[x]!=x]
        lowers=[x for x in support if s[x]<x]
        previous=[]
        for x,y in product(r,repeat=2):
            if s[x]!=x or s[y]!=y:break
            cs.extend([-p(x,y,z)]+previous[:] for z in lowers)
            previous.extend(p(x,y,z) for z in support)
    return cs


def solve(cycles,seconds,workdir,proof=False,bad_pair=None,first_use=False):
    n=sum(cycles);square=permutation(cycles)
    top,cs=encode(square)
    suffix='' if bad_pair is None else '-bad-'+'-'.join(map(str,bad_pair))
    stem=workdir/('-'.join(map(str,cycles))+suffix)
    if bad_pair is not None:
        x,y=bad_pair
        p=lambda x,y,z:1+(x*n+y)*n+z
        cs.extend([-p(x,y,z),-p(square[x],square[y],square[z])] for z in range(n))
    if first_use:cs.extend(centralizer_first_use(square,bad_pair or ()))
    path=stem.with_suffix('.cnf')
    with path.open('w') as out:
        out.write(f'p cnf {top} {len(cs)}\n')
        for c in cs:out.write(' '.join(map(str,c))+' 0\n')
    record=dict(order=n,square_cycles=cycles,square_map=square,variables=top,clauses=len(cs),
                cnf_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),seconds_limit=seconds,
                scope='fixed square permutation only; no additional row normalization',
                proof_status='external search; no Lean replay')
    if bad_pair is not None:
        record.update(nonautomorphism_pair=bad_pair,
                      scope='fixed involutive square map and specified failure of multiplicativity')
    if first_use:
        record['centralizer_first_use']=True
        record['scope']='fixed square map with centralizer first-use normalization'+(
            ' and specified failure of multiplicativity' if bad_pair is not None else '')
    del cs
    command=['cadical','-t',str(seconds),str(path)]
    if proof:command[1:1]=['--lrat','--no-binary','--shrink=0'];command.append(str(stem.with_suffix('.lrat')))
    started=time.monotonic()
    cp=subprocess.run(command,capture_output=True,text=True)
    stem.with_suffix('.log').write_text(cp.stdout+cp.stderr)
    record.update(status={10:'SAT',20:'UNSAT'}.get(cp.returncode,'UNKNOWN'),
                  elapsed=time.monotonic()-started,exit_code=cp.returncode)
    if cp.returncode==10:
        vals={int(x) for line in cp.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:]}
        t=[[next(z for z in range(n) if 1+(x*n+y)*n+z in vals) for y in range(n)] for x in range(n)]
        assert [t[x][x] for x in range(n)]==square
        assert satisfies(*load_equations()[666],sum(t,[]),n)
        record['table']=t
    stem.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    print({k:v for k,v in record.items() if k!='table'},flush=True)
    return record


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--order',type=int,default=12)
    ap.add_argument('--cycles',type=lambda s:tuple(map(int,s.split(','))))
    ap.add_argument('--seconds',type=int,default=30)
    ap.add_argument('--workers',type=int,default=4)
    ap.add_argument('--workdir',type=Path,required=True)
    ap.add_argument('--proof',action='store_true')
    ap.add_argument('--nonautomorphism-pairs',action='store_true',
                    help='split nonautomorphic involutions into ordered-pair orbits')
    ap.add_argument('--first-use',action='store_true',help='normalize using involution centralizer swaps')
    args=ap.parse_args();args.workdir.mkdir(parents=True,exist_ok=True)
    cases=[args.cycles] if args.cycles else list(partitions(args.order))
    assert all(sum(c)==args.order and min(c)>0 for c in cases)
    tasks=[(c,p) for c in cases for p in
           (nonautomorphism_pairs(c) if args.nonautomorphism_pairs else [None])]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results=list(pool.map(lambda t:solve(t[0],args.seconds,args.workdir,args.proof,t[1],args.first_use),tasks))
    (args.workdir/'results.json').write_text(json.dumps(results,indent=2)+'\n')
