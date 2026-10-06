#!/usr/bin/env python3
"""Search E467 with its squaring permutation fixed, eliminating the auxiliary table.

Research only: UNSAT results are external, and timeouts prove nothing. All
returned tables are checked against the original identity. The finite algebra
is in Spectrum/Equation467Translations.lean. The order-sixteen base encoding
and first-use normalization are formalized in Spectrum/Equation467/OrderSixteen;
the optional experimental variants are still research tools.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import time

from spectrum_generate import load_equations, satisfies


def cycle_types(n):
    def parts(n, minimum, k):
        if n == 0:
            yield ()
        for j in range(minimum, n+1):
            if j != 1 and j < k:
                continue
            for rest in parts(n-j, j, k):
                yield (j,)+rest
    return [(k,)+p for k in range(4,n+1) for p in parts(n-k,1,k)]


def permutation(lengths):
    out, offset = [], 0
    for k in lengths:
        out += list(range(offset+1,offset+k))+[offset]
        offset += k
    return out


def clauses(d, first_use=True, fixed_anchors=0):
    n=len(d); r=range(n); inv=[d.index(x) for x in r]
    p=lambda x,y,z: 1+(x*n+y)*n+z
    cs=[]
    def one(v):
        cs.append(v)
        cs.extend([-a,-b] for a,b in combinations(v,2))
    for x,y in product(r,repeat=2):
        one([p(x,y,z) for z in r])
        one([p(x,z,y) for z in r])
        one([p(z,x,y) for z in r])
    for x in r:
        cs.extend([[p(x,x,d[x])],[p(x,d[x],inv[x])],
                   [p(x,d[d[x]],d[d[x]])]])
        for y in r:
            if y != d[d[x]]:
                cs.append([-p(x,y,y)])
        for y,z in combinations(r,2):
            cs.append([-p(x,y,z),-p(x,z,y)])
    # P(x,P(x,y)) = L_{D^{-1}y}^{-1}(x). Each side uniquely determines
    # the intermediate value, so all three cancellation clauses are valid.
    for x,y,a,b in product(r,repeat=4):
        aa,bb,cc=p(x,y,a),p(x,a,b),p(inv[y],b,x)
        cs.extend([[-aa,-bb,cc],[-aa,bb,-cc],[aa,-bb,-cc]])
    if first_use:
        # The D-cycle through zero is fixed pointwise by its stabilizer.
        # Normalize first appearances in row zero within those columns.
        k=1
        while d[k-1]!=0:k+=1
        assert all(d[k+j] == k+j for j in range(fixed_anchors))
        start=k+fixed_anchors
        groups=[]
        while start<n:
            length=1
            while d[start+length-1]!=start:length+=1
            end=start+length
            while end<n and permutation_cycle_length(d,end)==length:end+=length
            groups.extend((j,end) for j in range(start,end,length));start=end
        for y in range(k):
            for start,end in groups:
                seen=[p(0,j,z) for j in range(y) for z in range(start,end)]
                cs.extend([-p(0,y,z)]+seen for z in range(start+1,end))
    return [c for c in cs if not any(-v in c for v in c)]


def permutation_cycle_length(d,x):
    y=d[x];k=1
    while y!=x:y=d[y];k+=1
    return k


def first_use_cells(n, k, fixed_anchors=0):
    """Inspect fixed inputs first, then grow the square of inspected inputs."""
    start = k + fixed_anchors
    initial = [(0, y) for y in range(k)]
    return (initial + [(x, y) for x, y in product(range(start), repeat=2)
                       if (x, y) not in initial] +
            sorted(((x, y) for x, y in product(range(n), repeat=2)
                    if max(x, y) >= start), key=lambda xy: (max(xy), xy)))


def full_first_use_clauses(n, k, fixed_anchors=0):
    """Normalize the freely permutable fixed points throughout the table.

    Before label z-1 has occurred as an input, an output z requires an
    earlier output z-1. A lexicographically minimal relabelling fixing the
    initial k+fixed_anchors labels has this property: otherwise swapping
    the two labels makes its first changed entry smaller. The general
    argument is proved in Spectrum/FiniteSearch/FirstUse.lean.

    This applies only when all squaring cycles after the first are singletons.
    """
    p = lambda x,y,z: 1+(x*n+y)*n+z
    start = k + fixed_anchors
    cs, seen = [], []
    for x, y in first_use_cells(n, k, fixed_anchors):
        for z in range(max(start, max(x,y)+1)+1, n):
            cs.append([-p(x,y,z)] + [p(a,b,z-1) for a,b in seen])
        seen.append((x,y))
    return cs


def run(n,lengths,seconds,out,row_return=None,idempotent_pair=False,full_first_use=False):
    tag='-'.join(map(str,lengths))
    if row_return is not None:tag+=f'-return-{row_return}'
    if idempotent_pair:tag+='-idempotent-pair'
    if full_first_use:tag+='-full-first-use'
    cnf=out/(tag+'.cnf');log=out/(tag+'.log')
    d=permutation(lengths);cs=clauses(d,fixed_anchors=2 if idempotent_pair else 0)
    if full_first_use:
        assert all(v == 1 for v in lengths[1:])
        cs += full_first_use_clauses(n,lengths[0],2 if idempotent_pair else 0)
    if row_return is not None:cs.append([1+d.index(0)*n+row_return])
    if idempotent_pair:
        k=lengths[0]
        assert k>=4 and all(v==1 for v in lengths[1:]) and 2*k<n
        cs.append([1+(k*n+k+1)*n])
    data=(f'p cnf {n**3} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()
    cnf.write_bytes(data)
    start=time.monotonic()
    with log.open('w') as f:
        proc=subprocess.run(['cadical','-t',str(seconds),str(cnf)],stdout=f,stderr=f)
    result=dict(law=467,order=n,square_cycles=lengths,first_use=True,
                status={0:'TIMEOUT',10:'SAT',20:'UNSAT'}.get(proc.returncode,'UNKNOWN'),
                seconds=time.monotonic()-start,time_limit=seconds,lean_checked=False,
                cnf_sha256=hashlib.sha256(data).hexdigest())
    if full_first_use:result['full_first_use']=True
    if row_return is not None:result['row_return']=row_return
    if idempotent_pair:result['idempotent_pair']=[lengths[0],lengths[0]+1,0]
    if proc.returncode==10:
        positive={int(v) for line in log.read_text().splitlines() if line.startswith('v ')
                  for v in line[2:].split() if int(v)>0}
        table=[next(z for z in range(n) if 1+(x*n+y)*n+z in positive)
               for x,y in product(range(n),repeat=2)]
        assert satisfies(*load_equations()[466],table,n)
        result['table']=table
    (out/(tag+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    cnf.unlink()
    print(json.dumps(result),flush=True)
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--order',type=int,default=16)
    ap.add_argument('--seconds',type=int,default=15)
    ap.add_argument('--workers',type=int,default=2)
    ap.add_argument('--cycles',help='one prescribed squaring cycle type')
    ap.add_argument('--row-return',type=int,help='fix P(0,D⁻¹(0)), the last point of its four-cycle')
    ap.add_argument('--idempotent-pair',action='store_true',
                    help='for one moving cycle and a majority of fixed points, fix two idempotents with product zero')
    ap.add_argument('--full-first-use',action='store_true',
                    help='normalize all free fixed-point labels by first occurrence throughout the table')
    ap.add_argument('--output',type=Path,default=Path('.cache/e467-square'))
    a=ap.parse_args()
    if min(a.order,a.seconds,a.workers)<1:ap.error('positive arguments required')
    cases=[tuple(map(int,a.cycles.split(',')))] if a.cycles else cycle_types(a.order)
    if any(min(c)<1 or sum(c)!=a.order for c in cases):ap.error('invalid cycle lengths')
    if a.full_first_use and any(any(v!=1 for v in c[1:]) for c in cases):
        ap.error('full-first-use requires at most one moving squaring cycle')
    if a.row_return is not None and not 0<=a.row_return<a.order:ap.error('invalid row return')
    if a.idempotent_pair and (not a.cycles or a.row_return is not None or
            cases[0][0]<4 or any(v!=1 for v in cases[0][1:]) or 2*cases[0][0]>=a.order):
        ap.error('idempotent-pair normalization requires one moving cycle, a majority of fixed points, and no prescribed return')
    a.output.mkdir(parents=True,exist_ok=True)
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        results=list(pool.map(lambda c:run(a.order,c,a.seconds,a.output,a.row_return,
                                         a.idempotent_pair,a.full_first_use),cases))
    (a.output/'summary.json').write_text(json.dumps(results,indent=2)+'\n')


if __name__=='__main__':main()
