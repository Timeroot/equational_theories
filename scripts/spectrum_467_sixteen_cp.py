#!/usr/bin/env python3
"""Independent CP-SAT encoding of the two final E467 order-sixteen cases.

The default runs both remaining squaring types with separate element/Latin
constraints and a separately implemented first-occurrence normalization.
INFEASIBLE is external evidence, not an end-to-end Lean theorem.
"""
import argparse
import json,time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from ortools.sat.python import cp_model

def job(k, seconds, workers, output):
    n=16;d=list(range(1,k))+[0]+list(range(k,n)); inv=[d.index(i) for i in range(n)]
    m=cp_model.CpModel(); p=[[m.new_int_var(0,n-1,f'p{x}_{y}') for y in range(n)] for x in range(n)]
    q=[[m.new_int_var(0,n-1,f'q{x}_{y}') for y in range(n)] for x in range(n)]
    for x in range(n):
        m.add_all_different(p[x]);m.add_all_different([p[y][x] for y in range(n)])
        m.add_all_different(q[x]);m.add_all_different([q[y][x] for y in range(n)])
        m.add(p[x][x]==d[x]);m.add(p[x][d[x]]==inv[x]);m.add(p[x][d[d[x]]]==d[d[x]])
        for y in range(n):
            m.add_element(p[x][y],p[x],q[x][y])
            m.add_element(q[x][y],p[inv[y]],x)
            if y!=d[d[x]]:m.add(p[x][y]!=y);m.add(q[x][y]!=y)
    # Independent implementation of first-encounter normalization: for each
    # free label z, the first position producing z precedes the first producing
    # z+1, unless z itself has already occurred as an input.
    initial=[(0,y) for y in range(k)]
    cells=initial+[(x,y) for x in range(k) for y in range(k) if (x,y) not in initial]
    cells+=sorted([(x,y) for x in range(n) for y in range(n) if max(x,y)>=k],key=lambda xy:(max(xy),xy))
    vals=[p[x][y] for x,y in cells]
    for z in range(k,n-1):
        before=[]
        for i,(x,y) in enumerate(cells):
            if max(x,y)>=z:break
            prev=m.new_bool_var(f'is{z}_{i}');m.add(vals[i]==z).only_enforce_if(prev);m.add(vals[i]!=z).only_enforce_if(prev.negated())
            nxt=m.new_bool_var(f'is{z+1}_{i}');m.add(vals[i]==z+1).only_enforce_if(nxt);m.add(vals[i]!=z+1).only_enforce_if(nxt.negated())
            m.add_bool_or(before+[nxt.negated()]);before.append(prev)
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=seconds;s.parameters.num_search_workers=workers
    t=time.monotonic();status=s.solve(m)
    r=dict(order=n,law=467,k=k,status=s.status_name(status),seconds=time.monotonic()-t,solver='OR-Tools CP-SAT',lean_checked=False,branches=s.num_branches,conflicts=s.num_conflicts)
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        from spectrum_generate import load_equations,satisfies
        table=[s.value(p[x][y]) for x in range(n) for y in range(n)]
        assert satisfies(*load_equations()[466],table,n)
        r['table']=table
    (output/f'cp-k{k}.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
    return r
if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seconds',type=int,default=180)
    ap.add_argument('--workers',type=int,default=4,help='CP-SAT workers for each case')
    ap.add_argument('--cycle',type=int,choices=(4,5))
    ap.add_argument('--output',type=Path,default=Path('.cache/e467-sixteen-cp'))
    args=ap.parse_args()
    if min(args.seconds,args.workers)<1:ap.error('positive limits required')
    args.output.mkdir(parents=True,exist_ok=True)
    with ThreadPoolExecutor(max_workers=2) as pool:
        list(pool.map(lambda k:job(k,args.seconds,args.workers,args.output),
                                                                [args.cycle] if args.cycle else [4,5]))
