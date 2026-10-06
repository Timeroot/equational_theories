#!/usr/bin/env python3
"""Patient Mace4 searches for E667, with exact-domain and explicit scope records.

The default order-12 suite covers the two broad branches (with an idempotent,
without one), plus the six surviving mixed-idempotent row shapes. LNH is off:
we impose only explicitly justified row labels. Returned tables are independently
checked against E667; only Mace4's exhaustive exit counts as an exclusion.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import time

from spectrum_generate import load_equations, satisfies

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MACE = ROOT / '.cache/e667-subclasses/LADR-2009-11A/bin/mace4'
ROWS = [(1,3,3,5),(1,3,4,4),(1,3,8),(1,4,7),(1,5,6),(1,11)]


def problem(n, mode, seconds, memory, row=None, selection=4):
    out = [f'assign(domain_size, {n}).', f'assign(end_size, {n}).',
           f'assign(max_seconds, {seconds}).', f'assign(max_megs, {memory}).',
           f'assign(selection_measure, {selection}).', 'assign(max_models, 1).',
           'clear(lnh).', 'formulas(assumptions).',
           'f(y,f(x,f(f(x,x),y)))=x.',
           'f(x,y)=f(x,z) -> y=z.', 'f(y,x)=f(z,x) -> y=z.',
           'f(x,f(x,f(x,x)))=x -> f(x,x)=x.',
           'f(x,f(x,x))=x -> f(f(x,x),f(x,x))=f(x,x).',
           'all e all x (f(e,e)=e -> (f(x,x)=e <-> f(e,f(e,x))=x)).',
           'all e all x (f(e,e)=e & f(x,x)=e -> f(f(e,x),f(e,x))=e).']
    if n % 3 == 0:
        for z in range(n):
            out.append(' | '.join(f'f({x},{x})!={z}' for x in range(n)) + '.')
    if n == 12:
        out.append(' | '.join(f'f({x},{x})!={x}' for x in range(n)) + '.')
        for e in range(n):
            out.append(' | '.join(f'f({x},{e})!={x}' for x in range(n)) + '.')
    if mode == 'one-idempotent':
        out.append('f(0,0)=0.')
    elif mode == 'idempotent-free':
        out.append('f(x,x)!=x.')
        # Some row has a fixed point in any finite Latin square.
        out.append(' | '.join(f'f(0,{x})={x}' for x in range(n)) + '.')
    elif mode == 'idempotent':
        out.append('f(x,x)=x.')
    elif mode == 'right-identity':
        out.append('f(x,0)=x.')
    elif mode == 'commutative':
        out.append('f(x,y)=f(y,x).')
    elif mode != 'all':
        raise ValueError(mode)
    if row:
        perm, offset = [], 0
        for length in row:
            perm.extend(list(range(offset+1, offset+length)) + [offset])
            offset += length
        assert offset == n
        out.extend(f'f(0,{y})={z}.' for y,z in enumerate(perm))
    else:
        # Proven chain labelling of row zero, with zero fixed by the relabelling.
        for y in range(n-2):
            out.append(' | '.join(f'f(0,{y})={z}' for z in range(y+2)) + '.')
    out += ['end_of_list.', '']
    return '\n'.join(out)


def run(args, task):
    mode, row, seconds = task
    label = mode + ('-'+'-'.join(map(str,row)) if row else '')
    base = args.output / label
    inp = problem(args.order, mode, seconds, args.memory, row, args.selection)
    base.with_suffix('.in').write_text(inp)
    command = [str(args.mace), '-f', str(base.with_suffix('.in'))]
    started = time.monotonic()
    print(json.dumps(dict(event='start',case=label,order=args.order,cpu_limit=seconds)),flush=True)
    with base.with_suffix('.out').open('w') as log:
        result = subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
    output = base.with_suffix('.out').read_text()
    match = re.search(r'function\(f\(_,_\),\s*\[([^]]*)\]', output, re.S)
    status = 'SAT' if match else 'UNSAT' if result.returncode == 2 else 'UNKNOWN'
    termination = re.findall(r'exit \(([^)]+)\)',output)
    cpu = re.findall(r'User_CPU=([0-9.]+)',output)
    record = dict(law=667,order=args.order,mode=mode,cycles=row,status=status,
                  cpu_limit=seconds,wall_seconds=round(time.monotonic()-started,3),
                  cpu_seconds=float(cpu[-1]) if cpu else None,
                  memory_limit_mb=args.memory,selection_measure=args.selection,
                  exit_code=result.returncode,termination=termination[-1] if termination else 'unrecognized',
                  input_sha256=sha256(inp.encode()).hexdigest(),
                  proof_status='external Mace4 search; no Lean refutation')
    if match:
        table = [int(x) for x in re.findall(r'\d+',match.group(1))]
        assert len(table)==args.order**2
        assert satisfies(*load_equations()[666],table,args.order)
        record['table']=table
        record['independently_checked_original_law']=True
    elif result.returncode not in (2,5,7):
        raise RuntimeError(f'Mace4 error in {label}: exit {result.returncode}; inspect {base}.out')
    base.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    return record


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--order',type=int,default=12)
    ap.add_argument('--mode',choices=['suite','all','one-idempotent','idempotent-free','idempotent','commutative','right-identity'],default='suite')
    ap.add_argument('--seconds',type=int,default=1800)
    ap.add_argument('--row-seconds',type=int,default=600)
    ap.add_argument('--workers',type=int,default=4)
    ap.add_argument('--memory',type=int,default=2048)
    ap.add_argument('--selection',type=int,choices=range(5),default=4)
    ap.add_argument('--mace',type=Path,default=DEFAULT_MACE)
    ap.add_argument('--output',type=Path,default=Path('.cache/e667-mace4'))
    args=ap.parse_args()
    if min(args.order,args.seconds,args.row_seconds,args.workers,args.memory)<1:
        ap.error('bounds must be positive')
    if args.mode=='suite' and args.order!=12:
        ap.error('the six-row suite is specific to order twelve')
    args.output.mkdir(parents=True,exist_ok=True)
    tasks=([('one-idempotent',None,args.seconds),('idempotent-free',None,args.seconds)]+
           [('one-idempotent',r,args.row_seconds) for r in ROWS]) if args.mode=='suite' else [(args.mode,None,args.seconds)]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        records=list(pool.map(lambda t:run(args,t),tasks))
    (args.output/'results.json').write_text(json.dumps(records,indent=2)+'\n')


if __name__=='__main__':
    main()
