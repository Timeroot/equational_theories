#!/usr/bin/env python3
"""Bounded SAT countermodel searches for a saved E872 image candidate.

The encoder uses one-hot multiplication tables and shared term evaluations.
Unit failures are normalized to 0*0=1: a failing point cannot be idempotent.
A block size restricts to row-bijective operations preserving the right input's
block, with arbitrary permutations inside each block. UNSAT is research evidence,
not a Lean proof. Every positive table is independently checked before saving.
"""
import argparse
import itertools
import json
import multiprocessing as mp
from pathlib import Path
import time

from pysat.formula import CNF
from pysat.solvers import Solver

from parastrophe_e872_compression import BASE, Model, core
from parastrophe_rewrite_replay import freeze


def encode(n, term, failure, translations="all", block=None):
    if n < 2 or translations not in ("all", "left", "quasigroup"):
        raise ValueError("Expected order >= 2 and a supported translation mode")
    if failure not in ("unit", "cross", "collision0", "collision2"):
        raise ValueError("Unsupported failure")
    if failure == "collision2" and n < 3:
        raise ValueError("The disjoint-row collision needs three elements")
    if block is not None and (block < 2 or n % block):
        raise ValueError("Block size must divide the order and be at least two")
    cnf = CNF()
    nextvar = 0
    allowed, memo = {}, {}

    def value(colour=None):
        nonlocal nextvar
        indices = list(range(n)) if colour is None else list(range(colour*block, (colour+1)*block))
        literals = list(range(nextvar+1, nextvar+len(indices)+1))
        nextvar += len(indices)
        by_index = dict(zip(indices, literals))
        v = tuple(by_index.get(k) for k in range(n))
        allowed[v] = indices
        cnf.append(literals)
        for a, b in itertools.combinations(literals, 2):
            cnf.append([-a, -b])
        return v

    table = [[value(y//block if block else None) for y in range(n)] for x in range(n)]

    def apply(a, b):
        if isinstance(a, int) and isinstance(b, int):
            return table[a][b]
        if (a,b) in memo:
            return memo[a,b]
        colour = (b//block if isinstance(b, int) else allowed[b][0]//block) if block else None
        v = value(colour)
        memo[a,b] = v
        aa = [(a,None)] if isinstance(a,int) else [(i,a[i]) for i in allowed[a]]
        bb = [(b,None)] if isinstance(b,int) else [(j,b[j]) for j in allowed[b]]
        for i, li in aa:
            for j, lj in bb:
                prefix = ([-li] if li is not None else []) + ([-lj] if lj is not None else [])
                for k in allowed[v]:
                    cnf.append(prefix+[-table[i][j][k], v[k]])
        return v

    def evaluate(t, xyz):
        return xyz[t] if isinstance(t,int) else apply(evaluate(t[0],xyz), evaluate(t[1],xyz))

    def require_value(v, k):
        if isinstance(v, int):
            if v != k:
                cnf.append([])
        elif v[k] is None:
            cnf.append([])
        else:
            cnf.append([v[k]])

    if translations in ("left", "quasigroup") or block:
        for x, k in itertools.product(range(n), repeat=2):
            for a,b in itertools.combinations([a for a in range(n) if table[x][a][k] is not None],2):
                cnf.append([-table[x][a][k], -table[x][b][k]])
    if translations == "quasigroup":
        for y,k in itertools.product(range(n), repeat=2):
            for a,b in itertools.combinations([a for a in range(n) if table[a][y][k] is not None],2):
                cnf.append([-table[a][y][k], -table[b][y][k]])
    if failure.startswith("collision"):
        row = int(failure[-1])
        for k in allowed[table[row][0]]:
            cnf.append([-table[row][0][k], table[row][1][k]])
            cnf.append([-table[row][1][k], table[row][0][k]])
    elif failure == "unit":
        cnf.append([-evaluate((0,core(0)),(0,0,0))[0]])
        cnf.append([table[0][0][1]])
    else:
        for x in range(n):
            require_value(evaluate((0,core(0)),(x,x,x)),x)
        cnf.append([-evaluate(BASE,(0,y,0))[0] for y in range(n)])
    for xyz in itertools.product(range(n),repeat=3):
        require_value(evaluate(term,xyz),xyz[0])
    return cnf, table


def _worker(connection, term, n, failure, translations, block, solver):
    started = time.monotonic()
    cnf, variables = encode(n,term,failure,translations,block)
    metadata = {"variables": cnf.nv, "clauses": len(cnf.clauses)}
    connection.send(metadata)
    with Solver(name=solver, bootstrap_with=cnf) as engine:
        answer = engine.solve()
        result = dict(metadata, status="sat" if answer else "unsat", stats=engine.accum_stats())
        if answer:
            true = set(lit for lit in engine.get_model() if lit > 0)
            table = [[next(k for k in range(n) if variables[x][y][k] in true)
                      for y in range(n)] for x in range(n)]
            model = Model(table)
            assert model.holds(term) and not model.is_image()
            result["table"] = table
    result["seconds"] = time.monotonic()-started
    connection.send(result)
    connection.close()


def search(term, n, failure, translations="all", block=None, solver="cadical195", seconds=60):
    ctx = mp.get_context("spawn")
    receive, send = ctx.Pipe(duplex=False)
    process = ctx.Process(target=_worker, args=(send,term,n,failure,translations,block,solver))
    start = time.monotonic()
    process.start()
    send.close()
    process.join(seconds)
    timed_out = process.is_alive()
    if timed_out:
        process.terminate()
        process.join()
    result = {"status": "timeout" if timed_out else "error", "seconds": time.monotonic()-start}
    while receive.poll():
        try:
            result.update(receive.recv())
        except EOFError:
            break
    receive.close()
    return dict(result, order=n, failure=failure, translations=translations, block_size=block,
                solver=solver, time_limit_seconds=seconds, lean_status="not formalized")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record",type=Path)
    parser.add_argument("--candidate",type=int,default=24237)
    parser.add_argument("--order",type=int,required=True)
    parser.add_argument("--failure",choices=["unit","cross","collision0","collision2"],required=True)
    parser.add_argument("--translations",choices=["all","left","quasigroup"],default="all")
    parser.add_argument("--block-size",type=int)
    parser.add_argument("--solver",default="cadical195")
    parser.add_argument("--seconds",type=float,default=60)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    record=json.loads(args.record.read_text())
    candidate=next(c for c in record["rewrite_replay"]["unresolved"] if c["index"]==args.candidate)
    result=search(freeze(candidate["term"]),args.order,args.failure,args.translations,
                  args.block_size,args.solver,args.seconds)
    result["candidate"]=args.candidate
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="table"}))


if __name__=="__main__":
    main()
