#!/usr/bin/env python3
"""Systematic small-source search for open finite term-definability arrows.

Orders <=3 use all labeled tables, reduced up to isomorphism. Larger orders
use a complete SMT encoding with lex-leader symmetry breaking, but explicit
time/model limits. Each source is screened by term enumeration and compatible
relations. A SAT relation relaxation is NOT a term-existence certificate.
Discovery negatives are research results until separately proved in Lean.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from pathlib import Path
import random
import time

import numpy as np
import z3

from spectrum_generate import load_equations, variables

ROOT = Path(__file__).resolve().parent.parent
EQUATIONS = load_equations()


def holds(eq, table):
    n = len(table)
    names = sorted(variables(eq[0]) | variables(eq[1]))
    assignments = np.array(list(product(range(n), repeat=len(names)))).T
    values = dict(zip(names, assignments))

    def ev(term):
        return values[term] if isinstance(term, str) else table[ev(term[0]), ev(term[1])]

    return bool(np.all(ev(eq[0]) == ev(eq[1])))


def eval_symbolic(term, values, op):
    return values[term] if isinstance(term, str) else op(
        eval_symbolic(term[0], values, op), eval_symbolic(term[1], values, op))


def relabel(table, permutation):
    p = np.array(permutation)
    inv = np.argsort(p)
    return p[table[np.ix_(inv, inv)]]


def small_bank(n):
    """Every isomorphism class, independently of the source equation."""
    seen = set()
    ps = list(permutations(range(n)))
    for flat in product(range(n), repeat=n*n):
        key = bytes(flat)
        if key in seen:
            continue
        table = np.array(flat, dtype=np.uint8).reshape(n, n)
        for p in ps:
            seen.add(relabel(table, p).astype(np.uint8).tobytes())
        yield table


def source_solver(source, n, timeout, symmetry='lex'):
    ctx = z3.Context()
    width = n.bit_length()
    domain = z3.BitVecSort(width, ctx=ctx)
    es = [z3.BitVecVal(i, width, ctx=ctx) for i in range(n)]
    op = z3.Function('source', domain, domain, domain)
    solver = z3.SolverFor('QF_UFBV', ctx=ctx)
    solver.set(timeout=timeout)
    cells = [op(x, y) for x in es for y in es]
    solver.add(*[z3.ULT(c, n) for c in cells])
    lhs, rhs = EQUATIONS[source-1]
    names = sorted(variables(lhs) | variables(rhs))
    for vals in product(es, repeat=len(names)):
        values = dict(zip(names, vals))
        solver.add(eval_symbolic(lhs, values, op) == eval_symbolic(rhs, values, op))
    if symmetry == 'orbit':
        return solver, es, cells
    # The output bounds make all ground source-law terms stay in {0,...,n-1}.
    # Keep precisely the lexicographically least table in each isomorphism class.
    for p in permutations(range(n)):
        if tuple(p) == tuple(range(n)):
            continue
        inv = np.argsort(p)
        transformed = []
        for x, y in product(range(n), repeat=2):
            cell = op(es[int(inv[x])], es[int(inv[y])])
            value = es[p[0]]
            for a in range(1, n):
                value = z3.If(cell == es[a], es[p[a]], value)
            transformed.append(value)
        le = z3.BoolVal(True, ctx=ctx)
        for a, b in reversed(list(zip(cells, transformed))):
            le = z3.Or(z3.ULT(a, b), z3.And(a == b, le))
        solver.add(le)
    return solver, es, cells


def term_screen(table, targets, limit):
    """Exact closure if exhausted; otherwise only the found terms are certified."""
    n = len(table)
    x, y = np.indices((n, n))
    ops = [x.astype(np.uint8), y.astype(np.uint8)]
    nodes = ['x', 'y']
    seen = {op.tobytes() for op in ops}
    found = {}
    pending = set(targets)

    def inspect(op, index):
        for target in list(pending):
            if holds(EQUATIONS[target-1], op):
                found[target] = index
                pending.remove(target)

    inspect(ops[0], 0)
    inspect(ops[1], 1)
    i = 0
    while i < len(ops) and pending:
        for j in range(i+1):
            for a, b in ((i, j), (j, i)):
                op = table[ops[a], ops[b]]
                key = op.tobytes()
                if key in seen:
                    continue
                seen.add(key)
                nodes.append([a, b])
                inspect(op, len(ops))
                ops.append(op)
                if len(ops) >= limit:
                    return found, nodes, False, len(ops)
        i += 1
    return found, nodes, i == len(ops), len(ops)


def compact_terms(nodes, roots):
    result = ['x', 'y']
    indices = {0: 0, 1: 1}

    def visit(i):
        if i not in indices:
            a, b = nodes[i]
            node = [visit(a), visit(b)]
            indices[i] = len(result)
            result.append(node)
        return indices[i]

    return {str(t): visit(i) for t, i in roots.items()}, result


def random_term_screen(table, targets, seed=0, steps=200000, seconds=10):
    """A positive-only search; failure says nothing about term existence."""
    n = len(table)
    x, y = np.indices((n, n))
    ops = [x.astype(np.uint8), y.astype(np.uint8)]
    nodes = ['x', 'y']
    seen = {op.tobytes() for op in ops}
    pending = set(targets)
    found = {}
    rng = random.Random(seed)
    start = time.monotonic()
    for _ in range(steps):
        if not pending or time.monotonic()-start > seconds:
            break
        a, b = rng.randrange(len(ops)), rng.randrange(len(ops))
        op = table[ops[a], ops[b]]
        key = op.tobytes()
        if key in seen:
            continue
        seen.add(key)
        nodes.append([a, b])
        for target in list(pending):
            if holds(EQUATIONS[target-1], op):
                found[target] = len(ops)
                pending.remove(target)
        ops.append(op)
    roots, compact = compact_terms(nodes, found)
    return dict(term_roots=roots, term_nodes=compact, unproved_targets=sorted(pending),
                enumerated_operations=len(ops), seconds=round(time.monotonic()-start, 3))


def guided_term_search(table, target, seed=0, steps=200000, seconds=2):
    """Positive-only search favoring terms with fewer failed law instances.

    Terms with the best score, tournament-selected terms, arbitrary terms, and
    the projections all remain available for composition. Keeping an arbitrary
    component avoids getting permanently trapped at a local optimum. A score
    above zero is only a search failure, never a negative result.
    """
    n = len(table)
    x, y = np.indices((n, n))
    ops, nodes = [x, y], ['x', 'y']
    seen = {op.tobytes() for op in ops}
    eq = EQUATIONS[target-1]
    names = sorted(variables(eq[0]) | variables(eq[1]))
    values = dict(zip(names, np.array(list(product(range(n), repeat=len(names)))).T))
    rng = random.Random(seed)

    def score(op):
        def ev(term):
            return values[term] if isinstance(term, str) else op[ev(term[0]), ev(term[1])]
        return int(np.count_nonzero(ev(eq[0]) != ev(eq[1])))

    scores = [score(op) for op in ops]
    best = min(scores)
    elite = [i for i, s in enumerate(scores) if s == best]
    found = {target: elite[0]} if best == 0 else {}
    start = time.monotonic()
    iterations = 0
    for _ in range(steps):
        if found or time.monotonic()-start >= seconds:
            break
        iterations += 1

        def pick():
            if rng.random() < 0.1:
                return rng.randrange(2)
            if rng.random() < 0.4:
                return rng.choice(elite)
            candidates = [rng.randrange(len(ops)) for _ in range(rng.choice([1, 2, 4, 8]))]
            return min(candidates, key=scores.__getitem__)

        a, b = pick(), pick()
        op = table[ops[a], ops[b]]
        key = op.tobytes()
        if key in seen:
            continue
        seen.add(key)
        s = score(op)
        i = len(ops)
        ops.append(op)
        nodes.append([a, b])
        scores.append(s)
        if s < best:
            best, elite = s, []
        if s == best:
            elite.append(i)
            if len(elite) > 1000:
                elite.pop(rng.randrange(len(elite)))
        if s == 0:
            found[target] = i
    roots, compact = compact_terms(nodes, found)
    return dict(term_roots=roots, term_nodes=compact, best_violations=best,
                unproved_targets=[] if found else [target], seed=seed, iterations=iterations,
                enumerated_operations=len(ops), seconds=round(time.monotonic()-start, 3))


def local_relations(table):
    """All two-coordinate restrictions generated by the two projections."""
    n = len(table)
    mult = [[int(table[a//n, b//n])*n + int(table[a % n, b % n])
             for b in range(n*n)] for a in range(n*n)]
    constraints = []
    for c, d in combinations_with_replacement(range(n*n), 2):
        elems = list(dict.fromkeys([(c//n)*n+d//n, (c % n)*n+d % n]))
        seen = set(elems)
        i = 0
        while i < len(elems):
            a = elems[i]
            for b in elems[:i+1]:
                for value in (mult[a][b], mult[b][a]):
                    if value not in seen:
                        seen.add(value)
                        elems.append(value)
            i += 1
        if len(seen) < n*n:
            constraints.append(dict(cells=[c, d], relation=[list(divmod(a, n)) for a in sorted(seen)]))
    return constraints


def diagonal_relation(table, limit=512):
    """All unary term maps, when closure finishes within the limit.

    A partial closure is never used as an obstruction: it need not contain
    the diagonal of every binary term.
    """
    n = len(table)
    elems = [tuple(range(n))]
    seen = set(elems)
    i = 0
    while i < len(elems):
        a = elems[i]
        for b in elems[:i+1]:
            for x, y in ((a, b), (b, a)):
                value = tuple(int(table[u, v]) for u, v in zip(x, y))
                if value not in seen:
                    seen.add(value)
                    elems.append(value)
                    if len(elems) >= limit:
                        return None
        i += 1
    if len(elems) == n**n:
        return None
    return dict(cells=[i*(n+1) for i in range(n)], relation=[list(v) for v in elems])


def relation_screen(table, targets, timeout, max_arity=2, refine_rounds=12):
    n = len(table)
    constraints = local_relations(table)
    diagonal = diagonal_relation(table)
    if diagonal is not None:
        constraints.append(diagonal)
    ctx = z3.Context()
    domain, es = z3.EnumSort('A', [f'e{i}' for i in range(n)], ctx=ctx)
    op = z3.Function('target', domain, domain, domain)
    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=timeout)
    tags = []
    for i, c in enumerate(constraints):
        values = [op(es[k//n], es[k % n]) for k in c['cells']]
        tag = z3.Bool(f'c{i}', ctx=ctx)
        predicate = z3.Or(*[z3.And(*[v == es[a] for v, a in zip(values, row)])
                            for row in c['relation']])
        solver.add(z3.Implies(tag, predicate))
        tags.append(tag)
    results = {}
    powers = {}
    for arity in range(3, max_arity+1):
        vectors = np.array(list(product(range(n), repeat=arity)), dtype=np.int32)
        weights = n**np.arange(arity-1, -1, -1)
        mult = (table[vectors[:, None, :], vectors[None, :, :]]*weights).sum(axis=2)
        powers[arity] = (vectors, weights, mult.tolist())

    def separating(candidate):
        for arity, (vectors, weights, mult) in powers.items():
            for cells in combinations(range(n*n), arity):
                a = sum((c//n)*int(w) for c, w in zip(cells, weights))
                b = sum((c % n)*int(w) for c, w in zip(cells, weights))
                needle = sum(candidate[c//n][c % n]*int(w) for c, w in zip(cells, weights))
                elems = list(dict.fromkeys([a, b]))
                seen = set(elems)
                i = 0
                while i < len(elems) and needle not in seen:
                    a = elems[i]
                    for b in elems[:i+1]:
                        for v in (mult[a][b], mult[b][a]):
                            if v not in seen:
                                seen.add(v)
                                elems.append(v)
                    i += 1
                if needle not in seen:
                    return dict(cells=list(cells), relation=vectors[sorted(seen)].tolist())
        return None

    for target in targets:
        solver.push()
        current_tags = tags.copy()
        current_constraints = constraints.copy()
        lhs, rhs = EQUATIONS[target-1]
        names = sorted(variables(lhs) | variables(rhs))
        for vals in product(es, repeat=len(names)):
            values = dict(zip(names, vals))
            solver.add(eval_symbolic(lhs, values, op) == eval_symbolic(rhs, values, op))
        record = {}
        for attempt in range(refine_rounds+1):
            status = solver.check(*current_tags)
            if status != z3.sat:
                break
            m = solver.model()
            ix = {str(e): i for i, e in enumerate(es)}
            candidate = [[ix[str(m.eval(op(x, y)))] for y in es] for x in es]
            if attempt == refine_rounds:
                record['refinement_limit'] = True
                break
            extra = separating(candidate)
            if extra is None:
                record['candidate_passes_arity'] = max_arity
                break
            values = [op(es[k//n], es[k % n]) for k in extra['cells']]
            predicate = z3.Or(*[z3.And(*[v == es[a] for v, a in zip(values, row)])
                                for row in extra['relation']])
            tag = z3.Bool(f'c{len(current_tags)}', ctx=ctx)
            solver.add(z3.Implies(tag, predicate))
            current_tags.append(tag)
            current_constraints.append(extra)
        record['status'] = str(status)
        record['added_relations'] = current_constraints[len(constraints):]
        if status == z3.unsat:
            core = [int(str(t)[1:]) for t in solver.unsat_core()]
            record['constraints'] = [current_constraints[i] for i in core]
        elif status == z3.sat:
            record['relaxed_target'] = candidate
        else:
            record['reason'] = solver.reason_unknown()
        results[target] = record
        solver.pop()
    return results


def sweep_job(job):
    source, n, targets, config = job
    output = Path(config['output'])
    path = output / f'E{source}_n{n}.json'
    previous = json.loads(path.read_text()) if path.exists() else None
    if previous and not config['rerun'] and not config.get('resume'):
        return json.loads(path.read_text())['summary']
    if previous and config.get('resume') and previous['summary']['source_enumeration'] in (
            'exhausted', 'all_targets_refuted'):
        return previous['summary']
    start = time.monotonic()
    summary = dict(source=source, order=n, targets=targets, models=0,
                   source_enumeration='not_started', outcomes={str(t): dict(
                       term_found=0, exact_clone_negative=0, relation_negative=0,
                       relation_sat=0, relation_unknown=0) for t in targets})
    records = []
    unresolved = set(targets)
    prior_seconds = 0
    if previous and config.get('resume'):
        assert previous['summary']['targets'] == targets
        summary = previous['summary']
        records = previous['models']
        unresolved = set(summary['unrefuted_targets'])
        prior_seconds = summary['seconds']
    if n <= 3:
        models = [m for m in small_bank(n) if holds(EQUATIONS[source-1], m)]
        summary['total_isomorphism_classes'] = len(models)
        iterator = iter(models)
        for _ in records:
            next(iterator)
        solver = None
    else:
        symmetry = config.get('symmetry', 'lex')
        solver, es, cells = source_solver(source, n, config['solver_ms'], symmetry)

        def block(table):
            orbit = {tuple(table.flat)} if symmetry == 'lex' else {
                tuple(relabel(table, p).flat) for p in permutations(range(n))}
            for flat in orbit:
                solver.add(z3.Or(*[c != es[int(v)] for c, v in zip(cells, flat)]))

        for r in records:
            block(np.array(r['table'], dtype=np.uint8))
    while True:
        if summary['models'] >= config['max_models']:
            summary['source_enumeration'] = 'model_limit'
            break
        if time.monotonic()-start >= config['seconds']:
            summary['source_enumeration'] = 'time_limit'
            break
        if solver is None:
            table = next(iterator, None)
            if table is None:
                summary['source_enumeration'] = 'exhausted'
                break
        else:
            result = solver.check()
            if result != z3.sat:
                summary['source_enumeration'] = 'exhausted' if result == z3.unsat else 'solver_unknown'
                if result == z3.unknown:
                    summary['solver_reason'] = solver.reason_unknown()
                break
            m = solver.model()
            ix = {str(e): i for i, e in enumerate(es)}
            flat = [ix[str(m.eval(c))] for c in cells]
            table = np.array(flat, dtype=np.uint8).reshape(n, n)
            assert holds(EQUATIONS[source-1], table)
            if symmetry == 'orbit':
                flat = min(tuple(relabel(table, p).flat) for p in permutations(range(n)))
                table = np.array(flat, dtype=np.uint8).reshape(n, n)
            assert all(tuple(table.flat) <= tuple(relabel(table, p).flat)
                       for p in permutations(range(n)))
            block(table)
        summary['models'] += 1
        found, nodes, complete, size = term_screen(table, unresolved, config['clone_limit'])
        record = dict(table=table.tolist(), term_roots={str(k): v for k, v in found.items()},
                      term_nodes=nodes, clone_exhausted=complete, enumerated_operations=size)
        for target in found:
            summary['outcomes'][str(target)]['term_found'] += 1
        pending = unresolved-set(found)
        if complete and pending:
            for target in pending:
                summary['outcomes'][str(target)]['exact_clone_negative'] += 1
            record['exact_clone_negatives'] = sorted(pending)
            unresolved -= pending
        elif pending:
            rr = relation_screen(table, sorted(pending), config['solver_ms'])
            record['relations'] = {str(k): v for k, v in rr.items()}
            for target, result in rr.items():
                status = result['status']
                key = {'unsat': 'relation_negative', 'sat': 'relation_sat', 'unknown': 'relation_unknown'}[status]
                summary['outcomes'][str(target)][key] += 1
                if status == 'unsat':
                    unresolved.remove(target)
        records.append(record)
        if not unresolved:
            summary['source_enumeration'] = 'all_targets_refuted'
            break
    summary['seconds'] = round(prior_seconds+time.monotonic()-start, 3)
    summary['unrefuted_targets'] = sorted(unresolved)
    data = dict(schema=1, summary=summary, config=config, models=records)
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(data, separators=(',', ':'))+'\n')
    tmp.replace(path)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[2, 3, 4, 5])
    parser.add_argument('--sources', nargs='+', type=int)
    parser.add_argument('--seconds', type=float, default=60)
    parser.add_argument('--solver-ms', type=int, default=5000)
    parser.add_argument('--max-models', type=int, default=500)
    parser.add_argument('--clone-limit', type=int, default=128)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--symmetry', choices=['lex', 'orbit'], default='lex')
    parser.add_argument('--output', default='.cache/definability-small-sweep-20261012')
    parser.add_argument('--rerun', action='store_true')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    snapshot = json.loads((ROOT/'docs/definability_open/snapshot.json').read_text())
    rows = snapshot['boards']['termDefinable/fin']['open_rows']
    targets = {int(s): sorted(t for ts in profiles.values() for t in ts) for s, profiles in rows.items()}
    if args.sources:
        targets = {s: targets[s] for s in args.sources}
    config = vars(args)
    jobs = [(s, n, ts, config) for n in args.orders for s, ts in targets.items()]
    summaries = {(d['summary']['order'], d['summary']['source']): d['summary']
                 for p in output.glob('E*_n*.json') for d in [json.loads(p.read_text())]}
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(sweep_job, job) for job in jobs]
        for future in as_completed(futures):
            summary = future.result()
            summaries[(summary['order'], summary['source'])] = summary
            discoveries = [t for t, c in summary['outcomes'].items()
                           if c['exact_clone_negative'] or c['relation_negative']]
            print(f'E{summary["source"]} n={summary["order"]}: {summary["models"]} models, '
                  f'{summary["source_enumeration"]}, negatives={discoveries}, '
                  f'{summary["seconds"]}s', flush=True)
            (output/'summary.json').write_text(json.dumps(dict(
                source_fingerprint=snapshot['fingerprint'], config=config,
                jobs=sorted(summaries.values(), key=lambda x: (x['order'], x['source']))), indent=2)+'\n')


if __name__ == '__main__':
    main()
