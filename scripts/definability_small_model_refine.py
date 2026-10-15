#!/usr/bin/env python3
"""Continue the explicitly unresolved finite-model term tests in the inventory.

Successful terms and majority-interpolation recipes are replayable certificates.
Limits on any search are inconclusive. This does not enumerate new source models
or establish a definability arrow for all models of a law.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import gzip
from itertools import product
import json
from pathlib import Path
import subprocess

import numpy as np

from definability_majority_interpolation import (
    Terms, boolean_majority, check_interpolation, encoded_majority)
from definability_small_model_sweep import EQUATIONS, ROOT, guided_term_search, holds, relation_screen


def compile_searches():
    outputs = []
    for name in ('definability_small_term_search', 'definability_subpower_search'):
        source, binary = ROOT/'scripts'/f'{name}.cpp', ROOT/'.cache'/name
        binary.parent.mkdir(parents=True, exist_ok=True)
        if not binary.exists() or binary.stat().st_mtime < source.stat().st_mtime:
            subprocess.run(['g++', '-O3', '-std=c++17', str(source), '-o', str(binary)], check=True)
        outputs.append(str(binary))
    return outputs


def run_search(binary, inputs):
    result = subprocess.run([binary], input=' '.join(map(str, inputs)), text=True,
                            capture_output=True, check=True)
    return json.loads(result.stdout)


def lattice_majority(table, binary, seconds):
    """Find min/max on the three source idempotents, then encode and decode."""
    n = len(table)
    domain = [x for x in range(n) if table[x][x] == x]
    if len(domain) != 3:
        return None
    inputs = list(product(domain, repeat=2))
    seeds = list(zip(*inputs))
    gates = []
    for op in (min, max):
        goal = list(map(op, inputs))
        args = [n, 2, len(inputs), 20000, seconds,
                *[v for seed in seeds for v in seed], *goal,
                *[v for row in table for v in row]]
        gate = run_search(binary, args)
        if gate['root'] < 0:
            return None
        gates.append(gate)
    dag = Terms(table, 3)

    def gate(i, a, b):
        return dag.subst(gates[i]['nodes'], gates[i]['root'], [a, b])

    root = gate(1, gate(0, 0, 1), gate(1, gate(0, 0, 2), gate(0, 1, 2)))
    # encoded_majority independently checks the claimed restricted majority.
    return encoded_majority(table, domain, dag.pack(root), seconds=seconds)


def pending_cases(data):
    def key(table):
        return tuple(v for row in table for v in row)

    found = set()
    for r in [r for j in data['jobs'] for r in j['models']] + data['additional_terms']:
        found.update((key(r['table']), int(t)) for t in r['term_roots'])
    for r in data.get('additional_interpolations', []):
        found.update((key(r['table']), int(t)) for t in r['interpolation_targets'])
    cases = {}
    for job in data['jobs']:
        summary = job['summary']
        for r in job['models']:
            k = key(r['table'])
            targets = [t for t in summary['targets'] if (k, t) not in found]
            if not targets:
                continue
            case = cases.setdefault(k, dict(table=r['table'], sources=set(), targets=set(), candidates={}))
            case['sources'].add(summary['source'])
            case['targets'].update(targets)
            for t in targets:
                candidate = r.get('relations', {}).get(str(t), {}).get('relaxed_target')
                if candidate is not None:
                    case['candidates'][str(t)] = candidate
    return [dict(r, sources=sorted(r['sources']), targets=sorted(r['targets'])) for r in cases.values()]


def refine(job):
    index, case, config, binaries = job
    table, targets = case['table'], case['targets']
    n = len(table)
    record = dict(table=table, term_roots={}, term_nodes=['x', 'y'], interpolation_targets={})
    attempts = {}

    def add_terms(result):
        # Independent replay uses the repository's parsed law, not the C++ formulas.
        x, y = np.indices((n, n))
        values, mapping = [], {0: 0, 1: 1}
        for i, node in enumerate(result['term_nodes']):
            if isinstance(node, str):
                assert node in ('x', 'y')
                values.append(x if node == 'x' else y)
            else:
                a, b = node
                assert 0 <= a < i and 0 <= b < i
                values.append(np.asarray(table)[values[a], values[b]])
                mapping[i] = len(record['term_nodes'])
                record['term_nodes'].append([mapping[a], mapping[b]])
        for t, root in result['term_roots'].items():
            assert 0 <= root < len(values) and holds(EQUATIONS[int(t)-1], values[root])
            record['term_roots'][t] = mapping[root]

    if 'enumerate' in config['methods']:
        supported = {313, 1482, 3272, 3472, 3548, 3558, 4290}
        selected = sorted(set(targets) & supported)
        if selected and 2 <= n <= 5:
            result = run_search(binaries[0], [n, len(selected), config['limit'], config['seconds'],
                                *selected, *[v for row in table for v in row]])
            add_terms(result)
            attempts['enumerate'] = {k: v for k, v in result.items() if k not in ('term_nodes', 'term_roots')}
    if 'guided' in config['methods']:
        for target in targets:
            if str(target) in record['term_roots']:
                continue
            result = guided_term_search(np.array(table), target, seed=config['seed']+index,
                                        seconds=config['seconds'])
            add_terms(result)
            attempts[f'guided_{target}'] = {k: v for k, v in result.items() if k not in ('term_nodes', 'term_roots')}
    pending = [t for t in targets if str(t) not in record['term_roots']]
    if pending and 'majority' in config['methods']:
        majority = boolean_majority(table, unary_limit=1024, seconds=config['seconds'])
        if majority is None:
            majority = lattice_majority(table, binaries[1], config['seconds'])
        attempts['majority'] = dict(found=majority is not None)
        if majority is not None:
            record['majority'] = majority
            for target in pending:
                candidate = case['candidates'].get(str(target))
                if candidate is None:
                    candidate = relation_screen(np.array(table), [target], 10000)[target].get('relaxed_target')
                if candidate is not None:
                    check_interpolation(table, majority, candidate)
                    assert holds(EQUATIONS[target-1], np.array(candidate))
                    record['interpolation_targets'][str(target)] = candidate
    missing = [t for t in targets if str(t) not in record['term_roots']
               and str(t) not in record['interpolation_targets']]
    record['search_attempts'] = attempts
    output = Path(config['output'])/f'E{case["sources"][0]}_n{n}_{index:04}.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(dict(source=case['sources'][0], order=n,
                                     sources=case['sources'], settings=config, models=[record]), indent=2)+'\n')
    return dict(index=index, sources=case['sources'], order=n, targets=targets, unproved=missing)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, default=ROOT/'data/definability_small_model_sweep.json.gz')
    parser.add_argument('--output', type=Path, default=ROOT/'.cache/definability-small-sweep-20261012/continued_refinements')
    parser.add_argument('--methods', nargs='+', choices=['enumerate', 'guided', 'majority'],
                        default=['enumerate', 'guided', 'majority'])
    parser.add_argument('--seconds', type=float, default=4)
    parser.add_argument('--limit', type=int, default=2000000)
    parser.add_argument('--seed', type=int, default=20261012)
    parser.add_argument('--workers', type=int, default=4)
    args = parser.parse_args()
    if args.seconds <= 0 or args.limit < 2 or args.workers < 1:
        parser.error('seconds and workers must be positive, and limit must be at least two')
    data = json.loads(gzip.decompress(args.archive.read_bytes()))
    cases = pending_cases(data)
    binaries = compile_searches()
    config = dict(methods=args.methods, seconds=args.seconds, limit=args.limit,
                  seed=args.seed, output=str(args.output))
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(refine, (i, case, config, binaries)) for i, case in enumerate(cases)]
        for result in as_completed(futures):
            print(json.dumps(result.result()), flush=True)


if __name__ == '__main__':
    main()
