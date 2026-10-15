#!/usr/bin/env python3
"""Publish and replay the small-model term-definability search inventory.

The replay checks positive witnesses for every covered model/target pair, source laws, and complete
order-2/3 enumeration. Higher-order enumeration completion records an SMT
search result, not a Lean theorem or a replayed UNSAT certificate.
"""
import argparse
from collections import Counter
import gzip
import json
from pathlib import Path

import numpy as np
import z3

from definability_small_model_sweep import (
    EQUATIONS, ROOT, compact_terms, holds, relabel, small_bank)
from definability_majority_interpolation import check_interpolation, evaluate

ARCHIVE = ROOT/'data/definability_small_model_sweep.json.gz'
SUMMARY = ROOT/'data/definability_small_model_sweep_summary.json'
DOC = ROOT/'docs/definability_small_model_sweep.md'


def table_key(table):
    return (len(table), bytes(v for row in table for v in row))


def gather(root):
    snapshot = json.loads((ROOT/'docs/definability_open/snapshot.json').read_text())
    best = {}
    for p in sorted(root.rglob('E*_n*.json')):
        d = json.loads(p.read_text())
        if 'summary' not in d:
            continue
        s = d['summary']
        key = (s['order'], s['source'])
        score = (s['source_enumeration'] == 'exhausted', s['models'],
                 sum(v['term_found'] for v in s['outcomes'].values()))
        if key not in best or score > best[key][0]:
            best[key] = score, d
    jobs = []
    for key in sorted(best):
        d = best[key][1]
        settings = {k: v for k, v in d['config'].items() if k not in ('output', 'sources', 'orders')}
        jobs.append(dict(summary=d['summary'], settings=settings, models=d['models']))
    extras = []
    interpolations = []
    extra_obstructions = []
    for p in sorted(root.rglob('E*_n*.json')):
        d = json.loads(p.read_text())
        if 'summary' in d or 'models' not in d:
            continue
        for r in d['models']:
            if r.get('term_roots'):
                roots, nodes = compact_terms(r['term_nodes'], r['term_roots'])
                extras.append(dict(table=r['table'], term_roots=roots, term_nodes=nodes))
            if r.get('interpolation_targets'):
                interpolations.append(dict(table=r['table'], majority=r['majority'],
                                           interpolation_targets=r['interpolation_targets']))
            for t, result in r.get('relations', {}).items():
                if result['status'] == 'unsat':
                    extra_obstructions.append(dict(source=d['source'], target=int(t),
                        order=d['order'], table=r['table'], kind='relation', result=result))
            for t in r.get('exact_clone_negatives', []):
                extra_obstructions.append(dict(source=d['source'], target=int(t),
                    order=d['order'], table=r['table'], kind='exact_clone', result=r))
    probes = [json.loads(p.read_text()) for pattern in ('four335_*.json', 'five335_*.json',
                                                       'five3472_*.json', 'five1519_*.json')
              for p in sorted(root.glob(pattern))]
    report = root/'marked_refinements/report.json'
    return dict(schema=2, date='2026-10-12', source_fingerprint=snapshot['fingerprint'],
                proof_status='Finite computations; majority interpolation principle proved in Lean. '
                             'Individual model certificates and enumeration results are not Lean proofs.',
                versions=dict(z3=z3.get_version_string(), numpy=np.__version__),
                jobs=jobs, additional_terms=extras, extra_obstructions=extra_obstructions,
                additional_interpolations=interpolations,
                refinement_report=json.loads(report.read_text()) if report.exists() else None,
                higher_arity_probes=probes)


def summarize(data):
    witnesses = set()
    for r in [r for j in data['jobs'] for r in j['models']] + data['additional_terms']:
        witnesses.update((table_key(r['table']), int(t)) for t in r['term_roots'])
    for r in data.get('additional_interpolations', []):
        witnesses.update((table_key(r['table']), int(t)) for t in r['interpolation_targets'])
    rows = []
    for job in data['jobs']:
        s = job['summary']
        counts = {str(t): sum((table_key(r['table']), t) in witnesses for r in job['models'])
                  for t in s['targets']}
        unresolved = {t: s['models']-c for t, c in counts.items() if c < s['models']}
        rows.append(dict(source=s['source'], order=s['order'], targets=s['targets'],
                         models=s['models'], source_enumeration=s['source_enumeration'],
                         term_witnesses=counts, model_target_cases_without_terms=unresolved))
    orders = {}
    for n in sorted({r['order'] for r in rows}):
        rs = [r for r in rows if r['order'] == n]
        orders[str(n)] = dict(source_classes=len(rs),
            enumeration_exhausted=sum(r['source_enumeration'] == 'exhausted' for r in rs),
            source_model_cases=sum(r['models'] for r in rs),
            term_witness_cases=sum(sum(r['term_witnesses'].values()) for r in rs),
            model_target_cases_without_terms=sum(sum(r['model_target_cases_without_terms'].values())
                                                  for r in rs),
            complete_source_rows_with_all_terms=sum(r['source_enumeration'] == 'exhausted'
                                                   and not r['model_target_cases_without_terms'] for r in rs),
            stop_reasons=dict(Counter(r['source_enumeration'] for r in rs)))
    discoveries = {(j['summary']['source'], int(t), j['summary']['order'])
                   for j in data['jobs'] for t, c in j['summary']['outcomes'].items()
                   if c['exact_clone_negative'] or c['relation_negative']}
    discoveries.update((r['source'], r['target'], r['order'])
                       for r in data.get('extra_obstructions', []))
    discoveries.update((r['source'], int(t), len(r['table']))
                       for r in data['higher_arity_probes'] for t, c in r['relations'].items()
                       if c['status'] == 'unsat')
    return dict(schema=data['schema'], date=data['date'], source_fingerprint=data['source_fingerprint'],
                proof_status=data['proof_status'], orders=orders,
                refinement_report=data.get('refinement_report'),
                discoveries=[list(r) for r in sorted(discoveries)], rows=rows)


def check(data):
    checked = set()
    source_checks = set()
    for job in data['jobs']:
        s = job['summary']
        assert len(job['models']) == s['models']
        keys = [table_key(r['table']) for r in job['models']]
        assert len(keys) == len(set(keys))
        for r in job['models']:
            key = (table_key(r['table']), s['source'])
            if key not in source_checks:
                table = np.array(r['table'], dtype=np.uint8)
                assert table.shape == (s['order'], s['order']) and np.all(table < s['order'])
                assert holds(EQUATIONS[s['source']-1], table)
                source_checks.add(key)
    for r in [r for j in data['jobs'] for r in j['models']] + data['additional_terms']:
        pending = {int(t) for t in r['term_roots'] if (table_key(r['table']), int(t)) not in checked}
        if not pending:
            continue
        table = np.array(r['table'], dtype=np.uint8)
        n = len(table)
        x, y = np.indices((n, n))
        ops = []
        for i, node in enumerate(r['term_nodes']):
            if node in ('x', 'y'):
                ops.append(x if node == 'x' else y)
            else:
                a, b = node
                assert 0 <= a < i and 0 <= b < i
                ops.append(table[ops[a], ops[b]])
        for target in pending:
            root = r['term_roots'][str(target)]
            assert 0 <= root < len(ops)
            assert holds(EQUATIONS[target-1], ops[root])
            checked.add((table_key(r['table']), target))
    interpolation_checks = 0
    known_tables = {key for key, _ in source_checks}
    for r in data.get('additional_interpolations', []):
        key = table_key(r['table'])
        assert key in known_tables
        for target, operation in r['interpolation_targets'].items():
            # Check even if another method already supplied this same witness.
            check_interpolation(r['table'], r['majority'], operation)
            assert holds(EQUATIONS[int(target)-1], np.array(operation, dtype=np.uint8))
            checked.add((key, int(target)))
            interpolation_checks += 1
    report = data.get('refinement_report')
    if report and report.get('last_case'):
        r = report['last_case']
        table = np.array(r['table'], dtype=np.uint8)
        retract, subset = r['retract'], r['subalgebra']
        # r(x) = (x*(x*x))*((x*x)*x).
        assert retract == [int(table[table[x, table[x, x]], table[table[x, x], x]])
                           for x in range(len(table))]
        assert set(retract) == set(subset) and all(retract[x] == x for x in subset)
        assert all(int(table[x, y]) in subset for x in subset for y in subset)
        subtable = np.array([[subset.index(int(table[x, y])) for y in subset] for x in subset])
        for base, certificate in ((table, r), (subtable, r['subalgebra_term'])):
            term = dict(nodes=[0, 1]+certificate['term_nodes'][2:],
                        root=certificate['term_roots'][str(r['target'])])
            assert holds(EQUATIONS[r['target']-1], evaluate(base, term, 2))
    for n in (2, 3):
        bank = list(small_bank(n))
        assert len(bank) == {2: 10, 3: 3330}[n]
        for job in data['jobs']:
            s = job['summary']
            if s['order'] == n and s['source_enumeration'] == 'exhausted':
                actual = {table_key(r['table']) for r in job['models']}
                expected = {table_key(t.tolist()) for t in bank if holds(EQUATIONS[s['source']-1], t)}
                assert actual == expected, (s['source'], n)
    # Independent published count for the cube-law pair at order 4.
    from itertools import permutations
    for job in data['jobs']:
        s = job['summary']
        if s['order'] == 4 and s['source'] in (3342, 3545) and s['source_enumeration'] == 'exhausted':
            labeled = sum(len({tuple(relabel(np.array(r['table']), p).flat)
                               for p in permutations(range(4))}) for r in job['models'])
            assert labeled == 37076
    print(f'Checked {len(source_checks):,} source-law cases and {len(checked):,} distinct model/target witnesses.')
    print(f'Checked {interpolation_checks:,} compact majority-interpolation certificates.')
    print('Re-enumerated orders 2 and 3 independently; cube-law order-4 counts agree with 37,076 labeled models.')
    print('Higher-order enumeration exhaustion remains a recorded solver result, not a Lean proof.')


def render(summary):
    lines = ['# Systematic small-model term-definability sweep', '',
        'Run: **12 October 2026**. The starting board has **210** open directed pairs',
        'of finite term-definability classes, involving **50** source classes.',
        'The finite-model results below are computational research, not Lean proofs',
        'of those individual examples. The general majority-interpolation theorem',
        'used by the compact certificates is proved in Lean.', '',
        '## Coverage', '',
        '“Enumerated” concerns the source models. “All terms witnessed” additionally',
        'means every target has a constructive term certificate on every enumerated source.',
        'A surviving compatible-relation relaxation **alone** does not count as a term.',
        'Source/model counts below count a table again when it satisfies another source law.', '',
        '| Order | Source rows enumerated completely | Source/model cases checked | Complete rows with all terms witnessed | Cases still lacking a term |',
        '|---|---:|---:|---:|---:|']
    for n, c in summary['orders'].items():
        lines.append(f'| {n} | {c["enumeration_exhausted"]}/{c["source_classes"]} | '
                     f'{c["source_model_cases"]:,} | {c["complete_source_rows_with_all_terms"]} | '
                     f'{c["model_target_cases_without_terms"]:,} |')
    lines += ['', f'New negative generators found: **{len(summary["discoveries"])}**.', '',
        'All remaining arrows have successful terms on every source model of orders',
        '2 and 3. Order 1 is automatic. Thus any counterexample to one of these',
        'remaining arrows must have at least four elements, according to this',
        'exhaustive computation. The completed order-4 rows raise that lower bound',
        'to five; the completed order-5 rows raise it to six. Incomplete source',
        'enumerations do not support those stronger lower bounds.',
        'These finite-size statements are not formalized in Lean.', '',
        '## Follow-up on the marked cases', '']
    report = summary.get('refinement_report')
    if report:
        left = sum(c['model_target_cases_without_terms'] for c in summary['orders'].values())
        initial = report['initial_model_target_cases']
        lines += [f'The follow-up resolved **{initial-left:,} of {initial:,}** previously marked',
                  f'model/target tests; **{left:,}** remain. This does not close a universal',
                  'definability arrow. In particular, incomplete source enumeration stays incomplete.', '']
        counts = report['counts']
        lines += [f'The new certificates comprise **{counts["explicit_terms"]:,} explicit binary terms**',
                  f'and **{counts["interpolations"]:,} compact majority-interpolation recipes**.',
                  f'The largest new stored term DAG has **{report["max_certificate_nodes"]} nodes**.', '']
    lines += [
        'The follow-up combines larger compiled term enumeration, a guided search',
        'that favors terms satisfying more instances of the target law, and majority',
        'interpolation. For the latter, unary terms encode the source into two- or',
        'three-value coordinates. A term computes majority on those values, and',
        'another term decodes the coordinates. The resulting majority term lets us',
        'combine pairwise witnesses into one successful binary term.', '',
        'The compact certificate records the majority term and the target operation.',
        'Replay checks the majority identities, every pair-interpolation condition,',
        'and the target law. It avoids storing the expanded interpolation term.',
        'The underlying finite interpolation argument, including its application to',
        'binary magma terms, is formalized in',
        '[MajorityInterpolation.lean](../equational_theories/Definability/MajorityInterpolation.lean).', '']
    if report:
        lines += [
            'The last E1519 → E3272 example used a different reduction. On that',
            'five-element source, the unary term `r(x) = (x*(x*x))*((x*x)*x)` is',
            '`[0,0,2,3,4]`: a retraction onto the subalgebra `{0,2,3,4}`. Find an',
            'E3272 term `t` on that four-element subalgebra, then use',
            '`t(r(x),r(y))` on the original source. Both sides of E3272 are composite',
            'terms, so this pullback preserves the law. The resulting witness has',
            '**18 DAG nodes**. Replay checks the retraction, subalgebra, and both',
            'successful terms. Its data are included in the machine-readable report.', '']
    lines += [
        '## Unfinished source enumeration', '',
        '| Order | Source | Models checked | Stop reason |', '|---|---|---:|---|']
    for r in summary['rows']:
        if r['source_enumeration'] != 'exhausted':
            lines.append(f'| {r["order"]} | E{r["source"]} | {r["models"]:,} | {r["source_enumeration"]} |')
    lines += ['', '## Enumerated models still lacking a target term', '']
    unresolved = [r for r in summary['rows'] if r['model_target_cases_without_terms']]
    if unresolved:
        lines += ['These are unresolved tests on particular finite sources, not counterexamples.', '',
                  '| Order | Source → target | Model cases without a term |', '|---|---|---:|']
        for r in unresolved:
            for t, count in r['model_target_cases_without_terms'].items():
                lines.append(f'| {r["order"]} | E{r["source"]} → E{t} | {count:,} |')
    else:
        lines += ['**None.** Every target on every currently enumerated source has a constructive',
                  'term certificate. The remaining gaps concern source enumeration, listed above.']
    lines += ['', '## Method and replay', '',
        'Orders 2 and 3 enumerate all multiplication tables and identify isomorphic',
        'copies. Higher orders use finite SMT encodings of the source law',
        '(enumerated domains in the first pass, bounded bit vectors in later runs),',
        'either lexicographic symmetry breaking or blocking every relabeling of a',
        'found model. Exhaustion means the source solver returned UNSAT after blocking',
        'the saved models; these UNSAT results are not Lean certificates.', '',
        'Every source is tested by enumeration of term operations. If that search',
        'does not supply a target, compatible relations generated by the projections',
        'constrain all possible terms. Later refinements add the complete unary-term',
        'diagonal relation when feasible, higher-arity compatible relations, and',
        'deterministic seeded searches for longer terms. Failed bounded term searches',
        'and SAT relation relaxations stay unresolved. Time and model limits are',
        'recorded separately from exhaustive results.', '',
        'The compressed archive contains the selected source tables, term expressions',
        'as directed acyclic graphs, compact interpolation recipes, run settings, and refinements.',
        'The replay checks',
        'the source laws and a successful term for every covered model/target pair. It independently',
        're-enumerates orders 2 and 3, and checks the known 37,076 labeled order-4',
        'models for each cube law E3342 and E3545.', '',
        '```sh',
        'python3 scripts/definability_small_model_inventory.py --check',
        'OPENBLAS_NUM_THREADS=1 python3 scripts/definability_small_model_sweep.py --orders 2 3 4 5',
        '# Continue a limited job without rechecking its saved models:',
        'python3 scripts/definability_small_model_sweep.py --sources 3472 --orders 4 --resume --seconds 300',
        '# Refine any newly marked finite-source cases:',
        'python3 scripts/definability_small_model_refine.py',
        '```', '',
        'Machine-readable coverage: [summary](../data/definability_small_model_sweep_summary.json).',
        'Replay data: [compressed archive](../data/definability_small_model_sweep.json.gz).', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT/'.cache/definability-small-sweep-20261012')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.write:
        data = gather(args.root)
        summary = summarize(data)
        ARCHIVE.write_bytes(gzip.compress(json.dumps(data, separators=(',', ':')).encode(), mtime=0))
        SUMMARY.write_text(json.dumps(summary, indent=2)+'\n')
        DOC.write_text(render(summary))
        print(f'Wrote {len(data["jobs"])} source/order jobs; archive {ARCHIVE.stat().st_size:,} bytes.')
    else:
        data = json.loads(gzip.decompress(ARCHIVE.read_bytes()))
    if args.check:
        check(data)
        summary = summarize(data)
        assert summary == json.loads(SUMMARY.read_text())
        assert render(summary) == DOC.read_text()


if __name__ == '__main__':
    main()
