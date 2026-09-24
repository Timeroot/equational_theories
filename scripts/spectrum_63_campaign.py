#!/usr/bin/env python3
"""Run a resumable, ascending-order E63 positive-model search portfolio.

Uses spectrum_63_atp.py for solver inputs and independent witness checks.
Cycle cases are a selection of promising symmetry restrictions, not an
exhaustive case split. No failed search supplies a Lean exclusion.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy
import json
from pathlib import Path
from types import SimpleNamespace

from spectrum_63_atp import MISSING, ROOT, product_closure, search, validate


def selected_cycles(n, count):
    """Mix long cycles with repeated short cycles without enumerating partitions."""
    candidates = []

    def add(first, rest):
        case = [first, *sorted(rest)]
        if sum(case) == n and all(k > 0 and k != 2 for k in case) and case not in candidates:
            candidates.append(case)

    for first in [1, 3]:
        add(first, [n - first])
    for k in [3, 5, 7, 4, 8, 11]:
        for first in [1, 3]:
            q, r = divmod(n - first, k)
            if r == 2 and q:
                add(first, [k] * (q - 1) + [k + 2])
            else:
                add(first, [k] * q + ([r] if r else []))
    for k in [1, 3, 5, 7, n // 3, n // 2]:
        for first in [1, 3]:
            add(first, [k, n - first - k])
    return candidates[:count]


def profiles(n, config):
    common = SimpleNamespace(
        restriction='none', cancellation=True, submodel=None, translation_hints=True,
        first_row_cycles=None, seconds=config.seconds, large_after=1000,
        large_seconds=config.seconds, memory=config.memory, vampire=config.vampire,
        mace4=config.mace4, sat_solver='cadical', random_seed=1,
        mace_order=2, mace_measure=4)
    result = []

    def add(name, solver, law, **changes):
        args = deepcopy(common)
        for key, value in changes.items():
            setattr(args, key, value)
        args.workdir = config.workdir / str(n) / name
        args.workdir.mkdir(parents=True, exist_ok=True)
        result.append((name, solver, law, args))

    add('mace63', 'mace4', 63, cancellation=False, translation_hints=False)
    add('mace229-hints', 'mace4', 229)
    if n <= config.vampire_max:
        add('vampire63-cadical', 'vampire', 63, cancellation=False, translation_hints=False)
        add('vampire229-minisat', 'vampire', 229, sat_solver='minisat')
    else:
        add('mace63-linear', 'mace4', 63, mace_order=0, mace_measure=0)
        add('mace229-occurrences', 'mace4', 229, mace_order=0, mace_measure=1)
    for i, case in enumerate(selected_cycles(n, config.cycle_count)):
        add(f'cycle-{i}', 'mace4', 229 if i % 2 == 0 else 63,
            first_row_cycles=case, seconds=config.cycle_seconds)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=MISSING)
    parser.add_argument('--seconds', type=int, default=180)
    parser.add_argument('--cycle-seconds', type=int, default=30)
    parser.add_argument('--cycle-count', type=int, default=16)
    parser.add_argument('--memory', type=int, default=4096)
    parser.add_argument('--workers', type=int, choices=range(1, 17), default=8)
    parser.add_argument('--vampire-max', type=int, default=62)
    parser.add_argument('--vampire', type=Path, required=True)
    parser.add_argument('--mace4', type=Path, required=True)
    parser.add_argument('--workdir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--force-known', action='store_true')
    config = parser.parse_args()
    assert min(config.orders) >= 3 and min(config.seconds, config.cycle_seconds) > 0
    assert config.cycle_count >= 0
    config.workdir.mkdir(parents=True, exist_ok=True)
    config.output.parent.mkdir(parents=True, exist_ok=True)
    configuration = {key: str(value) if isinstance(value, Path) else value
                     for key, value in vars(config).items() if key != 'resume'}
    report = {'law': 63, 'status': 'MODEL_SEARCH_NOT_LEAN', 'configuration': configuration,
              'attempts': [], 'witnesses': {}, 'derived': {}, 'completed_orders': []}
    if config.resume:
        report = json.loads(config.output.read_text())
        assert report['configuration'] == configuration, 'Resume requires unchanged search settings'
    certificate = json.loads((ROOT / 'data/spectrum/63_constructions.json').read_text())
    known = {int(n): {'kind': 'existing_construction'} for n in certificate['pointed']}
    for n, record in report['witnesses'].items():
        validate(record['e63_table'], int(n))
        known[int(n)] = {'kind': 'verified_table', 'order': int(n)}

    def save():
        temporary = config.output.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(config.output)

    with ThreadPoolExecutor(max_workers=config.workers) as executor:
        for n in sorted(set(config.orders)):
            if n in report['completed_orders']:
                continue
            product_closure(known, max(config.orders))
            if n in known and not config.force_known:
                report['derived'][str(n)] = known[n]
                report['completed_orders'].append(n)
                save()
                print('SKIP', n, known[n], flush=True)
                continue
            report['current_order'] = n
            save()
            done = {r['profile'] for r in report['attempts'] if r['order'] == n}
            pending = [p for p in profiles(n, config) if p[0] not in done]
            print('BEGIN ORDER', n, len(pending), 'profiles', flush=True)
            futures = {executor.submit(search, args, n, solver, law): name
                       for name, solver, law, args in pending}
            for future in as_completed(futures):
                if future.cancelled():
                    continue
                record = future.result()
                record['profile'] = futures[future]
                report['attempts'].append(record)
                if record['status'] == 'VERIFIED_MODEL' and str(n) not in report['witnesses']:
                    report['witnesses'][str(n)] = {
                        'e63_table': record['e63_table'], 'idempotents': record['idempotents'],
                        'profile': record['profile']}
                    known[n] = {'kind': 'verified_table', 'order': n}
                    for other in futures:
                        other.cancel()
                    print('NEW VERIFIED ORDER', n, flush=True)
                save()
            report['completed_orders'].append(n)
            save()
            print('END ORDER', n, 'witnesses', sorted(map(int, report['witnesses'])), flush=True)
    report.pop('current_order', None)
    report['finished'] = True
    save()
    print('FINISHED; direct witnesses:', sorted(map(int, report['witnesses'])), flush=True)


if __name__ == '__main__':
    main()
