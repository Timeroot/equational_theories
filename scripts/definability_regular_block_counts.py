#!/usr/bin/env python3
"""Research counts for unary laws under regular finite-group actions.

These Python counts select targets, not proof facts. Exported negatives must be
checked separately by the Lean regular-block counting theorem and local counts.
"""
import argparse
import itertools
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def parse_term(s):
    tokens = re.findall(r'x|◇|\(|\)', s)
    i = 0

    def expression():
        nonlocal i

        def atom():
            nonlocal i
            if tokens[i] == 'x':
                i += 1
                return None
            assert tokens[i] == '('
            i += 1
            result = expression()
            assert tokens[i] == ')'
            i += 1
            return result

        result = atom()
        while i < len(tokens) and tokens[i] == '◇':
            i += 1
            result = (result, atom())
        return result

    result = expression()
    assert i == len(tokens)
    return result


def group(name):
    if name.startswith('C'):
        n = int(name[1:])
        return [[(a+b) % n for b in range(n)] for a in range(n)]
    if name == 'V4':
        return [[a ^ b for b in range(4)] for a in range(4)]
    if name == 'S3':
        perms = list(itertools.permutations(range(3)))
        return [[perms.index(tuple(a[b[i]] for i in range(3))) for b in perms] for a in perms]
    raise ValueError(name)


def count_laws(mul, laws, *, pointed=False):
    n = len(mul)
    assert mul[0] == list(range(n))
    inv = [next(b for b in range(n) if mul[a][b] == 0) for a in range(n)]
    counts = {a: 0 for a in laws}
    values = range(n+1) if pointed else range(n)
    for data in itertools.product(values, repeat=n+2 if pointed else n):
        p = data[:n]

        def operation(a, b):
            if pointed:
                u, v = data[n:]
                if a == n and b == n:
                    return n
                if a == n:
                    return n if v == n else mul[b][v]
                if b == n:
                    return n if u == n else mul[a][u]
            q = p[mul[inv[a]][b]]
            return n if q == n else mul[a][q]

        def evaluate(t):
            if t is None:
                return 0
            a, b = evaluate(t[0]), evaluate(t[1])
            return operation(a, b)
        for a, (l, r) in laws.items():
            counts[a] += evaluate(l) == evaluate(r)
    return counts


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--groups', nargs='+', default=['C2', 'C3', 'C4', 'V4', 'C5', 'C6', 'S3'])
    ap.add_argument('--pointed-groups', nargs='*', default=['C2', 'C3', 'C4', 'V4'])
    ap.add_argument('--output', type=Path, default=ROOT/'data/definability_regular_block_counts.json')
    args = ap.parse_args()
    snapshot = json.loads((ROOT/'docs/definability_open/snapshot.json').read_text())
    board = snapshot['boards']['structural/all']
    rep = {n: int(a) for a, ns in board['classes'].items() for n in ns}
    laws = {}
    for a, line in enumerate((ROOT/'data/equations.txt').read_text().splitlines(), 1):
        if set(re.findall('[a-z]', line)) == {'x'} and rep[a] == a:
            laws[a] = tuple(map(parse_term, line.split('=')))
    counts = {}
    pairs = {}
    for name in args.groups:
        counts[name] = count_laws(group(name), laws)
        new = []
        for a, ca in counts[name].items():
            targets = {t for ts in board['open_rows'].get(str(a), {}).values() for t in ts}
            for b, cb in counts[name].items():
                if cb < ca and b in targets:
                    pairs.setdefault((a,b), []).append(name)
                    new.append((a,b))
        print(name, counts[name], 'open arrows ruled out:', len(new), flush=True)
    pointed_counts = {}
    pointed_pairs = {}
    for name in args.pointed_groups:
        pointed_counts[name] = count_laws(group(name), laws, pointed=True)
        new = []
        for a, ca in pointed_counts[name].items():
            targets = {t for ts in board['open_rows'].get(str(a), {}).values() for t in ts}
            for b, cb in pointed_counts[name].items():
                if cb < ca and b in targets and (a,b) not in pairs:
                    pointed_pairs.setdefault((a,b), []).append(name)
                    new.append((a,b))
        print('pointed', name, pointed_counts[name], 'additional arrows:', len(new), flush=True)
    out = dict(status='research counts; Lean checks required' , source_fingerprint=snapshot['fingerprint'],
               counts=counts, pointed_counts=pointed_counts,
               pointed_candidate_arrows=[dict(source=a, target=b, groups=gs) for (a,b), gs in sorted(pointed_pairs.items())],
               candidate_arrows=[dict(source=a, target=b, groups=gs) for (a,b), gs in sorted(pairs.items())])
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print('Distinct candidate arrows:', len(pairs), 'regular +', len(pointed_pairs), 'pointed', flush=True)


if __name__ == '__main__':
    main()
