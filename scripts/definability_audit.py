"""Exhaustive, lossless inventory of open definability cells; not a proof oracle.

Run from the repository root with OPENBLAS_NUM_THREADS=2. --write scans Lean and
regenerates the snapshot and Markdown appendices; --check recomputes and compares.
--render only regenerates Markdown from the saved snapshot (no source scan).
The mathematical discussion in docs/definability_open_audit.md is maintained by hand.
"""
import argparse
from collections import Counter
from datetime import date
import hashlib
import json
from pathlib import Path
import subprocess
import time

import numpy as np

import definable as board
from lean_sources import import_graph

ROOT = board.ROOT
OUT = ROOT / 'docs/definability_open'
SNAPSHOT = OUT / 'snapshot.json'
KEY_NAMES = ['/'.join(key) for key in board.KEYS]
HISTORICAL_TS_ALL = [
    (63, 125), (63, 3548), (124, 1648), (124, 3343), (124, 4130),
    (125, 3548), (125, 3954), (206, 1648), (206, 3343), (222, 3548),
    (271, 3548), (1648, 124), (1648, 206), (1648, 3343), (1648, 4130),
    (56, 50), (167, 117), (440, 414), (467, 437), (473, 429),
    (477, 417), (481, 452), (504, 427), (543, 4541), (879, 632),
    (910, 427), (1492, 417), (1496, 452),
]
HISTORICAL = ([('termStructural/all', s, t) for s, t in HISTORICAL_TS_ALL]
              + [('termStructural/fin', s, t) for s, t in [(56, 50), (167, 117), (440, 414)]]
              + [('structural/fin', s, t) for s, t in [(56, 50), (167, 117), (332, 3), (440, 414)]])


def ranges(numbers):
    """Inclusive ranges of >= 3 consecutive integers; no suppressed gaps."""
    numbers = sorted(numbers)
    result, i = [], 0
    while i < len(numbers):
        j = i
        while j + 1 < len(numbers) and numbers[j + 1] == numbers[j] + 1:
            j += 1
        if j - i >= 2:
            result.append(f'{numbers[i]}–{numbers[j]}')
        else:
            result.extend(str(n) for n in numbers[i:j + 1])
        i = j + 1
    return ', '.join(result)


def profile(code):
    """Ten ternary digits in KEYS order: O=0, P=1, N=2."""
    return ''.join('OPN'[(int(code) // 3**i) % 3] for i in range(len(board.KEYS)))


def source_fingerprint():
    paths = sorted((ROOT / 'equational_theories').rglob('*.lean')) + [
        ROOT / 'data/duals.json', ROOT / 'scripts/definable.py',
        ROOT / 'scripts/lean_sources.py', Path(__file__).resolve(),
    ]
    digest = hashlib.sha256()
    for path in paths:
        content = path.read_bytes()
        digest.update(str(path.relative_to(ROOT)).encode() + b'\0')
        digest.update(str(len(content)).encode() + b'\0' + content)
    return {'sha256': digest.hexdigest(), 'files': len(paths)}


def summarize_relation(pos, neg, codes):
    """Quotient and verify *every* status rectangle, not just aggregate counts."""
    reps, cls = board.preorder_quotient(pos)
    assert reps[0] == 0 and np.all(cls[1:] > 0), 'sentinel must be isolated'
    grid = np.ix_(reps, reps)
    for matrix in (pos, neg):
        reduced = matrix[grid]
        # Check one full source row at a time, avoiding another 4695² allocation.
        for s in range(1, len(matrix)):
            assert np.array_equal(matrix[s, 1:], reduced[cls[s], cls[1:]])
    assert not np.any(pos & neg)
    assert np.all(np.diag(pos))
    members = {int(r): np.flatnonzero(cls == i).tolist() for i, r in enumerate(reps) if r}
    assert sorted(n for group in members.values() for n in group) == list(range(1, len(pos)))
    assert all(r == min(group) for r, group in members.items())
    rows = {}
    reduced_profiles = Counter()
    weighted_open = 0
    for s in reps[1:]:
        targets = reps[1:][~(pos[s, reps[1:]] | neg[s, reps[1:]])]
        if not len(targets):
            continue
        groups = {}
        for t in targets:
            sig = profile(codes[s, t])
            groups.setdefault(sig, []).append(int(t))
            reduced_profiles[sig] += 1
            weighted_open += len(members[int(s)]) * len(members[int(t)])
        rows[int(s)] = dict(sorted(groups.items()))
    raw_open = ~(pos[1:, 1:] | neg[1:, 1:])
    assert weighted_open == int(raw_open.sum())
    values, counts = np.unique(codes[1:, 1:][raw_open], return_counts=True)
    raw_profiles = {profile(v): int(c) for v, c in zip(values, counts)}
    return dict(classes=members, open_rows=rows, reduced_profiles=dict(sorted(reduced_profiles.items())),
                raw_profiles=dict(sorted(raw_profiles.items())),
                counts=dict(classes=len(members), positive=int(pos[1:, 1:].sum()) - len(pos) + 1,
                            negative=int(neg[1:, 1:].sum()), raw_open=weighted_open,
                            reduced_open=sum(reduced_profiles.values())))


def collect(snapshot_date, verify):
    before = source_fingerprint()
    diagnostics = {}
    pos, neg = board.build_relations(verify=verify, diagnostics=diagnostics)
    codes = np.zeros((board.SIZE, board.SIZE), dtype=np.uint16)
    for i, key in enumerate(board.KEYS):
        codes += (pos[key].astype(np.uint16) + 2 * neg[key].astype(np.uint16)) * 3**i
    for a, b in board.ARROWS:
        assert not np.any(pos[a] & ~pos[b])
        assert not np.any(neg[b] & ~neg[a])
    boards = {'/'.join(key): summarize_relation(pos[key], neg[key], codes) for key in board.KEYS}
    completely_open = summarize_completely_open(pos, neg)
    cross_tabs = {}
    off_diagonal = ~np.eye(board.N_EQ, dtype=bool)
    for relation in board.RELATIONS:
        states = {}
        for flavour in board.FLAVOURS:
            key = relation, flavour
            states[flavour] = pos[key][1:, 1:].astype(np.uint8) + 2 * neg[key][1:, 1:].astype(np.uint8)
        counts = np.bincount((states['all'] * 3 + states['fin'])[off_diagonal], minlength=9)
        cross_tabs[relation] = {'OPN'[a] + 'OPN'[f]: int(counts[3*a + f])
                                for a in range(3) for f in range(3)}
    historical = [dict(relation=k, source=s, target=t, profile=profile(codes[s, t]))
                  for k, s, t in HISTORICAL]
    for warning in diagnostics['definability']['carrier_warnings']:
        for fact in warning['negative_facts']:
            key = fact['relation'], 'fin'
            fact['finite_refutation_in_closure'] = bool(neg[key][fact['source'], fact['target']])
    graph = import_graph(ROOT)
    diagnostics['implications']['outside_definability_imports'] = [
        p for p in diagnostics['implications']['source_files']
        if '.'.join(Path(p).with_suffix('').parts) not in graph]
    assert before == source_fingerprint(), 'sources changed during audit; rerun on a stable tree'
    return dict(schema=1, date=snapshot_date, equation_count=board.N_EQ, key_order=KEY_NAMES,
                head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                fingerprint=before, boards=boards, completely_open=completely_open,
                all_fin=cross_tabs, historical=historical,
                diagnostics=diagnostics)


def summarize_completely_open(pos, neg):
    """Intersect all eight boards; quotient only by the strongest positive relation."""
    mask = ~neg['termStructural', 'all'] & ~pos['definable', 'fin']
    explicit = np.ones_like(mask)
    for key in board.KEYS:
        if key[0] != 'implies':
            explicit &= ~(pos[key] | neg[key])
    assert np.array_equal(mask, explicit), 'hierarchy endpoints must equal the eight-way intersection'
    mask[0, :] = mask[:, 0] = False  # Equation 0 is an isolated bookkeeping sentinel.
    reps, cls = board.preorder_quotient(pos['termStructural', 'all'])
    assert reps[0] == 0 and not mask[0].any() and not mask[:, 0].any()
    reduced = mask[np.ix_(reps, reps)]
    for s in range(1, len(mask)):
        assert np.array_equal(mask[s, 1:], reduced[cls[s], cls[1:]])
    pairs = [(int(s), int(t)) for s in reps[1:] for t in reps[1:] if mask[s, t]]
    incident = sorted({n for pair in pairs for n in pair})
    classes = {r: np.flatnonzero(cls == cls[r]).tolist() for r in incident}
    raw = sum(len(classes[s]) * len(classes[t]) for s, t in pairs)
    assert raw == int(mask[1:, 1:].sum())
    return dict(raw_pairs=raw, reduced_pairs=len(pairs), quotient='termStructural/all',
                pairs=pairs, classes=classes)


def completely_open_markdown(data):
    entry = data['completely_open']
    classes = {int(k): v for k, v in entry['classes'].items()}
    lines = ['# Completely open in all eight definability variants', '',
             '[Full audit](../definability_open_audit.md) · [All board totals](summary.md) · '
             '[Spectrum recheck](../definability_spectrum_check.md)', '',
             f'Snapshot: {data["date"]}. **{entry["raw_pairs"]:,} directed equation pairs**, '
             f'compressed losslessly into **{entry["reduced_pairs"]:,} class pairs**.', '',
             'A pair `source → target` is completely open exactly when neither of these is known:', '',
             '- A negative for **term-structural definability on arbitrary carriers** (TS/all).',
             '- A positive for **FO definability on finite carriers** (D/fin).', '',
             'TS/all is the strongest of the eight variants and D/fin the weakest.',
             'Every positive anywhere implies D/fin positive; every negative anywhere implies',
             'TS/all negative. Thus the endpoint test is equivalent to all eight statuses being',
             'open. The generator checks this equivalence on every raw pair, not just representatives.', '',
             '“Arbitrary carriers” allows infinite magmas; it does **not** mean infinitary terms.',
             'Implication is excluded from the eight variants. OPEN means unresolved by the',
             'current source-derived board, not necessarily unknown to mathematics.', '',
             '## Counting and progress', '',
             'We quotient by mutual **TS/all** positive arrows, using the least equation number',
             'as representative. These classes refine those of every other definability variant,',
             'so all eight statuses are constant on each rectangle. A weaker quotient would not',
             'justify this claim. The raw count is the primary progress metric: class counts can',
             'also fall merely because new positive equivalences merge classes.', '',
             'The 15 September snapshot and the subsequent square-swap / argument-swap passes',
             'all have **284 raw / 61 reduced** completely open pairs. Those passes improve',
             'structural/all without changing either endpoint of this metric.', '',
             '## Complete inventory', '',
             'Each row denotes `class(source) × class(target)`. No pairs are omitted;',
             'the next section supplies every member needed to expand the rectangles.', '',
             '| Source representative | Target representative | Raw pairs |', '|---:|---:|---:|']
    for s, t in entry['pairs']:
        lines.append(f'| {s} | {t} | {len(classes[s]) * len(classes[t])} |')
    lines += ['', '## All participating class memberships', '',
              'Classes not incident to a completely open pair are omitted. Ranges are inclusive.', '',
              '| Representative | All members |', '|---:|---|']
    for r, members in classes.items():
        lines.append(f'| {r} | {ranges(members)} |')
    lines += ['', '## Reproduction', '',
              'Run `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --verify-closure`.',
              'Use `--check` instead of `--write` to check the committed snapshot without rewriting it.',
              'The `completely_open` record in [snapshot.json](snapshot.json) contains the same',
              'pairs and class memberships. Counts are recomputed from Lean-source facts and closure;',
              'this documentation does not feed proof facts back into the board.']
    return '\n'.join(lines) + '\n'


def slug(key):
    return key.replace('/', '_') + '.md'


def summary_markdown(data):
    lines = ['# Open-cell totals', '', '[Audit and interpretation](../definability_open_audit.md).', '',
             f'**Completely open in all eight definability variants: '
             f'[{data["completely_open"]["raw_pairs"]:,} raw pairs / '
             f'{data["completely_open"]["reduced_pairs"]:,} class pairs](completely_open.md).**', '',
             f'Snapshot: {data["date"]}. Source SHA-256: `{data["fingerprint"]["sha256"]}`.', '',
             'All counts exclude diagonal pairs. Each full grid has 22,028,942 directed pairs.', '',
             '| Relation / carriers | Classes | Positive | Negative | Raw open | Reduced open |',
             '|---|---:|---:|---:|---:|---:|']
    for key, entry in data['boards'].items():
        c = entry['counts']
        lines.append(f'| [{key}]({slug(key)}) | ' + ' | '.join(f'{c[k]:,}' for k in
                     ('classes', 'positive', 'negative', 'raw_open', 'reduced_open')) + ' |')
    lines += ['', '## Arbitrary versus finite carriers', '',
              'These are **raw pairs with the same equation numbers**, not comparisons between',
              'different quotients. `P` = proved, `N` = refuted, `O` = open in the extracted board.', '',
              '| Relation | all O / fin O | all O / fin P | all N / fin O | all N / fin P |',
              '|---|---:|---:|---:|---:|']
    for rel, counts in data['all_fin'].items():
        lines.append(f'| {rel} | ' + ' | '.join(f'{counts[k]:,}' for k in ('OO', 'OP', 'NO', 'NP')) + ' |')
    lines += ['', '`all N / fin P` is a **settled** distinction, not an open question.',
              'The JSON also records P/P and N/N. P/O, P/N and O/N must be zero.', '',
              '## Historical shortlist rechecked', '',
              'Every one of the 35 cells in the historical report §3.5, in its original relation.',
              'The full profile uses `I, TS, S, TD, D`, with `all` then `fin` within each pair.', '',
              '| Relation originally open | Source → target | Current status | I · TS · S · TD · D |',
              '|---|---|---|---|']
    for h in data['historical']:
        sig = h['profile']
        status = {'O': 'OPEN', 'P': 'PROVED', 'N': 'REFUTED'}[sig[KEY_NAMES.index(h['relation'])]]
        lines.append(f'| {h["relation"]} | {h["source"]} → {h["target"]} | {status} | '
                     + ' · '.join(sig[i:i+2] for i in range(0, 10, 2)) + ' |')
    return '\n'.join(lines) + '\n'


def relation_markdown(key, entry):
    classes = {int(k): v for k, v in entry['classes'].items()}
    rows = {int(k): v for k, v in entry['open_rows'].items()}
    c = entry['counts']
    lines = [f'# {key}: complete open-cell inventory', '',
             '[Audit and interpretation](../definability_open_audit.md) · [Totals](summary.md)', '',
             f'{c["reduced_open"]:,} reduced cells, representing **{c["raw_open"]:,} raw pairs**,',
             f'with {c["classes"]:,} positive-equivalence classes. No open entries are omitted.', '',
             '`s → t` asks whether target E_t is obtainable from source E_s.',
             'Class representatives are the least equation numbers in their classes.',
             'Each entry expands to **class(s) × class(t)**; membership is listed below.',
             'Inclusive ranges abbreviate consecutive numbers only.', '',
             'A profile has ten characters: `I/all I/fin TS/all TS/fin S/all S/fin TD/all TD/fin D/all D/fin`.',
             '`P` = proved, `N` = refuted, `O` = open in the source-derived board.',
             '**Profiles in the inventory describe the representative pair only**: the other',
             'nine statuses need not be constant on this relation’s class rectangle.',
             'The open status for the relation named in this heading *is* constant.', '',
             '## Profiles of the remaining work', '',
             'Raw counts below are computed directly on the full matrices, not by weighting',
             'representative profiles. The two profile distributions can therefore differ.', '',
             '| Profile | Reduced open cells | Raw open pairs |', '|---|---:|---:|']
    for sig in sorted(set(entry['raw_profiles']) | set(entry['reduced_profiles'])):
        lines.append(f'| `{sig}` | {entry["reduced_profiles"].get(sig, 0):,} | '
                     f'{entry["raw_profiles"].get(sig, 0):,} |')
    lines += ['', '## Largest open source blocks', '',
              'Ranked by number of open target classes. Raw pairs include all members of both classes.', '',
              '| Source representative | Source class size | Open target classes | Raw open pairs |',
              '|---|---:|---:|---:|---:|']
    blocks = []
    for s, groups in rows.items():
        targets = [t for ts in groups.values() for t in ts]
        blocks.append((len(targets), s, len(classes[s]) * sum(len(classes[t]) for t in targets)))
    for count, s, raw in sorted(blocks, key=lambda b: (-b[0], b[1]))[:10]:
        lines.append(f'| {s} | {len(classes[s]):,} | {count:,} | {raw:,} |')
    lines += ['', '## Every open cell, grouped by source and profile', '',
              'Sources absent from this section have no open outgoing cells.', '',
              '| Source representative | Representative profile | All open target representatives |',
              '|---|---|---|']
    for s, groups in rows.items():
        for sig, targets in groups.items():
            lines.append(f'| {s} | `{sig}` | {ranges(targets)} |')
    if not rows:
        lines += ['', 'No open cells.']
    lines += ['', '## Complete class membership', '',
              'These are the classes for **this relation and carrier flavour only**.',
              'All 4,694 equations occur exactly once, including classes not incident to an open cell.', '',
              '| Representative | All members (including the representative) |', '|---|---|']
    for r, members in classes.items():
        lines.append(f'| {r} | {ranges(members)} |')
    return '\n'.join(lines) + '\n'


def diagnostics_markdown(data):
    d = data['diagnostics']
    defs, imp = d['definability'], d['implications']
    lines = ['# Extraction diagnostics', '', '[Main audit](../definability_open_audit.md).', '',
             'This is a complete warning list, not the CLI’s first-four preview.', '',
             '## Implication scan', '', f'Counts: `{json.dumps(imp["counts"], sort_keys=True)}`.', '',
             f'Unparsed attributed statements: {len(imp["unparsed"])}.', '',
             *[f'- `{s}`' for s in imp['unparsed']], '',
             '### Attributed source files outside the Definability import closure', '',
             'These are not claimed checked by the Definability entry-point build alone.', '',
             *[f'- [{p}](../../{p})' for p in imp['outside_definability_imports']], '',
             '### Skipped conjectures', '', 'Conjecture declarations are not used as proof seeds.', '',
             '| Source | Statement |', '|---|---|']
    for c in imp['conjectures']:
        lines.append(f'| [{Path(c["file"]).name}](../../{c["file"]}) | `{c["statement"]}` |')
    lines += ['', '## Definability scan', '',
              f'{defs["positives"]:,} positive and {defs["negatives"]:,} negative fact occurrences; '
              f'{defs["finite_negatives"]:,} negative occurrences seed the finite flavour.', '',
              f'{defs["rows"]} universal rows; {defs["columns"]} universal columns; '
              f'{len(defs["families"])} paired certificate families; '
              f'{defs["reachable_modules"]:,} reachable local modules.', '',
              f'Orphan declarations: `{defs["orphan_declarations"]}`.', '',
              f'Unpaired Satisfies families: `{defs["unpaired_satisfies"]}`.', '',
              f'Unpaired FamilyRefutes families: `{defs["unpaired_refutes"]}`.', '',
              f'Unclassified carrier strings (including appearances in positive proofs): `{defs["unknown_carriers"]}`.', '',
              f'Refutations with no recognized carrier: {len(defs["uncarried"])}; '
              f'with mixed carrier classifications: {len(defs["mixed"])}.', '',
              '### All negative declarations with carrier warnings', '',
              '`FromFin` independently certifies the finite flavour even without a parsed carrier.',
              '“Finite seed” records how the parser classified this occurrence; “finite closure”',
              'records whether the finite negative is known after all propagation. A missing',
              'finite seed is not automatically an open cell or an error.', '',
              '| Declaration | Carrier strings | Source → target / relation | Finite seed | Finite closure |',
              '|---|---|---|---|---|']
    for w in defs['carrier_warnings']:
        for f in w['negative_facts']:
            lines.append(f'| [{w["declaration"]}](../../{w["file"]}) | `{w["carriers"]}` | '
                         f'{f["source"]} → {f["target"]} / {f["relation"]} | {f["finite"]} | '
                         f'{f["finite_refutation_in_closure"]} |')
    return '\n'.join(lines) + '\n'


def snapshot_json(data):
    # Machine-readable output: one top-level record per line, avoiding a six-figure
    # line count of individual integers. Markdown provides the human-readable view.
    return '{\n' + ',\n'.join(f'  {json.dumps(k)}: {json.dumps(v, ensure_ascii=False)}'
                              for k, v in data.items()) + '\n}\n'


def artifacts(data):
    result = {'summary.md': summary_markdown(data), 'diagnostics.md': diagnostics_markdown(data),
              'completely_open.md': completely_open_markdown(data)}
    result.update({slug(k): relation_markdown(k, v) for k, v in data['boards'].items()})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--render', action='store_true')
    parser.add_argument('--date', default=None, help='snapshot date (YYYY-MM-DD)')
    parser.add_argument('--verify-closure', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    if args.render:
        data = json.loads(SNAPSHOT.read_text())
    else:
        snapshot_date = args.date or (json.loads(SNAPSHOT.read_text())['date'] if args.check else date.today().isoformat())
        date.fromisoformat(snapshot_date)
        data = collect(snapshot_date, args.verify_closure)
        if args.check:
            # HEAD is historical provenance, not a source input. Committing the
            # snapshot itself must not invalidate an otherwise identical audit.
            data['head'] = json.loads(SNAPSHOT.read_text())['head']
    outputs = artifacts(data)
    if not args.render:
        outputs['snapshot.json'] = snapshot_json(data)
    if args.check:
        stale = [name for name, content in outputs.items()
                 if not (OUT / name).exists() or (OUT / name).read_text() != content]
        if stale:
            raise SystemExit('Stale audit outputs: ' + ', '.join(stale))
        print('Audit snapshot and all appendices agree with the current sources.')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, content in outputs.items():
            (OUT / name).write_text(content)
        print(f'Wrote {len(outputs)} audit outputs to {OUT.relative_to(ROOT)}.')
    print(f'Elapsed: {time.monotonic() - start:.2f} s')


if __name__ == '__main__':
    main()
