#!/usr/bin/env python3
"""Export the audited relation board, compact proof generators, and spectrum evidence.

Build Lean first, then export declarations with export_website.lean. We independently
collect source-labelled seeds and compare their entire closure with definable.py;
no status is inferred from a theorem's name or from an unproved conjecture.
"""
import argparse
import collections
import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import numpy as np
import definable as board

ROOT = board.ROOT
KEYS = [f'{r}-{f}' for r, f in board.KEYS]
LABELS = ['Implication', 'Term structural', 'FO structural', 'Term definable', 'FO definable']
DESCRIPTIONS = [
    'Every magma satisfying A also satisfies B, with the same operation.',
    'On each A-magma, a binary term defines a B-operation and a binary term recovers the original operation.',
    'On each A-magma, a parameter-free first-order definition gives a B-operation and a first-order definition recovers the original operation.',
    'On each A-magma, a binary term defines a B-operation on the same carrier.',
    'On each A-magma, a parameter-free first-order definition gives a B-operation on the same carrier.',
]

def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, separators=(',', ':'), ensure_ascii=False))


def commentless(text):
    # Preserve offsets for links; match the board scanner's treatment of comments.
    blank = lambda m: ''.join('\n' if c == '\n' else ' ' for c in m[0])
    return board.LINE_COMMENT.sub(blank, board.BLOCK_COMMENT.sub(blank, text))


def rle(a):
    a = np.asarray(a, dtype=np.uint8).ravel()
    starts = np.flatnonzero(np.r_[True, a[1:] != a[:-1]])
    return np.column_stack((a[starts], np.diff(np.r_[starts, len(a)]))).ravel().tolist()


class Export:
    def __init__(self, declarations):
        self.declarations = declarations
        self.by_name = {d['name']: d for d in declarations}
        self.by_suffix = collections.defaultdict(list)
        for d in declarations:
            parts = d['name'].split('.')
            for i in range(len(parts)): self.by_suffix['.'.join(parts[i:])].append(d)
        self.by_file = collections.defaultdict(list)
        for d in declarations:
            self.by_file[d['file']].append(d)
        self.sources, self.source_ids = [], {}
        self.positive, self.negative = [], []
        self.families = {}
        self.rules = {}
        self.all_ids = list(range(1, board.SIZE))
        self.includes = np.eye(len(KEYS), dtype=bool)
        for a, b in board.ARROWS:
            self.includes[board.KEYS.index(a), board.KEYS.index(b)] = True
        self.includes = board.transitive_closure(self.includes)

    def ref(self, record):
        ident = (record['file'], record['name'])
        if ident not in self.source_ids:
            self.source_ids[ident] = len(self.sources)
            self.sources.append(record)
        return self.source_ids[ident]

    def declaration(self, path, text, start, decl):
        name = re.search(r'\b(?:theorem|lemma)\s+(\S+)', decl)
        if not name:
            raise ValueError(f'Anonymous evidence at {path}:{text[:start].count(chr(10))+1}')
        name = name[1]
        file = str(path.relative_to(ROOT))
        candidates = [d for d in self.by_suffix[name] if d['file'] == file]
        if len(candidates) > 1:
            declaration_line = text[:start + re.search(r'\b(?:theorem|lemma)\s+',decl).start()].count('\n') + 1
            candidates = [d for d in candidates if d['line'] == declaration_line]
        if len(candidates) != 1:
            raise ValueError(f'Missing/ambiguous compiled declaration {file}: {name}')
        record = candidates[0]
        if record['status'] != 'PROVED':
            raise ValueError(f'Unproved definability evidence: {file}:{name} ({record["status"]})')
        return self.ref(record)

    def named(self, suffix):
        candidates = self.by_suffix[suffix]
        if len(candidates) != 1:
            raise ValueError(f'Missing/ambiguous rule {suffix}: {[d["name"] for d in candidates]}')
        if candidates[0]['status'] != 'PROVED':
            raise ValueError(f'Unproved closure rule {suffix}')
        return self.ref(candidates[0])

    def seed(self, positive, key, sources, targets, refs, **extra):
        if sources and targets:
            (self.positive if positive else self.negative).append(
                dict(key=key, s=sources, t=targets, refs=refs, **extra))

    def implications(self, entries):
        _, dual = board.load_duals()
        seen = set()
        for entry in entries:
            filename = entry['filename']
            if Path(filename).is_absolute():
                filename = 'equational_theories/' + filename.rsplit('/equational_theories/',1)[1]
            filename = re.sub(r'^(\./)+', '', filename)
            ident = (filename, entry['name'])
            if ident in seen:
                continue
            seen.add(ident)
            v = entry['variant']
            proven = entry['proven']
            ref = self.ref(dict(file=filename, name=entry['name'],
                                line=entry['line'] or 1, status='PROVED' if proven else 'PROOF_AVAILABLE'))
            parse = lambda xs: [int(x[8:]) for x in xs if x.startswith('Equation') and x[8:].isdigit() and 1 <= int(x[8:]) <= board.N_EQ]
            if 'implication' in v:
                x = v['implication']
                positive, s, t, finite = True, parse([x['lhs']]), parse([x['rhs']]), x['finite']
            elif 'facts' in v:
                x = v['facts']
                positive, s, t, finite = False, parse(x['satisfied']), parse(x['refuted']), x['finite']
            elif 'unconditional' in v:
                positive, s, t, finite = True, self.all_ids, parse([v['unconditional']]), False
            else:
                raise ValueError(v)
            key = KEYS.index('implies-' + ('fin' if finite else 'all'))
            self.seed(positive, key, s, t, [ref], conjectural=not proven)
            ds, dt = [int(dual[i]) for i in s], [int(dual[i]) for i in t]
            if set(ds) != set(s) or set(dt) != set(t):
                self.seed(positive, key, ds, dt, [ref], conjectural=not proven, dual=True)

    def definability(self):
        reachable = board.import_graph(ROOT)
        for path in sorted(board.LEAN.rglob('*.lean')):
            if '.'.join(path.relative_to(ROOT).with_suffix('').parts) not in reachable:
                continue
            text = commentless(path.read_text())
            cuts = [m.start() for m in board.DECL.finditer(text)] + [len(text)]
            for start, stop in zip(cuts, cuts[1:]):
                decl = text[start:stop]
                if not any(p.search(decl) for p in (board.FACT, board.ROW, board.COL, board.SATISFIES, board.REFUTES)):
                    continue
                ref = self.declaration(path, text, start, decl)
                carriers = {board.carrier_is_finite(c) for c in board.witness_carriers(decl)}
                if any(lemma in decl for lemma in board.FINITE_LEMMAS):
                    carriers.add(True)
                uses_compactness = any(lemma in decl for lemma in board.COMPACTNESS_LEMMAS)
                finite = bool(carriers) and carriers == {True} and not uses_compactness
                for neg, tgt, rel, fin, src in board.FACT.findall(decl):
                    key = KEYS.index(board.REL_NAMES[rel] + ('-fin' if fin or (neg and finite) else '-all'))
                    self.seed(not neg, key, [int(src)], [int(tgt)], [ref])
                for tgt, rel in board.ROW.findall(decl):
                    self.seed(True, KEYS.index(board.REL_NAMES[rel]+'-all'), self.all_ids, [int(tgt)], [ref])
                for rel, src in board.COL.findall(decl):
                    self.seed(True, KEYS.index(board.REL_NAMES[rel]+'-all'), [int(src)], self.all_ids, [ref])
                for kind, regex in [('s', board.SATISFIES), ('t', board.REFUTES)]:
                    for fam, body in regex.findall(decl):
                        ids = [int(x) for x in body.replace('\n', ' ').split(',')]
                        self.families.setdefault(fam, {'s': [], 't': []})[kind].append([ids, ref])
        missing_rules = []
        for fam, parts in self.families.items():
            if not parts['s'] or not parts['t']:
                continue
            rel = board.STRUCTURAL_FAMILIES.get(fam, 'definable')
            key = KEYS.index(rel+'-fin')
            # The family obstruction theorem is needed in addition to the two lists.
            spellings = [f'not_{rel}From_{fam}', f'not_{rel}FromFin_of_{fam}',
                         f'not_{rel}From_of_{fam}', f'not_{rel}FromFin_{fam}']
            spelling = next((name for name in spellings if self.by_suffix[name]), None)
            if spelling is None:
                missing_rules.append((fam,rel))
                continue
            rule = self.named(spelling)
            self.seed(False, key, sorted({i for ids, _ in parts['s'] for i in ids}),
                      sorted({i for ids, _ in parts['t'] for i in ids}), [rule], family=fam)
        if missing_rules: raise ValueError(f'Missing family rules: {missing_rules}')
        dual_ref = self.named('TermStructural_dual')
        for a, b in board.load_duals()[0]:
            self.seed(True, KEYS.index('termStructural-all'), [a], [b], [dual_ref])
            self.seed(True, KEYS.index('termStructural-all'), [b], [a], [dual_ref])

    def seeds_matrix(self, seeds, key, conjectures=False):
        out = np.zeros((board.SIZE, board.SIZE), dtype=bool)
        for x in seeds:
            if x['key'] == key and (conjectures or not x.get('conjectural')):
                out[np.ix_(x['s'], x['t'])] = True
        return out

    def build(self, output):
        p, n = {}, {}
        for k, key in enumerate(board.KEYS):
            p[key] = self.seeds_matrix(self.positive, k) | np.eye(board.SIZE, dtype=bool)
            n[key] = self.seeds_matrix(self.negative, k)
        board.close(p, n)
        # An independent exporter must agree with every cell of the audited board.
        expected_p, expected_n = board.build_relations()
        for key in board.KEYS:
            for kind, actual, expected in [('positive', p, expected_p), ('negative', n, expected_n)]:
                if not np.array_equal(actual[key], expected[key]):
                    mismatch = np.argwhere(actual[key] != expected[key])
                    raise ValueError(f'{key} {kind} disagrees with board: {mismatch[:8].tolist()} ({len(mismatch)})')
        del expected_p, expected_n
        # A minimal greedy cover of each native negative closure. All retained
        # witnesses carry their original key: weaker-relation paths cannot be
        # silently presented as stronger-relation paths.
        selected = []
        native_n = []
        for k, key in enumerate(board.KEYS):
            reps, classes = board.equivalence_classes(p[key])
            covered = np.zeros((len(reps), len(reps)), dtype=bool)
            candidates = [x for x in self.negative if x['key'] == k and not x.get('conjectural')]
            candidates.sort(key=lambda x: -len(x['s'])*len(x['t']))
            for x in candidates:
                if len(x['s']) == len(x['t']) == 1 and covered[classes[x['s'][0]], classes[x['t'][0]]]:
                    continue
                sources = p[key][np.ix_(x['s'], reps)].any(axis=0)
                targets = p[key][np.ix_(reps, x['t'])].any(axis=1)
                rectangle = np.ix_(sources, targets)
                if covered[rectangle].all():
                    continue
                covered[rectangle] = True
                selected.append(x)
            full = covered[np.ix_(classes, classes)]
            full[0,:] = full[:,0] = False
            native_n.append(full)
        for k, key in enumerate(board.KEYS):
            covered = np.zeros_like(n[key])
            for j in range(len(KEYS)):
                if self.includes[k,j]:
                    covered |= native_n[j]
            if not np.array_equal(covered, n[key]):
                raise ValueError(f'Negative provenance coverage failed for {key}')
        del native_n
        print(f'Kept {len(selected)} negative witnesses from {len(self.negative)} generators', flush=True)
        self.negative = selected
        # Conjectures are only exported for implication, never promoted into the
        # definability board or used to collapse equivalence classes.
        cp, cn = {}, {}
        for k, key in enumerate(board.KEYS[:2]):
            cp[key] = self.seeds_matrix(self.positive, k, True) | np.eye(board.SIZE, dtype=bool)
            cn[key] = np.zeros_like(n[key])
        for x in self.original_negative:
            if x.get('conjectural'):
                cn[board.KEYS[x['key']]][np.ix_(x['s'],x['t'])] = True
        # Positives flow all -> finite; refutations flow finite -> all.
        cp['implies','all'] = board.transitive_closure(cp['implies','all'])
        cp['implies','fin'] |= cp['implies','all']
        cp['implies','fin'] = board.transitive_closure(cp['implies','fin'])
        for key in [('implies','fin'), ('implies','all')]:
            cn[key] |= n[key]
            if key[1] == 'all': cn[key] |= cn['implies','fin']
            cn[key] = board.compose_negatives(cp[key], cn[key])
            if (cp[key] & cn[key]).any():
                raise ValueError(f'Conflicting implication claims in {key}')
        manifests = []
        for k, key in enumerate(board.KEYS):
            reps, classes = board.equivalence_classes(p[key])
            groups = [[i for i in range(1,board.SIZE) if classes[i] == c] for c in range(len(reps))]
            ix = np.ix_(reps,reps)
            status = np.zeros((len(reps),len(reps)), dtype=np.uint8)
            status[p[key][ix]] = 1
            status[n[key][ix]] = 2
            if key[0] == 'implies':
                status[(status == 0) & cp[key][ix]] = 3
                status[(status == 0) & cn[key][ix]] = 4
            gaps = np.argwhere(np.triu((status != 2) & (status.T != 2) & ~np.eye(len(reps),dtype=bool),1))
            # Definite class collapses require proved yes in both directions.
            record = dict(key=KEYS[k], label=LABELS[k//2], flavour=key[1], description=DESCRIPTIONS[k//2],
                          classes=len(groups), unresolved_equivalence_pairs=len(gaps),
                          counts={str(i):int((status==i).sum()) for i in range(5)})
            manifests.append(record)
            dump(output / f'{KEYS[k]}.json', dict(**record, groups=groups, classOf=classes.tolist(),
                 status=rle(status), possibleMerges=gaps.tolist()))
        # Remove unused source records and family pieces after selecting witnesses.
        self.negative += [x for x in self.original_negative if x.get('conjectural')]
        used_fams = {x['family'] for x in self.negative if 'family' in x}
        families = {f:self.families[f] for f in used_fams}
        rules = [self.ref(d) for d in self.declarations if d['file'] in [
            'equational_theories/Definability/Basic.lean','equational_theories/Definability/FiniteFlavour.lean']
            and (d['name'].endswith(('.trans','.refl')) or '_of_' in d['name'])]
        for filename, names in [('Preorder.lean', ['implies_refl','implies_trans']),
                                ('MagmaOp.lean', ['implies_iff_dual','satisfies_dual_dual'])]:
            file = 'equational_theories/' + filename
            text = (ROOT/file).read_text()
            for name in names:
                match = re.search(r'^theorem ' + name + r'\b', text, re.M)
                if not match: raise ValueError(f'Missing closure rule {name}')
                rules.append(self.ref(dict(file=file, name='Law.MagmaLaw.'+name,
                    line=text[:match.start()].count('\n')+1, status='PROVED')))
        used = set(rules)
        for x in self.positive+self.negative: used.update(x['refs'])
        for f in families.values():
            for parts in f.values(): used.update(ref for _,ref in parts)
        mapping = {old:new for new,old in enumerate(sorted(used))}
        for x in self.positive+self.negative: x['refs'] = [mapping[r] for r in x['refs']]
        for f in families.values():
            for parts in f.values():
                for piece in parts: piece[1] = mapping[piece[1]]
        dump(output/'proofs.json', dict(positive=self.positive, negative=self.negative,
             families=families, sources=[self.sources[r] for r in sorted(used)],
             includes=self.includes.astype(int).tolist(), rules=[mapping[r] for r in rules]))
        self.metadata(output, manifests)

    def metadata(self, output, manifests):
        commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        repo = os.environ.get('GITHUB_REPOSITORY', 'Timeroot/equational_theories')
        # Equations use the original plain-text file; frontend renders as text.
        eqs = (ROOT/'data/equations.txt').read_text().splitlines()
        equation_sources = [None] * board.SIZE
        for path in sorted((ROOT/'equational_theories/Equations').glob('*.lean')):
            for line, text in enumerate(commentless(path.read_text()).splitlines(),1):
                m = re.match(r'equation\s+(\d+)\s*:=',text)
                if m:
                    i = int(m[1])
                    if not 1 <= i <= board.N_EQ: continue
                    equation_sources[i] = dict(file=str(path.relative_to(ROOT)),line=line,name=f'Equation{i}')
        if not all(equation_sources[1:]): raise ValueError('Missing equation source location')
        dump(output/'index.json', dict(version=1, repository=repo, commit=commit,
             generated=datetime.datetime.now(datetime.timezone.utc).isoformat(),
             relations=manifests, equations=eqs, equationSources=equation_sources, duals=board.load_duals()[1].tolist(),
             statuses={'0':'unknown','1':'proved yes','2':'proved no','3':'conjectural yes','4':'conjectural no'}))
        self.spectrum(output)

    def spectrum(self, output):
        records = json.loads((ROOT/'data/spectrum/catalogue.json').read_text())
        used = {}
        witnesses = collections.defaultdict(list)
        for d in self.declarations:
            # Construction modules also use namespaces such as E63.model46.
            m = (re.search(r'\.model_(\d+)_(\d+)$', d['name']) or
                 re.search(r'\.E(\d+)\.model(\d+)$', d['name']))
            if m and d['file'].startswith('equational_theories/Spectrum/'):
                witnesses[int(m[1])].append(dict(order=int(m[2]), theorem=d['name']))
        for record in records:
            record['witnesses'] = sorted(witnesses[record['equation']], key=lambda x:x['order'])
            for w in record['witnesses']: used[w['theorem']] = self.by_name[w['theorem']]
            for key, name in list(record.items()):
                if key.endswith('_theorem') and name:
                    if name not in self.by_name: raise ValueError(f'Missing spectrum declaration {name}')
                    used[name] = self.by_name[name]
            # A selected witness list is not itself a proved lower bound. Link to
            # the catalogue's checked exact/bound declarations instead.
        dump(output/'spectrum.json', dict(records=records, declarations=used))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--declarations', type=Path, required=True)
    parser.add_argument('--general-entries', type=Path, required=True)
    parser.add_argument('--finite-entries', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=ROOT/'home_page/research/data')
    args = parser.parse_args()
    exporter = Export(json.loads(args.declarations.read_text()))
    print('Reading implication evidence…', flush=True)
    exporter.implications(json.loads(args.general_entries.read_text())+json.loads(args.finite_entries.read_text()))
    print('Reading definability evidence…', flush=True)
    exporter.definability()
    exporter.original_negative = exporter.negative.copy()
    print('Closing and verifying relation matrices…', flush=True)
    exporter.build(args.output)

if __name__ == '__main__': main()
