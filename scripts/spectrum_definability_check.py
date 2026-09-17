"""Read-only spectrum/definability cross-check; run after `lake build equational_theories.Spectrum`.

Uses completed Lean spectrum declarations, never pending claims or failure to find
a model. Prints a reproducible summary and every newly detected D/fin refutation.
This is a diagnostic, not a generator of Lean proofs or board seed facts.
"""
from collections import Counter
import json
from math import isqrt
import re
import subprocess

import numpy as np

import definable as board
from definability_audit import source_fingerprint


def spectrum_closure(present, absent, inclusion):
    """Presence goes source→target; absence goes target→source."""
    present = inclusion[present].any(axis=0)
    absent = inclusion[:, absent].any(axis=1)
    assert not np.any(present & absent), 'inconsistent spectrum evidence'
    return present, absent


def formula_contains(formula, n):
    """Evaluate only audited, supported Lean spectrum formulas; fail on new syntax."""
    if formula == '{n : ℕ | 0 < n}':
        return n > 0
    if formula == '{1}':
        return n == 1
    if formula == 'squares':
        return n > 0 and isqrt(n) ** 2 == n
    if match := re.fullmatch(r'positiveExcept \{([0-9, ]+)\}', formula):
        return n > 0 and n not in {int(x) for x in match[1].split(',')}
    raise ValueError(f'new completed spectrum formula needs an evaluator: {formula}')


def main():
    before = source_fingerprint()
    catalogue_path = board.ROOT / 'data/spectrum/catalogue.json'
    catalogue_text = catalogue_path.read_text()
    # Independently checks actual types AND transitive axioms for all JSON claims.
    subprocess.run(['lake', 'env', 'lean', 'scripts/check_spectrum.lean'], cwd=board.ROOT, check=True)
    output = subprocess.check_output(
        ['lake', 'env', 'lean', 'scripts/spectrum_definability_facts.lean'],
        cwd=board.ROOT, text=True)
    records = [json.loads(line) for line in output.splitlines()]
    facts = [record['fact'] for record in records if 'fact' in record]
    # Include every exported witness order: new exact upper bounds can exclude
    # one even when no standalone `not_order_*` theorem has been written.
    orders = sorted({n for kind, (_, n) in facts if kind in ('excluded', 'model') and n > 1})
    catalogue = json.loads(catalogue_text)
    singletons = np.zeros(board.SIZE, dtype=bool)
    bounds = []
    for record in catalogue:
        if record.get('exact_proof_status') == 'PROVED':
            formula = record['exact_spectrum_formula']
            formula_contains(formula, 1)  # Reject unsupported formulas even if no orders exist.
            bounds.append((record['equation'], formula, True))
            singletons[record['equation']] = formula == '{1}'
        if record.get('upper_bound_proof_status') == 'PROVED':
            formula = record['upper_bound_formula']
            formula_contains(formula, 1)
            bounds.append((record['equation'], formula, False))

    pos, neg = board.build_relations()
    inclusion = pos['definable', 'fin'].copy()
    full = np.zeros(board.SIZE, dtype=bool)
    nontrivial = np.zeros(board.SIZE, dtype=bool)
    models = {n: np.zeros(board.SIZE, dtype=bool) for n in orders}
    exclusions = {n: singletons.copy() for n in orders}
    for n in orders:
        for i, formula, exact in bounds:
            if not formula_contains(formula, n):
                exclusions[n][i] = True
            elif exact:
                models[n][i] = True
    for kind, (s, t) in facts:
        assert 1 <= s <= board.N_EQ
        if kind == 'full':
            full[s] = True
            nontrivial[s] = True
        elif kind == 'model':
            if t in models:
                models[t][s] = True
            if t > 1:
                nontrivial[s] = True
        elif kind == 'excluded':
            exclusions[t][s] = True
        elif kind in ('equal', 'inclusion'):
            assert 1 <= t <= board.N_EQ
            inclusion[s, t] = True
            if kind == 'equal':
                inclusion[t, s] = True
        else:
            raise AssertionError(kind)
    inclusion = board.transitive_closure(inclusion)
    nontrivial, singleton_closure = spectrum_closure(nontrivial, singletons, inclusion)
    # Every non-singleton law has a *proved* nontrivial finite model, not just
    # the absence of an exclusion. This covers all orders for singleton targets.
    assert np.all((nontrivial | singleton_closure)[1:])
    candidates = nontrivial[:, None] & singleton_closure[None, :]
    summary = {'singleton_sources_with_nontrivial_model': int(nontrivial.sum()),
               'singleton_targets': int(singleton_closure.sum()),
               'singleton_obstructions': int(candidates.sum()), 'orders': {}}
    for n in orders:
        models[n] |= full
        # Factor orders are smaller and already transported by this iteration.
        for d in orders:
            if d * d > n:
                break
            if n % d == 0 and n // d in models:
                models[n] |= models[d] & models[n // d]
        models[n], exclusions[n] = spectrum_closure(models[n], exclusions[n], inclusion)
        current = models[n][:, None] & exclusions[n][None, :]
        candidates |= current
        summary['orders'][n] = dict(present=int(models[n].sum()), absent=int(exclusions[n].sum()),
                                   obstructions=int(current.sum()),
                                   new_D_fin=int((current & ~neg['definable', 'fin']).sum()))
    newly_negative = candidates & ~neg['definable', 'fin']
    assert not np.any(candidates & pos['definable', 'fin'])
    summary.update(unique_obstructions=int(candidates.sum()),
                   already_negative={ '/'.join(key): int((candidates & neg[key]).sum())
                                     for key in board.KEYS if key[0] != 'implies'},
                   new_D_fin_pairs=np.argwhere(newly_negative).tolist(),
                   exported_fact_counts=dict(sorted(Counter(kind for kind, _ in facts).items())),
                   pending_declarations_skipped=records[-1]['pending_declarations_skipped'],
                   source_fingerprint=before)
    assert before == source_fingerprint() and catalogue_text == catalogue_path.read_text(), \
        'source inputs changed during check; rerun'
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
