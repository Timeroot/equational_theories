#!/usr/bin/env python3
"""Recheck the E677 field survey against E255 and the affine ideal identities.

This reads the original field coefficients and evaluates the original equations
on their full tables. It does not change the implication or spectrum catalogue.
The general results are proved in Spectrum/Equation677/ConstructionLimits.lean.
"""
import argparse
import json
from pathlib import Path

import sympy as sp
from spectrum_generate import load_equations, satisfies
from spectrum_open_survey import Field

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'data/spectrum/677_255_designs_check.json'


def check():
    a, b = sp.symbols('a b')
    P = a*b**3+a*b-1
    Q = a*a*b*b+a+b**3
    R = a*b*b+b*b+b+1
    S = a*a+a+1
    U = -a**3*b-a*a-a*b*b-b+1
    V = a*(a*b*b+a+b-1)
    Uc = -a*a*b-a*b-a-2
    Vc = a*b*b+a+b+b*b
    Wc = -b**3+b-1
    assert sp.expand((a+b-1)*S-U*P-V*Q) == 0
    assert sp.expand(S-Uc*P-Vc*Q-Wc*R) == 0
    F = b**4-b**3+b*b-b+1
    assert sp.expand(P.subs(a, 1-b)+F) == 0
    assert sp.expand(Q.subs(a, 1-b)-F) == 0
    source = json.loads((ROOT / 'data/spectrum/open_survey_20260927.json').read_text())
    family = source['finite_fields']['families']['677']
    laws = load_equations()
    results = []
    for kind in ['models', 'idempotent_models']:
        for order, model in sorted(family[kind].items(), key=lambda item: int(item[0])):
            field = Field(model['p'], model['modulus'])
            assert field.q == int(order)
            table = field.table(model['a'], model['b'])
            assert satisfies(*laws[676], table, field.q)
            assert satisfies(*laws[254], table, field.q)
            idempotent = all(table[x*field.q+x] == x for x in range(field.q))
            if kind == 'idempotent_models':
                assert idempotent
            results.append(dict(kind=kind, order=field.q, **model,
                                idempotent=idempotent, E677=True, E255=True))
    return dict(status='ALL_SAVED_MODELS_SATISFY_E255',
                all_field_witnesses=len(family['models']),
                separately_saved_idempotent_witnesses=len(family['idempotent_models']),
                affine_polynomial_identities_checked=True, witnesses=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = check()
    if args.write:
        OUT.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(OUT.read_text()) == result
    print(f"Checked {result['all_field_witnesses']} field witnesses and "
          f"{result['separately_saved_idempotent_witnesses']} idempotent witnesses; "
          'all satisfy E677 and E255. Both affine ideal identities checked.')


if __name__ == '__main__':
    main()
