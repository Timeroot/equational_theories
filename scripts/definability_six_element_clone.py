#!/usr/bin/env python3
"""Reproduce the twelve tiny counterexamples per E960 recovery obstruction.

The Lean module proves the clone composition rule symbolically; this script
only supplies falsifying assignments. --check verifies the generated section
byte for byte, and independently checks the finite arithmetic model and closure.
"""
import argparse
from itertools import product
from pathlib import Path

from spectrum_generate import evaluate, load_equations, satisfies, variables

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / 'equational_theories/Definability/SixElementCloneRecovery.lean'
MARKER = '-- BEGIN GENERATED EXCLUSIONS (scripts/definability_six_element_clone.py)\n'
TARGETS = [55, 65, 669, 679, 713, 825, 845, 872, 1434, 1451, 1525,
           3315, 3316, 3318, 3319, 3518, 3519, 3521, 3522, 4275, 4320]
# Same order as `bad` in the Lean module. All have reflection enabled.
BAD = [(0, 1, 1, 1), (1, 1, 1, 1), (1, 1, 2, 1), (0, 2, 0, 1),
       (0, 2, 2, 1), (0, 1, 2, 1), (1, 2, 2, 1), (0, 2, 1, 1),
       (1, 2, 0, 1), (1, 2, 1, 1), (1, 1, 0, 1), (0, 1, 0, 1)]


def operation(i, x, y):
    right, outside, inside, reflected = i
    u, v = (x, y) if right else (y, x)
    if u % 2 and not v % 2:
        return 2 * ((u // 2 - v // 2 + inside if reflected else v // 2 + inside) % 3)
    return 2 * ((v // 2 + outside) % 3) + v % 2


def compose(i, j):
    same = i[0] == j[0]
    return (j[0], (j[1] + 1) % 3,
            (j[2] + 1 if same else i[1] - j[2] + 1) % 3,
            j[3] if same else 1 - j[3])


def point(x):
    return f'({str(bool(x % 2)).lower()}, {x // 2})'


def generate():
    equations = load_equations()
    indices = list(product(range(2), range(3), range(3), range(2)))
    tables = {i: [operation(i, x, y) for x in range(6) for y in range(6)] for i in indices}
    assert len({tuple(t) for t in tables.values()}) == 36
    source = tables[(1, 1, 1, 1)]
    assert satisfies(*equations[959], source, 6)
    for i, j in product(indices, repeat=2):
        assert tables[compose(i, j)] == [source[6 * a + b] for a, b in zip(tables[i], tables[j])]
    assert set(BAD) == {i for i in indices if i[1] != 0 and i[3]}
    out = ''
    for target in TARGETS:
        lhs, rhs = equations[target - 1]
        names = sorted(variables(lhs) | variables(rhs), key='xyzw'.index)
        out += (f'private theorem exclude{target} : ∀ j, ¬ @Equation{target} Point (family (bad j)) := by\n'
                '  intro j h\n  fin_cases j\n')
        for i in BAD:
            table = tables[i]
            assignment = next(dict(zip(names, vals)) for vals in product(range(6), repeat=len(names))
                              if evaluate(lhs, dict(zip(names, vals)), table, 6) !=
                              evaluate(rhs, dict(zip(names, vals)), table, 6))
            a, b = (evaluate(term, assignment, table, 6) for term in (lhs, rhs))
            arguments = ' '.join(point(assignment[v]) for v in names)
            out += f'  · exact (by decide : ({point(a)} : Point) ≠ {point(b)}) (h {arguments})\n'
        out += (f'\ntheorem Equation{target}_not_termStructuralFromFin_Equation960 :\n'
                f'    ¬ Law{target}.TermStructuralFromFin Law960 :=\n'
                f'  obstruct (fun j h => exclude{target} j ((@Law{target}.models_iff Point (family (bad j))).mp h))\n\n')
    out += 'end SixElementCloneRecovery\n'
    for target in TARGETS:
        name = f'SixElementCloneRecovery.Equation{target}_not_termStructuralFromFin_Equation960'
        out += (f"\n/-- info: '{name}' depends on axioms: [propext, Classical.choice, Quot.sound] -/\n"
                f'#guard_msgs (whitespace := lax) in\n#print axioms {name}\n')
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    args = parser.parse_args()
    old = LEAN.read_text()
    prefix, _ = old.split(MARKER)
    new = prefix + MARKER + generate()
    if args.write:
        LEAN.write_text(new)
    elif new != old:
        raise SystemExit('Generated exclusions differ; run with --write.')
    print('Checked 36 operations, 1296 compositions, and 252 target-law counterexamples.')


if __name__ == '__main__':
    main()
